"""Build compact blast_map.json.gz from pinned sqlglot checkout and tests.json."""

from __future__ import annotations

import argparse
import ast
import collections
from concurrent.futures import Future
import concurrent.futures
import gzip
import importlib
import json
import os
from pathlib import Path
import pickle
import pkgutil
import re
import sys
import time
import unittest


_UPPER_KEY_ATTRS = frozenset(
    {
        "FUNCTIONS",
        "FUNCTION_PARSERS",
        "PROPERTY_PARSERS",
        "CONSTRAINT_PARSERS",
        "NO_PAREN_FUNCTION_PARSERS",
        "KEYWORDS",
    }
)

_ATTR_DERIVED_SYMBOLS_KEEP = {
    "TIME_MAPPING",
    "TIME_TRIE",
    "INVERSE_TIME_MAPPING",
    "INVERSE_TIME_TRIE",
    "FORMAT_MAPPING",
    "FORMAT_TRIE",
    "INVERSE_FORMAT_MAPPING",
    "INVERSE_FORMAT_TRIE",
    "CREATABLE_KIND_MAPPING",
    "INVERSE_CREATABLE_KIND_MAPPING",
    "DATE_PART_MAPPING",
    "VALID_INTERVAL_UNITS",
    "UNESCAPED_SEQUENCES",
    "ESCAPED_SEQUENCES",
    "IDENTIFIER_ESCAPED_SEQUENCES",
    "SUPPORTED_JSON_PATH_PARTS",
    "TRANSFORMS",
    "QUOTES",
    "_QUOTES",
    "QUOTE_START",
    "QUOTE_END",
    "IDENTIFIERS",
    "_IDENTIFIERS",
    "IDENTIFIER_START",
    "IDENTIFIER_END",
    "BIT_STRINGS",
    "_FORMAT_STRINGS",
    "BIT_START",
    "BIT_END",
    "HEX_STRINGS",
    "HEX_START",
    "HEX_END",
    "BYTE_STRINGS",
    "BYTE_START",
    "BYTE_END",
    "UNICODE_STRINGS",
    "UNICODE_START",
    "UNICODE_END",
    "RAW_STRINGS",
    "HEREDOC_STRINGS",
    "NATIONAL_RAW_STRINGS",
    "STRING_ESCAPES",
    "_STRING_ESCAPES",
    "STRINGS_SUPPORT_ESCAPED_SEQUENCES",
    "BYTE_STRING_ESCAPES",
    "_BYTE_STRING_ESCAPES",
    "BYTE_STRINGS_SUPPORT_ESCAPED_SEQUENCES",
    "IDENTIFIER_ESCAPES",
    "_IDENTIFIER_ESCAPES",
    "COMMENTS",
    "_COMMENTS",
    "KEYWORDS",
    "_KEYWORD_TRIE",
    "SUPPORTS_COLUMN_JOIN_MARKS",
    "SHOW_PARSERS",
    "SHOW_TRIE",
    "SET_PARSERS",
    "SET_TRIE",
}

_WORD_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_$]*")
_NONALNUM_RUN_RE = re.compile(r"[^A-Za-z0-9_$\s]+")


def _norm_dict_key(attr_name: str, key) -> str | None:
    if key is None:
        return None
    if isinstance(key, type):
        return key.__name__
    if hasattr(key, "name") and hasattr(key, "value"):
        return str(key.name)
    if isinstance(key, str):
        return key.upper() if attr_name in _UPPER_KEY_ATTRS else key
    return str(key)


class InlinePoolExecutor:
    """Synchronous drop-in replacement for ProcessPoolExecutor so sys.monitoring captures all lines."""

    def __init__(self, max_workers=None, mp_context=None, initializer=None, initargs=()):
        if initializer is not None:
            initializer(*initargs)

    def submit(self, fn, *args, **kwargs):
        fut = Future()
        try:
            # Mirror ProcessPoolExecutor's IPC pickling so Expr.__reduce__ (serde) is traced too
            fn_p, args_p, kwargs_p = pickle.loads(pickle.dumps((fn, args, kwargs)))
            res = fn_p(*args_p, **kwargs_p)
            res = pickle.loads(pickle.dumps(res))
        except BaseException as exc:
            fut.set_exception(exc)
        else:
            fut.set_result(res)
        return fut

    def shutdown(self, wait=True, cancel_futures=False):
        pass

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        return False


def _rel_path(path_str: str, repo_root: Path) -> str | None:
    try:
        p = Path(path_str).resolve()
        rel = p.relative_to(repo_root)
        return rel.as_posix()
    except Exception:
        return None


class _LineRecorder:
    def __init__(self, repo_root: Path):
        self.repo_root = repo_root
        self.repo_prefix = str(repo_root).lower()
        self.active = False
        self.suppress_dict_trace = 0
        self.current_test: int = -1
        # code_obj -> (rel_file_or_None, firstlineno)
        self.code_meta: dict[object, tuple[str | None, int]] = {}
        self.test_lines: dict[int, dict[str, set[int]]] = collections.defaultdict(
            lambda: collections.defaultdict(set)
        )
        self.test_funcs: dict[int, set[tuple[str, int]]] = collections.defaultdict(set)
        self.test_files_opened: dict[int, set[str]] = collections.defaultdict(set)
        self.setup_files_opened: dict[tuple[str, str], set[str]] = collections.defaultdict(set)
        self.setup_lines: dict[tuple[str, str], dict[str, set[int]]] = collections.defaultdict(
            lambda: collections.defaultdict(set)
        )
        self.setup_funcs: dict[tuple[str, str], set[tuple[str, int]]] = collections.defaultdict(set)
        self.setup_modules: dict[tuple[str, str], set[str]] = collections.defaultdict(set)
        self.current_class_key: tuple[str, str] | None = None
        self.import_lines: dict[str, set[int]] = collections.defaultdict(set)
        self.test_to_imported_modules: dict[int, set[str]] = collections.defaultdict(set)

        # Runtime maps (per-test and per-setUpClass)
        self.test_exprs: dict[int, set[str]] = collections.defaultdict(set)
        self.setup_exprs: dict[tuple[str, str], set[str]] = collections.defaultdict(set)
        self.test_dialects: dict[int, set[str]] = collections.defaultdict(set)
        self.setup_dialects: dict[tuple[str, str], set[str]] = collections.defaultdict(set)
        self.test_dict_keys: dict[str, dict[str, set[int]]] = collections.defaultdict(
            lambda: collections.defaultdict(set)
        )
        self.setup_dict_keys: dict[tuple[str, str], dict[str, set[str]]] = collections.defaultdict(
            lambda: collections.defaultdict(set)
        )
        self.test_dict_iters: dict[str, set[int]] = collections.defaultdict(set)
        self.setup_dict_iters: dict[tuple[str, str], set[str]] = collections.defaultdict(set)
        self.test_tokens: dict[str, set[int]] = collections.defaultdict(set)
        self.setup_tokens: dict[tuple[str, str], set[str]] = collections.defaultdict(set)
        self.test_time_substrs: dict[str, set[int]] = collections.defaultdict(set)
        self.setup_time_substrs: dict[tuple[str, str], set[str]] = collections.defaultdict(set)

    def record_expr(self, expr_name: str) -> None:
        if not self.active:
            return
        if self.current_test >= 0:
            self.test_exprs[self.current_test].add(expr_name)
        elif self.current_test == -2 and self.current_class_key is not None:
            self.setup_exprs[self.current_class_key].add(expr_name)

    def record_dialect(self, dname: str) -> None:
        if not self.active:
            return
        if self.current_test >= 0:
            self.test_dialects[self.current_test].add(dname)
        elif self.current_test == -2 and self.current_class_key is not None:
            self.setup_dialects[self.current_class_key].add(dname)

    def record_dict_key(self, attr_name: str, key) -> None:
        if not self.active or self.suppress_dict_trace > 0:
            return
        nk = _norm_dict_key(attr_name, key)
        if nk is None:
            return
        if self.current_test >= 0:
            self.test_dict_keys[attr_name][nk].add(self.current_test)
        elif self.current_test == -2 and self.current_class_key is not None:
            self.setup_dict_keys[self.current_class_key][attr_name].add(nk)

    def record_dict_iter(self, attr_name: str) -> None:
        if not self.active or self.suppress_dict_trace > 0:
            return
        if self.current_test >= 0:
            self.test_dict_iters[attr_name].add(self.current_test)
        elif self.current_test == -2 and self.current_class_key is not None:
            self.setup_dict_iters[self.current_class_key].add(attr_name)

    def record_sql_tokens(self, sql: str) -> None:
        if not self.active or not sql:
            return
        tokens_set: set[str] = set()
        upper_sql = sql.upper()
        words = _WORD_RE.findall(upper_sql)
        n_words = len(words)
        for i, w in enumerate(words):
            tokens_set.add(w)
            if i + 1 < n_words:
                w2 = f"{w} {words[i + 1]}"
                tokens_set.add(w2)
                if i + 2 < n_words:
                    tokens_set.add(f"{w2} {words[i + 2]}")
        for run in _NONALNUM_RUN_RE.findall(sql):
            rlen = len(run)
            max_sub = min(rlen, 5)
            for a in range(rlen):
                for b in range(a + 1, min(rlen, a + max_sub) + 1):
                    tokens_set.add("SYM:" + run[a:b])
        if self.current_test >= 0:
            tnum = self.current_test
            tmap = self.test_tokens
            for tok in tokens_set:
                tmap[tok].add(tnum)
        elif self.current_test == -2 and self.current_class_key is not None:
            self.setup_tokens[self.current_class_key].update(tokens_set)

    def record_time_format_str(self, s: str) -> None:
        if not self.active or not s or len(s) > 128:
            return
        slen = len(s)
        subs: set[str] = set()
        max_len = min(slen, 12)
        for i in range(slen):
            for j in range(i + 1, min(slen, i + max_len) + 1):
                subs.add(s[i:j])
        if self.current_test >= 0:
            tnum = self.current_test
            tmap = self.test_time_substrs
            for sub in subs:
                tmap[sub].add(tnum)
        elif self.current_test == -2 and self.current_class_key is not None:
            self.setup_time_substrs[self.current_class_key].update(subs)

    def _classify_code(self, code) -> tuple[str | None, int]:
        cached = self.code_meta.get(code)
        if cached is not None:
            return cached
        fn = code.co_filename
        rel = None
        if fn and not fn.startswith("<"):
            try:
                p = Path(fn).resolve()
                if str(p).lower().startswith(self.repo_prefix) and p.is_file():
                    rel = p.relative_to(self.repo_root).as_posix()
            except Exception:
                rel = None
        meta = (rel, code.co_firstlineno)
        self.code_meta[code] = meta
        return meta

    def on_py_start(self, code, instruction_offset):
        if not self.active:
            return sys.monitoring.DISABLE
        rel, firstline = self._classify_code(code)
        if rel is None:
            return sys.monitoring.DISABLE
        if self.current_test >= 0:
            self.test_funcs[self.current_test].add((rel, firstline))
            if rel.startswith("sqlglot/"):
                self.test_to_imported_modules[self.current_test].add(rel)
        elif self.current_test == -2 and self.current_class_key is not None:
            self.setup_funcs[self.current_class_key].add((rel, firstline))
            if rel.startswith("sqlglot/"):
                self.setup_modules[self.current_class_key].add(rel)
        return sys.monitoring.DISABLE

    def on_line(self, code, line_number):
        if not self.active:
            return sys.monitoring.DISABLE
        rel, _ = self._classify_code(code)
        if rel is None:
            return sys.monitoring.DISABLE
        if self.current_test >= 0:
            self.test_lines[self.current_test][rel].add(line_number)
        elif self.current_test == -2 and self.current_class_key is not None:
            self.setup_lines[self.current_class_key][rel].add(line_number)
        else:
            self.import_lines[rel].add(line_number)
        return sys.monitoring.DISABLE

    def on_audit(self, event: str, args):
        if event != "open" or not args:
            return
        path_arg = args[0]
        if not isinstance(path_arg, (str, os.PathLike)):
            return
        try:
            s = os.fspath(path_arg)
            if isinstance(s, bytes):
                s = s.decode("utf-8", errors="ignore")
            p = Path(s)
            if not p.is_absolute():
                p = (Path.cwd() / p).resolve()
            else:
                p = p.resolve()
            if str(p).lower().startswith(self.repo_prefix) and p.is_file():
                rel = p.relative_to(self.repo_root).as_posix()
                if (
                    "__pycache__" in rel
                    or rel.startswith(".git/")
                    or rel.endswith((".pyc", ".pyo", ".so", ".pyd"))
                ):
                    return
                if self.current_test >= 0:
                    self.test_files_opened[self.current_test].add(rel)
                elif self.current_class_key is not None:
                    self.setup_files_opened[self.current_class_key].add(rel)
        except Exception:
            pass


class _TrackedDict(dict):
    """Dictionary subclass that records key hits/misses and full iterations during tracing."""

    __slots__ = ("_attr_name", "_recorder")

    def __init__(self, initial, attr_name: str, recorder: _LineRecorder):
        super().__init__(initial)
        self._attr_name = attr_name
        self._recorder = recorder

    def __getitem__(self, key):
        self._recorder.record_dict_key(self._attr_name, key)
        return super().__getitem__(key)

    def get(self, key, default=None):
        self._recorder.record_dict_key(self._attr_name, key)
        return super().get(key, default)

    def __contains__(self, key):
        self._recorder.record_dict_key(self._attr_name, key)
        return super().__contains__(key)

    def __iter__(self):
        self._recorder.record_dict_iter(self._attr_name)
        return super().__iter__()

    def keys(self):
        self._recorder.record_dict_iter(self._attr_name)
        return super().keys()

    def values(self):
        self._recorder.record_dict_iter(self._attr_name)
        return super().values()

    def items(self):
        self._recorder.record_dict_iter(self._attr_name)
        return super().items()

    def __len__(self):
        self._recorder.record_dict_iter(self._attr_name)
        return super().__len__()

    def copy(self):
        return dict(self)

    def __reduce__(self):
        return (dict, (dict(self),))


def _extract_ast_info(repo_root: Path) -> dict:
    """Extract function ranges, class ranges, pruned symbol readers, and class/import graphs."""
    file_defs: dict[str, list[dict]] = {}
    file_classes: dict[str, list[dict]] = {}
    # symbol_name -> list of [rel_file, line_no]
    symbol_readers: dict[str, list[tuple[str, int]]] = collections.defaultdict(list)
    # class_name -> {rel_file, bases: [str], attrs: {attr_name: [start, end]}}
    class_graph: dict[str, list[dict]] = collections.defaultdict(list)
    # module_name -> set of imported sqlglot/tests modules
    module_imports: dict[str, set[str]] = collections.defaultdict(set)
    # Defined symbols in sqlglot/ to prune local-variable noise from symbol_readers
    defined_symbols: set[str] = set(_ATTR_DERIVED_SYMBOLS_KEEP)

    py_files = sorted(
        list((repo_root / "sqlglot").rglob("*.py"))
        + list((repo_root / "tests").rglob("*.py"))
    )

    for py_path in py_files:
        rel = py_path.relative_to(repo_root).as_posix()
        if rel == "tests/test_integration_loader.py":
            continue
        src = py_path.read_text(encoding="utf-8")
        tree = ast.parse(src, filename=rel)

        defs: list[dict] = []
        classes: list[dict] = []

        # Collect imports for both sqlglot/ and tests/
        if rel.startswith(("sqlglot/", "tests/")):
            mod_name = rel[:-3].replace("/", ".")
            if mod_name.endswith(".__init__"):
                mod_name = mod_name[:-9]
            for node in ast.walk(tree):
                if isinstance(node, ast.Import):
                    for alias in node.names:
                        if alias.name.startswith(("sqlglot", "tests")):
                            module_imports[mod_name].add(alias.name)
                elif isinstance(node, ast.ImportFrom):
                    if node.level == 0 and node.module and node.module.startswith(("sqlglot", "tests")):
                        module_imports[mod_name].add(node.module)
                        for alias in node.names:
                            if alias.name != "*":
                                module_imports[mod_name].add(f"{node.module}.{alias.name}")
                    elif node.level > 0:
                        parts = mod_name.split(".")
                        if rel.endswith("/__init__.py"):
                            base_parts = parts[: len(parts) - (node.level - 1)]
                        else:
                            base_parts = parts[: len(parts) - node.level]
                        target = ".".join(base_parts + ([node.module] if node.module else []))
                        if target.startswith(("sqlglot", "tests")):
                            module_imports[mod_name].add(target)
                            if not node.module:
                                for alias in node.names:
                                    if alias.name != "*":
                                        module_imports[mod_name].add(f"{target}.{alias.name}")

        # Walk top-down for functions and classes
        is_sqlglot = rel.startswith("sqlglot/")
        is_expr_file = rel.startswith("sqlglot/expressions/")

        if is_sqlglot:
            for stmt in tree.body:
                if isinstance(stmt, ast.Assign):
                    for tgt in stmt.targets:
                        if isinstance(tgt, ast.Name):
                            defined_symbols.add(tgt.id)
                elif isinstance(stmt, ast.AnnAssign) and isinstance(stmt.target, ast.Name):
                    defined_symbols.add(stmt.target.id)

        def visit(node: ast.AST, prefix: str = ""):
            for child in ast.iter_child_nodes(node):
                if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    qname = f"{prefix}.{child.name}" if prefix else child.name
                    start = min([child.lineno] + [d.lineno for d in child.decorator_list])
                    end = child.end_lineno or child.lineno
                    defs.append({
                        "q": qname,
                        "s": start,
                        "e": end,
                        "fl": child.lineno,
                    })
                    if is_sqlglot:
                        defined_symbols.add(child.name)
                    visit(child, qname)
                elif isinstance(child, ast.Lambda):
                    qname = f"{prefix}.<lambda>" if prefix else "<lambda>"
                    defs.append({
                        "q": qname,
                        "s": child.lineno,
                        "e": child.end_lineno or child.lineno,
                        "fl": child.lineno,
                    })
                    visit(child, qname)
                elif isinstance(child, ast.ClassDef):
                    qname = f"{prefix}.{child.name}" if prefix else child.name
                    start = min([child.lineno] + [d.lineno for d in child.decorator_list])
                    end = child.end_lineno or child.lineno
                    attrs: dict[str, list[int]] = {}
                    for stmt in child.body:
                        if isinstance(stmt, ast.Assign):
                            for tgt in stmt.targets:
                                if isinstance(tgt, ast.Name):
                                    attrs[tgt.id] = [stmt.lineno, stmt.end_lineno or stmt.lineno]
                                    if is_sqlglot:
                                        defined_symbols.add(tgt.id)
                        elif isinstance(stmt, ast.AnnAssign) and isinstance(stmt.target, ast.Name):
                            attrs[stmt.target.id] = [stmt.lineno, stmt.end_lineno or stmt.lineno]
                            if is_sqlglot:
                                defined_symbols.add(stmt.target.id)
                    bases = []
                    for b in child.bases:
                        if isinstance(b, ast.Name):
                            bases.append(b.id)
                        elif isinstance(b, ast.Attribute):
                            bases.append(b.attr)
                    classes.append({
                        "q": qname,
                        "s": start,
                        "e": end,
                        "attrs": attrs,
                    })
                    class_graph[child.name].append({
                        "file": rel,
                        "q": qname,
                        "bases": bases,
                        "s": start,
                        "e": end,
                    })
                    if is_sqlglot:
                        defined_symbols.add(child.name)
                        if is_expr_file:
                            snake1 = re.sub(
                                r"([a-z0-9])([A-Z])",
                                r"\1_\2",
                                re.sub(r"([A-Z]+)([A-Z][a-z])", r"\1_\2", child.name),
                            ).upper()
                            snake2 = re.sub(r"([a-z0-9])([A-Z])", r"\1_\2", child.name).upper()
                            defined_symbols.add(snake1)
                            defined_symbols.add(snake2)
                    visit(child, qname)
                else:
                    visit(child, prefix)

        visit(tree)
        file_defs[rel] = defs
        file_classes[rel] = classes

        # Collect symbol readers in sqlglot/ (Attribute loads and Name loads)
        if is_sqlglot:
            seen_sym_line: set[tuple[str, int]] = set()
            for node in ast.walk(tree):
                if isinstance(node, ast.Attribute) and isinstance(node.ctx, ast.Load):
                    key = (node.attr, node.lineno)
                    if key not in seen_sym_line:
                        seen_sym_line.add(key)
                        symbol_readers[node.attr].append((rel, node.lineno))
                elif isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load):
                    key = (node.id, node.lineno)
                    if key not in seen_sym_line:
                        seen_sym_line.add(key)
                        symbol_readers[node.id].append((rel, node.lineno))
                elif isinstance(node, ast.Subscript) and isinstance(node.ctx, ast.Load):
                    if isinstance(node.slice, ast.Constant) and isinstance(node.slice.value, str):
                        val = node.slice.value
                        if len(val) > 2:
                            key = (val, node.lineno)
                            if key not in seen_sym_line:
                                seen_sym_line.add(key)
                                symbol_readers[val].append((rel, node.lineno))

    pruned_readers = {
        k: sorted(set(v))
        for k, v in symbol_readers.items()
        if k in defined_symbols
    }

    return {
        "file_defs": file_defs,
        "file_classes": file_classes,
        "symbol_readers": pruned_readers,
        "class_graph": dict(class_graph),
        "module_imports": {k: sorted(v) for k, v in module_imports.items()},
    }


def _install_runtime_recorders(recorder: _LineRecorder) -> None:
    """Install lightweight runtime tracers for Expr, Dialect, dict keys, tokens, and format_time."""
    import sqlglot.dialects.dialect as sg_dialect
    import sqlglot.expressions.core as sg_exp_core
    import sqlglot.generator as sg_gen
    import sqlglot.parser as sg_parser
    import sqlglot.time as sg_time
    import sqlglot.tokenizer_core as sg_tok_core
    import sqlglot.tokens as sg_tokens

    Dialect = sg_dialect.Dialect
    _ = Dialect.classes  # ensure all 35 dialect modules & subclasses are loaded

    # 1. Expr.__init__ & Generator.sql -> expr_to_tests + TRANSFORMS dispatch
    orig_expr_init = sg_exp_core.Expr.__init__

    def _tracked_expr_init(self, **args):
        recorder.record_expr(self.__class__.__name__)
        return orig_expr_init(self, **args)

    sg_exp_core.Expr.__init__ = _tracked_expr_init

    orig_gen_sql = sg_gen.Generator.sql

    def _tracked_gen_sql(self, expression, key=None, comment=True):
        if key is None and isinstance(expression, sg_exp_core.Expr):
            recorder.record_expr(expression.__class__.__name__)
            recorder.record_dict_key("TRANSFORMS", expression.__class__)
        return orig_gen_sql(self, expression, key=key, comment=comment)

    sg_gen.Generator.sql = _tracked_gen_sql

    # 2. Dialect.get_or_raise & Dialect.__init__ -> dialect_used_tests
    orig_get_or_raise = Dialect.get_or_raise.__func__

    @classmethod
    def _tracked_get_or_raise(cls, dialect):
        res = orig_get_or_raise(cls, dialect)
        stem = type(res).__module__.rsplit(".", 1)[-1]
        recorder.record_dialect("" if stem == "dialect" else stem)
        if isinstance(dialect, str) and dialect:
            dname = dialect.split(",")[0].strip().lower()
            if dname:
                recorder.record_dialect(dname)
        return res

    Dialect.get_or_raise = _tracked_get_or_raise

    orig_dialect_init = Dialect.__init__

    def _tracked_dialect_init(self, **kwargs):
        stem = type(self).__module__.rsplit(".", 1)[-1]
        recorder.record_dialect("" if stem == "dialect" else stem)
        return orig_dialect_init(self, **kwargs)

    Dialect.__init__ = _tracked_dialect_init

    # 3. TokenizerCore.tokenize -> token_to_tests
    orig_tc_tokenize = sg_tok_core.TokenizerCore.tokenize

    def _tracked_tc_tokenize(self, sql):
        recorder.record_sql_tokens(sql)
        return orig_tc_tokenize(self, sql)

    sg_tok_core.TokenizerCore.tokenize = _tracked_tc_tokenize

    # 4. sqlglot.time.format_time -> time_substr_to_tests
    orig_format_time = sg_time.format_time

    def _tracked_format_time(string, mapping, trie=None):
        recorder.record_time_format_str(string)
        return orig_format_time(string, mapping, trie=trie)

    sg_time.format_time = _tracked_format_time
    for m in list(sys.modules.values()):
        if m is not None and getattr(m, "format_time", None) is orig_format_time:
            setattr(m, "format_time", _tracked_format_time)

    # 5. Suppress dict iteration tracing inside internal class/init boilerplate
    orig_build_dispatch = sg_gen._build_dispatch

    def _wrapped_build_dispatch(cls):
        recorder.suppress_dict_trace += 1
        try:
            return orig_build_dispatch(cls)
        finally:
            recorder.suppress_dict_trace -= 1

    sg_gen._build_dispatch = _wrapped_build_dispatch

    orig_init_core = sg_tokens.Tokenizer._init_core

    def _wrapped_init_core(self):
        recorder.suppress_dict_trace += 1
        try:
            return orig_init_core(self)
        finally:
            recorder.suppress_dict_trace -= 1

    sg_tokens.Tokenizer._init_core = _wrapped_init_core

    orig_dialect_new = sg_dialect._Dialect.__new__

    def _wrapped_dialect_new(cls, clsname, bases, attrs):
        recorder.suppress_dict_trace += 1
        try:
            return orig_dialect_new(cls, clsname, bases, attrs)
        finally:
            recorder.suppress_dict_trace -= 1

    sg_dialect._Dialect.__new__ = _wrapped_dialect_new

    orig_tok_init_sub = sg_tokens._TokenizerBase.__init_subclass__

    @classmethod
    def _wrapped_tok_init_sub(cls, **kwargs):
        recorder.suppress_dict_trace += 1
        try:
            return orig_tok_init_sub.__func__(cls, **kwargs)
        finally:
            recorder.suppress_dict_trace -= 1

    sg_tokens._TokenizerBase.__init_subclass__ = _wrapped_tok_init_sub

    # 6. Wrap class-level dicts on Generator, Parser, Tokenizer, Dialect & subclasses
    gen_attrs = ("TRANSFORMS", "TYPE_MAPPING", "PROPERTIES_LOCATION", "AFTER_HAVING_MODIFIER_TRANSFORMS")
    parser_attrs = (
        "FUNCTIONS",
        "FUNCTION_PARSERS",
        "STATEMENT_PARSERS",
        "PROPERTY_PARSERS",
        "UNARY_PARSERS",
        "PRIMARY_PARSERS",
        "PLACEHOLDER_PARSERS",
        "CONSTRAINT_PARSERS",
        "RANGE_PARSERS",
        "NO_PAREN_FUNCTIONS",
        "NO_PAREN_FUNCTION_PARSERS",
        "EXPRESSION_PARSERS",
        "QUERY_MODIFIER_PARSERS",
        "STRING_PARSERS",
    )
    dialect_attrs = (
        "TIME_MAPPING",
        "FORMAT_MAPPING",
        "INVERSE_TIME_MAPPING",
        "INVERSE_FORMAT_MAPPING",
        "DATE_PART_MAPPING",
        "SET_OP_DISTINCT_BY_DEFAULT",
    )
    tok_attrs = ("KEYWORDS", "SINGLE_TOKENS")

    wrapped_cache: dict[tuple[int, str], _TrackedDict] = {}

    def _wrap_class_attrs(klass: type, attrs: tuple[str, ...]) -> None:
        for attr_name in attrs:
            if attr_name not in klass.__dict__:
                continue
            val = klass.__dict__[attr_name]
            if isinstance(val, dict) and not isinstance(val, _TrackedDict):
                ckey = (id(val), attr_name)
                td = wrapped_cache.get(ckey)
                if td is None:
                    td = _TrackedDict(val, attr_name, recorder)
                    wrapped_cache[ckey] = td
                setattr(klass, attr_name, td)

    seen_classes: set[type] = set()
    candidates: list[type] = list(Dialect._classes.values())
    for mname, mod in list(sys.modules.items()):
        if mod is not None and mname.startswith("sqlglot"):
            for obj in mod.__dict__.values():
                if isinstance(obj, type):
                    candidates.append(obj)
                    for sub_attr in ("parser_class", "generator_class", "tokenizer_class", "jsonpath_tokenizer_class"):
                        sub_cls = getattr(obj, sub_attr, None)
                        if isinstance(sub_cls, type):
                            candidates.append(sub_cls)

    for klass in candidates:
        for base in klass.__mro__:
            if base in seen_classes:
                continue
            seen_classes.add(base)
            if issubclass(base, sg_gen.Generator):
                _wrap_class_attrs(base, gen_attrs)
            if issubclass(base, sg_parser.Parser):
                _wrap_class_attrs(base, parser_attrs)
            if issubclass(base, Dialect):
                _wrap_class_attrs(base, dialect_attrs)
            if issubclass(base, sg_tokens._TokenizerBase):
                _wrap_class_attrs(base, tok_attrs)

    sg_gen._DISPATCH_CACHE.clear()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", required=True, help="Path to sqlglot checkout")
    parser.add_argument("--tests", required=True, help="Path to tests.json")
    parser.add_argument("--out", required=True, help="Output blast_map.pkl.gz or .json.gz path")
    parser.add_argument("--limit", type=int, default=0, help="Optional limit on tests for debugging")
    args = parser.parse_args()

    t0 = time.perf_counter()
    repo_root = Path(args.repo).resolve()
    tests_path = Path(args.tests).resolve()
    out_path = Path(args.out).resolve()
    os.environ["SKIP_INTEGRATION"] = "0"
    os.chdir(repo_root)
    if str(repo_root) not in sys.path:
        sys.path.insert(0, str(repo_root))

    # Replace ProcessPoolExecutor before importing test modules
    concurrent.futures.ProcessPoolExecutor = InlinePoolExecutor

    tests_data = json.loads(tests_path.read_text(encoding="utf-8"))["tests"]
    if args.limit > 0:
        tests_data = tests_data[: args.limit]

    recorder = _LineRecorder(repo_root)
    sys.addaudithook(recorder.on_audit)

    TOOL_ID = sys.monitoring.PROFILER_ID
    sys.monitoring.use_tool_id(TOOL_ID, "blast_map")
    sys.monitoring.register_callback(TOOL_ID, sys.monitoring.events.PY_START, recorder.on_py_start)
    sys.monitoring.register_callback(TOOL_ID, sys.monitoring.events.LINE, recorder.on_line)
    events_mask = sys.monitoring.events.PY_START | sys.monitoring.events.LINE

    # Group tests by (file, class_name) preserving file order
    grouped: dict[tuple[str, str], list[dict]] = collections.OrderedDict()
    for t in tests_data:
        parts = t["id"].split("::")
        grouped.setdefault((parts[0], parts[1]), []).append(t)

    # Pre-import all sqlglot modules before activating tracing so lazy module imports
    # during the first test do not pollute line_to_tests or file_open_to_tests
    import sqlglot
    from sqlglot import Dialect

    for info in pkgutil.walk_packages(sqlglot.__path__, prefix="sqlglot."):
        if info.name == "sqlglot.__main__":
            continue
        try:
            importlib.import_module(info.name)
        except Exception:
            continue

    _install_runtime_recorders(recorder)

    failures = []
    # Also ensure Dialect.classes stays consistent across TestDialectEntryPoints
    for (rel_file, cls_name), items in grouped.items():
        mod_name = rel_file[:-3].replace("/", ".")
        mod = importlib.import_module(mod_name)
        if hasattr(mod, "ProcessPoolExecutor"):
            mod.ProcessPoolExecutor = InlinePoolExecutor
        cls = getattr(mod, cls_name)

        class_key = (rel_file, cls_name)
        recorder.current_class_key = class_key
        recorder.current_test = -1
        saved_dialects = dict(Dialect._classes) if cls_name == "TestDialectEntryPoints" else None

        if hasattr(cls, "setUpClass"):
            recorder.current_test = -2
            recorder.active = True
            sys.monitoring.set_events(TOOL_ID, events_mask)
            sys.monitoring.restart_events()
            try:
                cls.setUpClass()
            finally:
                recorder.active = False
                sys.monitoring.set_events(TOOL_ID, 0)
                recorder.current_test = -1

        s_lines = recorder.setup_lines.get(class_key)
        s_funcs = recorder.setup_funcs.get(class_key)
        s_mods = recorder.setup_modules.get(class_key)
        s_exprs = recorder.setup_exprs.get(class_key)
        s_dialects = recorder.setup_dialects.get(class_key)
        s_dkeys = recorder.setup_dict_keys.get(class_key)
        s_diters = recorder.setup_dict_iters.get(class_key)
        s_tokens = recorder.setup_tokens.get(class_key)
        s_tsubs = recorder.setup_time_substrs.get(class_key)

        for item in items:
            test_num = item["number"]
            method_name = item["id"].split("::")[2]
            tc = cls(method_name)
            result = unittest.TestResult()

            recorder.current_test = test_num
            recorder.active = True
            sys.monitoring.set_events(TOOL_ID, events_mask)
            sys.monitoring.restart_events()

            # Run setUp, method, tearDown, doCleanups without tearDownClass
            tc.run(result)

            recorder.active = False
            sys.monitoring.set_events(TOOL_ID, 0)
            recorder.current_test = -1

            if s_lines:
                for rf, lns in s_lines.items():
                    recorder.test_lines[test_num][rf].update(lns)
            if s_funcs:
                recorder.test_funcs[test_num].update(s_funcs)
            if s_mods:
                recorder.test_to_imported_modules[test_num].update(s_mods)
            if s_exprs:
                recorder.test_exprs[test_num].update(s_exprs)
            if s_dialects:
                recorder.test_dialects[test_num].update(s_dialects)
            if s_dkeys:
                for attr_n, ks in s_dkeys.items():
                    dmap = recorder.test_dict_keys[attr_n]
                    for k in ks:
                        dmap[k].add(test_num)
            if s_diters:
                for attr_n in s_diters:
                    recorder.test_dict_iters[attr_n].add(test_num)
            if s_tokens:
                tmap = recorder.test_tokens
                for tok in s_tokens:
                    tmap[tok].add(test_num)
            if s_tsubs:
                tsmap = recorder.test_time_substrs
                for sub in s_tsubs:
                    tsmap[sub].add(test_num)

            if not result.wasSuccessful():
                failures.append((test_num, item["id"], result.errors + result.failures))

        if hasattr(cls, "doClassCleanups"):
            cls.doClassCleanups()
        if hasattr(cls, "tearDownClass"):
            cls.tearDownClass()
        if saved_dialects is not None:
            Dialect._classes.update(saved_dialects)
        recorder.current_class_key = None

    sys.monitoring.free_tool_id(TOOL_ID)
    elapsed_exec = time.perf_counter() - t0
    print(
        f"Executed {len(tests_data)} tests in {elapsed_exec:.2f}s (failures={len(failures)})",
        file=sys.stderr,
    )
    if failures:
        for num, tid, errs in failures[:10]:
            print(f"  FAIL #{num} {tid}: {errs[0][1][:200]}", file=sys.stderr)

    # Intern unique sorted test-number tuples so shared basic blocks share one set_id
    set_pool: dict[tuple[int, ...], int] = {}
    test_sets: list[list[int]] = []

    def intern(nums) -> int:
        key = tuple(sorted(set(nums)))
        sid = set_pool.get(key)
        if sid is None:
            sid = len(test_sets)
            set_pool[key] = sid
            test_sets.append(list(key))
        return sid

    # Build inverted indices using set_ids
    line_to_tests: dict[str, dict[str, int]] = collections.defaultdict(dict)
    tmp_line: dict[str, dict[int, list[int]]] = collections.defaultdict(lambda: collections.defaultdict(list))
    file_to_tests: dict[str, set[int]] = collections.defaultdict(set)

    for test_num, files_dict in recorder.test_lines.items():
        for rel_file, lines in files_dict.items():
            file_to_tests[rel_file].add(test_num)
            for ln in lines:
                tmp_line[rel_file][ln].append(test_num)

    for rel_file, lines_map in tmp_line.items():
        line_to_tests[rel_file] = {str(ln): intern(nums) for ln, nums in lines_map.items()}

    # func_to_tests: rel_file -> { str(firstlineno): set_id }
    func_to_tests: dict[str, dict[str, int]] = collections.defaultdict(dict)
    tmp_func: dict[str, dict[int, list[int]]] = collections.defaultdict(lambda: collections.defaultdict(list))
    for test_num, funcs in recorder.test_funcs.items():
        for rel_file, fl in funcs:
            tmp_func[rel_file][fl].append(test_num)
    for rel_file, fl_map in tmp_func.items():
        func_to_tests[rel_file] = {str(fl): intern(nums) for fl, nums in fl_map.items()}

    # file_open_to_tests: opened_rel -> set_id
    tmp_open: dict[str, set[int]] = collections.defaultdict(set)
    for test_num, opened in recorder.test_files_opened.items():
        for rel in opened:
            tmp_open[rel].add(test_num)
    for (rel_file, cls_name), opened in recorder.setup_files_opened.items():
        cls_tests = [t["number"] for t in grouped[(rel_file, cls_name)]]
        for rel in opened:
            tmp_open[rel].update(cls_tests)
    file_open_to_tests = {rel: intern(nums) for rel, nums in tmp_open.items()}

    # expr_to_tests: expr_class_name -> set_id
    tmp_expr: dict[str, list[int]] = collections.defaultdict(list)
    for test_num, enames in recorder.test_exprs.items():
        for en in enames:
            tmp_expr[en].append(test_num)
    expr_to_tests = {en: intern(nums) for en, nums in tmp_expr.items()}

    # dialect_used_tests: dialect_stem -> set_id
    tmp_dial: dict[str, list[int]] = collections.defaultdict(list)
    for test_num, dnames in recorder.test_dialects.items():
        for dn in dnames:
            tmp_dial[dn].append(test_num)
    dialect_used_tests = {dn: intern(nums) for dn, nums in tmp_dial.items()}

    # dict_key_to_tests & dict_iter_tests
    dict_key_to_tests: dict[str, dict[str, int]] = {}
    for attr_n, kmap in recorder.test_dict_keys.items():
        dict_key_to_tests[attr_n] = {k: intern(nums) for k, nums in kmap.items()}
    dict_iter_tests = {attr_n: intern(nums) for attr_n, nums in recorder.test_dict_iters.items()}

    # token_to_tests & time_substr_to_tests
    token_to_tests = {tok: intern(nums) for tok, nums in recorder.test_tokens.items()}
    time_substr_to_tests = {sub: intern(nums) for sub, nums in recorder.test_time_substrs.items()}

    ast_info = _extract_ast_info(repo_root)

    # Precompute reverse indices so BlastSelector.__init__ does zero disk reads
    dialect_file_re = re.compile(r"^sqlglot/(?:dialects|parsers|generators|typing)/([a-z0-9_]+)\.py$")
    test_dialect_file_re = re.compile(r"^tests/dialects/test_([a-z0-9_]+)\.py$")
    tmp_dialect_tests: dict[str, set[int]] = collections.defaultdict(set)
    for rel, nums in file_to_tests.items():
        m = dialect_file_re.match(rel) or test_dialect_file_re.match(rel)
        if m:
            tmp_dialect_tests[m.group(1)].update(nums)
    dialect_tests_pre = {k: intern(v) for k, v in tmp_dialect_tests.items()}

    dialect_stems = sorted(
        Path(rel).stem
        for rel in ast_info["file_defs"]
        if rel.startswith("sqlglot/dialects/")
        and Path(rel).stem not in ("dialect", "__init__", "python")
    )
    tmp_cross: dict[str, set[int]] = collections.defaultdict(set)
    if dialect_stems:
        d_pat = re.compile(
            r"""['"](?:""" + "|".join(re.escape(s) for s in dialect_stems) + r""")['"]"""
            + r"""|\bDialects\.(?:""" + "|".join(re.escape(s.upper()) for s in dialect_stems) + r""")\b"""
        )
        by_file: dict[str, list[tuple[int, str, str]]] = collections.defaultdict(list)
        for t in tests_data:
            parts = t["id"].split("::")
            if len(parts) == 3:
                by_file[parts[0]].append((t["number"], parts[1], parts[2]))
        for tfile in sorted(by_file):
            tp = repo_root / tfile
            if not tp.is_file():
                continue
            lines = tp.read_text(encoding="utf-8", errors="ignore").splitlines()
            defs_for_file = ast_info["file_defs"].get(tfile, ())
            cls_fn_ranges = {
                tuple(d["q"].split(".")[-2:]): (d["s"], d["e"])
                for d in defs_for_file
                if "." in d["q"]
            }
            fn_ranges = {d["q"].split(".")[-1]: (d["s"], d["e"]) for d in defs_for_file}
            in_method_lines: set[int] = set()
            for num, t_cls, mname in by_file[tfile]:
                rng = cls_fn_ranges.get((t_cls, mname)) or fn_ranges.get(mname)
                if not rng:
                    continue
                in_method_lines.update(range(rng[0], rng[1] + 1))
                snippet = "\n".join(lines[rng[0] - 1 : rng[1]])
                for match in d_pat.finditer(snippet):
                    tok = match.group(0)
                    stem = tok[9:].lower() if tok.startswith("Dialects.") else tok[1:-1]
                    tmp_cross[stem].add(num)
            # Also scan module/class helper lines outside test methods in that test file
            file_nums = [num for num, _, _ in by_file[tfile]]
            non_method_text = "\n".join(
                line for idx, line in enumerate(lines, 1) if idx not in in_method_lines
            )
            for match in d_pat.finditer(non_method_text):
                tok = match.group(0)
                stem = tok[9:].lower() if tok.startswith("Dialects.") else tok[1:-1]
                tmp_cross[stem].update(file_nums)
    cross_dialect_tests_pre = {k: intern(v) for k, v in tmp_cross.items()}

    subclasses_pre: dict[str, set[str]] = collections.defaultdict(set)
    for cname, defs_list in ast_info["class_graph"].items():
        for d in defs_list:
            if "." not in d["q"]:
                for base in d["bases"]:
                    subclasses_pre[base].add(cname)

    reverse_mod_files_pre: dict[str, set[str]] = collections.defaultdict(set)
    for mod, deps in ast_info["module_imports"].items():
        src_rel = mod.replace(".", "/") + ".py"
        if not (repo_root / src_rel).is_file() and (repo_root / mod.replace(".", "/") / "__init__.py").is_file():
            src_rel = mod.replace(".", "/") + "/__init__.py"
        for dep in deps:
            reverse_mod_files_pre[dep].add(src_rel)

    payload = {
        "test_sets": test_sets,
        "line_to_tests": dict(line_to_tests),
        "func_to_tests": dict(func_to_tests),
        "file_to_tests": {k: intern(v) for k, v in file_to_tests.items()},
        "file_open_to_tests": file_open_to_tests,
        "file_defs": ast_info["file_defs"],
        "file_classes": ast_info["file_classes"],
        "symbol_readers": ast_info["symbol_readers"],
        "class_graph": ast_info["class_graph"],
        "module_imports": ast_info["module_imports"],
        "expr_to_tests": expr_to_tests,
        "dialect_used_tests": dialect_used_tests,
        "dict_key_to_tests": dict_key_to_tests,
        "dict_iter_tests": dict_iter_tests,
        "token_to_tests": token_to_tests,
        "time_substr_to_tests": time_substr_to_tests,
        "dialect_tests": dialect_tests_pre,
        "cross_dialect_tests": cross_dialect_tests_pre,
        "subclasses": {k: sorted(v) for k, v in subclasses_pre.items()},
        "reverse_mod_files": {k: sorted(v) for k, v in reverse_mod_files_pre.items()},
    }

    if out_path.name.endswith(".pkl.gz") or out_path.suffix == ".pkl":
        raw = pickle.dumps(payload, protocol=4)
    else:
        raw = json.dumps(payload, separators=(",", ":")).encode("utf-8")

    if out_path.name.endswith(".gz"):
        with gzip.open(out_path, "wb", compresslevel=9) as gz:
            gz.write(raw)
    else:
        out_path.write_bytes(raw)

    print(
        f"Wrote {out_path} ({out_path.stat().st_size / 1024:.1f} KB, raw {len(raw) / 1024:.1f} KB, "
        f"sets={len(test_sets)}, exprs={len(expr_to_tests)}, dialects={len(dialect_used_tests)}, "
        f"tokens={len(token_to_tests)}, time_subs={len(time_substr_to_tests)}, "
        f"dict_attrs={len(dict_key_to_tests)}, dict_iters={ {k: len(test_sets[v]) for k, v in dict_iter_tests.items()} }) "
        f"in {time.perf_counter() - t0:.2f}s total",
        file=sys.stderr,
    )
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
