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
import sys
import time
import unittest


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
        self.current_test: int = -1
        # code_obj -> (rel_file_or_None, set_of_lines)
        self.code_meta: dict[object, tuple[str | None, int]] = {}
        self.test_lines: dict[int, dict[str, set[int]]] = collections.defaultdict(
            lambda: collections.defaultdict(set)
        )
        self.test_funcs: dict[int, set[tuple[str, int]]] = collections.defaultdict(set)
        self.test_files_opened: dict[int, set[str]] = collections.defaultdict(set)
        self.setup_files_opened: dict[tuple[str, str], set[str]] = collections.defaultdict(set)
        self.current_class_key: tuple[str, str] | None = None
        self.import_lines: dict[str, set[int]] = collections.defaultdict(set)
        self.test_to_imported_modules: dict[int, set[str]] = collections.defaultdict(set)

    def _classify_code(self, code) -> tuple[str | None, int]:
        cached = self.code_meta.get(code)
        if cached is not None:
            return cached
        fn = code.co_filename
        rel = None
        if fn and not fn.startswith("<"):
            try:
                p = Path(fn).resolve()
                if str(p).lower().startswith(self.repo_prefix):
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
        return sys.monitoring.DISABLE

    def on_line(self, code, line_number):
        if not self.active:
            return sys.monitoring.DISABLE
        rel, _ = self._classify_code(code)
        if rel is None:
            return sys.monitoring.DISABLE
        if self.current_test >= 0:
            self.test_lines[self.current_test][rel].add(line_number)
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
            if str(p).lower().startswith(self.repo_prefix):
                rel = p.relative_to(self.repo_root).as_posix()
                if rel.startswith(("tests/fixtures/", "sqlglot/", "sqlglotc/")):
                    if self.current_test >= 0:
                        self.test_files_opened[self.current_test].add(rel)
                    elif self.current_class_key is not None:
                        self.setup_files_opened[self.current_class_key].add(rel)
        except Exception:
            pass


def _extract_ast_info(repo_root: Path) -> dict:
    """Extract function ranges, class ranges, symbol readers, and class/import graphs."""
    file_defs: dict[str, list[dict]] = {}
    file_classes: dict[str, list[dict]] = {}
    # symbol_name -> list of [rel_file, line_no]
    symbol_readers: dict[str, list[tuple[str, int]]] = collections.defaultdict(list)
    # class_name -> {rel_file, bases: [str], attrs: {attr_name: [start, end]}}
    class_graph: dict[str, list[dict]] = collections.defaultdict(list)
    # module_name -> set of imported sqlglot modules
    module_imports: dict[str, set[str]] = collections.defaultdict(set)

    py_files = sorted(
        list((repo_root / "sqlglot").rglob("*.py"))
        + list((repo_root / "tests").rglob("*.py"))
    )

    for py_path in py_files:
        rel = py_path.relative_to(repo_root).as_posix()
        src = py_path.read_text(encoding="utf-8")
        tree = ast.parse(src, filename=rel)

        defs: list[dict] = []
        classes: list[dict] = []

        # Collect imports
        if rel.startswith("sqlglot/"):
            mod_name = rel[:-3].replace("/", ".")
            if mod_name.endswith(".__init__"):
                mod_name = mod_name[:-9]
            for node in ast.walk(tree):
                if isinstance(node, ast.Import):
                    for alias in node.names:
                        if alias.name.startswith("sqlglot"):
                            module_imports[mod_name].add(alias.name)
                elif isinstance(node, ast.ImportFrom) and node.module:
                    if node.level == 0 and node.module.startswith("sqlglot"):
                        module_imports[mod_name].add(node.module)
                        for alias in node.names:
                            module_imports[mod_name].add(f"{node.module}.{alias.name}")
                    elif node.level > 0:
                        parts = mod_name.split(".")
                        if rel.endswith("/__init__.py"):
                            base_parts = parts[: len(parts) - (node.level - 1)]
                        else:
                            base_parts = parts[: len(parts) - node.level]
                        target = ".".join(base_parts + ([node.module] if node.module else []))
                        if target.startswith("sqlglot"):
                            module_imports[mod_name].add(target)

        # Walk top-down for functions and classes
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
                        elif isinstance(stmt, ast.AnnAssign) and isinstance(stmt.target, ast.Name):
                            attrs[stmt.target.id] = [stmt.lineno, stmt.end_lineno or stmt.lineno]
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
                    visit(child, qname)
                else:
                    visit(child, prefix)

        visit(tree)
        file_defs[rel] = defs
        file_classes[rel] = classes

        # Collect symbol readers in sqlglot/ (Attribute loads and Name loads)
        if rel.startswith("sqlglot/"):
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

    return {
        "file_defs": file_defs,
        "file_classes": file_classes,
        "symbol_readers": {k: sorted(set(v)) for k, v in symbol_readers.items()},
        "class_graph": dict(class_graph),
        "module_imports": {k: sorted(v) for k, v in module_imports.items()},
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", required=True, help="Path to sqlglot checkout")
    parser.add_argument("--tests", required=True, help="Path to tests.json")
    parser.add_argument("--out", required=True, help="Output blast_map.json.gz path")
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

    # Pre-import sqlglot to separate base import lines if desired
    import sqlglot
    from sqlglot import Dialect

    failures = []
    # Also ensure Dialect.classes stays consistent across TestDialectEntryPoints
    for (rel_file, cls_name), items in grouped.items():
        mod_name = rel_file[:-3].replace("/", ".")
        mod = importlib.import_module(mod_name)
        if hasattr(mod, "ProcessPoolExecutor"):
            mod.ProcessPoolExecutor = InlinePoolExecutor
        cls = getattr(mod, cls_name)

        recorder.current_class_key = (rel_file, cls_name)
        recorder.current_test = -1
        saved_dialects = dict(Dialect._classes) if cls_name == "TestDialectEntryPoints" else None

        if hasattr(cls, "setUpClass"):
            cls.setUpClass()

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

    ast_info = _extract_ast_info(repo_root)

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
    }

    raw = json.dumps(payload, separators=(",", ":")).encode("utf-8")
    with gzip.open(out_path, "wb", compresslevel=9) as gz:
        gz.write(raw)

    print(
        f"Wrote {out_path} ({out_path.stat().st_size / 1024:.1f} KB, raw {len(raw) / 1024:.1f} KB) "
        f"in {time.perf_counter() - t0:.2f}s total",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
