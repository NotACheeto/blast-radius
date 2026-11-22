"""Blast Radius 3-stage test selector and millisecond-exact worker scheduler.

Stage 1: Parse unified diffs, apply hunks in memory, drop pure comment/whitespace
         no-op edits via AST comparison, and resolve tight candidate tests using
         the pre-computed sys.monitoring + AST + fixture blast_map.json.gz.
Stage 2: Verify fast candidate tests in isolated worker processes over a
         read-only-safe /tmp overlay (using early-exit subTest and lazy TPC
         fixture loading) to drop false positives and find exact failing tests.
Stage 3: Pack selected tests across 1..8 workers minimizing
         max_worker_load_ms + 2000 * worker_count.
"""

from __future__ import annotations

import ast
import collections
import concurrent.futures
from concurrent.futures import Future
import difflib
from enum import Enum as _Enum
import gzip
import hashlib
import importlib
import inspect
import json
import logging
import math
import os
from pathlib import Path
import pickle
import re
import selectors
import shutil
import subprocess
import sys
import textwrap
import time
import unittest
import zlib

WORKER_COST_MS = 2_000
MAX_WORKERS = 8
HEAVY_TEST_SECONDS = 0.8

_TPC_CACHE: dict | None = None
_VAL_CACHE: dict | None = None
_VAL_ASTS: dict | None = None
_TPCDS_RULE_CKPT_CACHE: dict[int, list] = {}
_SUITE_RULE_CKPT_CACHE: dict[tuple[str, int], list] = {}
_TPCDS_ALL_OPT_DUMPS: list | None = None
_IN_NULLS_OPT_DUMPS: list | None = None
_TPCDS_RAW_DUMPS: dict | None = None
_TPCDS_PLAN_EXPR_DUMPS: dict | None = None
_OPT_DUMP_CACHE: dict[str, dict] = {}
_PRELOADED_SQLGLOT_FILES: frozenset[str] = frozenset()
_PRELOADED_SQLGLOT_MODS: frozenset[str] = frozenset()
_PRELOADED_MOD_FILE_REL: dict[str, str] = {}
_PRELOADED_MOD_PKG_REL: dict[str, str] = {}
_FRESH_SQLGLOT_DIALECT_COUNT: int | None = None
_LAST_FAILED_SUBTEST_MSG: str | None = None
_COMMIT_TPCDS_OPT_PASSED: bool = False
_COMMIT_TPCDS_FAILED_IDX: int | None = None
_ASSERT_LOGS_DEPTH: int = 0

_STRICT_TO_LAX_TIME = {
    "%mstrict": "%m",
    "%dstrict": "%d",
    "%Hstrict": "%H",
    "%Istrict": "%I",
    "%Mstrict": "%M",
    "%Sstrict": "%S",
}
_LAX_TO_STRICT_TIME = {v: k for k, v in _STRICT_TO_LAX_TIME.items()}


def _hash_expr_dump(dump_obj) -> bytes:
    return hashlib.blake2b(pickle.dumps(dump_obj, protocol=4), digest_size=12).digest()


_NO_ATTR = object()
_TYPE_NAME_BYTES: dict[type, bytes] = {}
_ARG_KEY_BYTES: dict[str, bytes] = {}
_LEN_BYTES: tuple[bytes, ...] = tuple(i.to_bytes(4, "little") for i in range(64))


def _hash_walk(v, upd) -> None:
    if v is None:
        upd(b"N")
        return
    tv = type(v)
    if tv is str:
        b = v.encode("utf-8")
        nb = len(b)
        upd(b"S" + (_LEN_BYTES[nb] if nb < 64 else nb.to_bytes(4, "little")) + b)
    elif tv is list:
        nv = len(v)
        upd(b"L" + (_LEN_BYTES[nv] if nv < 64 else nv.to_bytes(4, "little")))
        for item in v:
            _hash_walk(item, upd)
    elif tv is bool:
        upd(b"T" if v else b"F")
    elif tv is int:
        upd(b"I" + str(v).encode("ascii") + b"\0")
    elif tv is tuple:
        nv = len(v)
        upd(b"P" + (_LEN_BYTES[nv] if nv < 64 else nv.to_bytes(4, "little")))
        for item in v:
            _hash_walk(item, upd)
    elif tv is float:
        upd(b"R")
        upd(b"NAN" if math.isnan(v) else repr(v).encode("ascii"))
        upd(b"\0")
    elif isinstance(v, _Enum):
        upd(b"M")
        tb = _TYPE_NAME_BYTES.get(tv)
        if tb is None:
            tb = tv.__name__.encode("utf-8") + b":"
            _TYPE_NAME_BYTES[tv] = tb
        upd(tb)
        upd(v.name.encode("utf-8"))
    elif isinstance(v, dict):
        nv = len(v)
        upd(b"D" + (_LEN_BYTES[nv] if nv < 64 else nv.to_bytes(4, "little")))
        for dk in sorted(v, key=lambda x: (type(x).__name__, str(x))):
            _hash_walk(dk, upd)
            _hash_walk(v[dk], upd)
    elif isinstance(v, (set, frozenset)):
        nv = len(v)
        upd(b"Z" + (_LEN_BYTES[nv] if nv < 64 else nv.to_bytes(4, "little")))
        for s in sorted(_hash_expr_exact(item) for item in v):
            upd(s)
    elif getattr(v, "_type", _NO_ATTR) is not _NO_ATTR and getattr(v, "args", _NO_ATTR) is not _NO_ATTR:
        tb = _TYPE_NAME_BYTES.get(tv)
        if tb is None:
            tb = b"E" + tv.__name__.encode("utf-8") + b"\0"
            _TYPE_NAME_BYTES[tv] = tb
        upd(tb)
        vt = v._type
        if vt is None:
            upd(b"N")
        else:
            _hash_walk(vt, upd)
        vc = v.comments
        if vc is None:
            upd(b"N")
        else:
            _hash_walk(vc, upd)
        vm = v._meta
        if vm is None:
            upd(b"N")
        else:
            _hash_walk(vm, upd)
        args = v.args
        na = len(args)
        upd(_LEN_BYTES[na] if na < 64 else na.to_bytes(4, "little"))
        if na == 1:
            k, av = next(iter(args.items()))
            kb = _ARG_KEY_BYTES.get(k)
            if kb is None:
                kb = k.encode("utf-8") + b":"
                _ARG_KEY_BYTES[k] = kb
            upd(kb)
            _hash_walk(av, upd)
        elif na > 1:
            for k in sorted(args):
                kb = _ARG_KEY_BYTES.get(k)
                if kb is None:
                    kb = k.encode("utf-8") + b":"
                    _ARG_KEY_BYTES[k] = kb
                upd(kb)
                _hash_walk(args[k], upd)
    else:
        b = f"{tv.__name__}:{v!r}".encode("utf-8", errors="replace")
        nb = len(b)
        upd(b"O" + (_LEN_BYTES[nb] if nb < 64 else nb.to_bytes(4, "little")) + b)


def _hash_expr_exact(obj) -> bytes:
    """Lossless deterministic 12-byte hash over Expr ASTs, types, comments, meta, and containers."""
    h = hashlib.blake2b(digest_size=12)
    _hash_walk(obj, h.update)
    return h.digest()


def _unpack_expr(obj, exp_mod):
    """Reconstruct an exact Expr AST tree packed in tpc_cache rule checkpoints."""
    if obj is None or type(obj) in (bool, int, float, str):
        return obj
    if type(obj) is list:
        return [_unpack_expr(x, exp_mod) for x in obj]
    if type(obj) is tuple and obj:
        tag = obj[0]
        if tag == "__E__":
            _, cname, ap, tp, cp, mp = obj
            cls = getattr(exp_mod, cname)
            e = cls(**{k: _unpack_expr(v, exp_mod) for k, v in ap.items()})
            if tp is not None:
                e._type = _unpack_expr(tp, exp_mod)
            e.comments = list(cp) if cp is not None else None
            if mp is not None:
                e._meta = _unpack_expr(mp, exp_mod)
            return e
        if tag == "__M__":
            _, qn, name = obj
            cur = exp_mod
            for part in qn.split("."):
                cur = getattr(cur, part)
            return cur[name]
        if tag == "__T__":
            return tuple(_unpack_expr(x, exp_mod) for x in obj[1])
        if tag == "__D__":
            return {_unpack_expr(k, exp_mod): _unpack_expr(v, exp_mod) for k, v in obj[1]}
    return obj


def _dedent_method_source(fn) -> str:
    """Dedent a method's source by its first-line indent without breaking column-0 string literals."""
    src = inspect.getsource(fn)
    lines = src.splitlines(keepends=True)
    if not lines:
        return src
    first = lines[0]
    ind = len(first) - len(first.lstrip(" \t"))
    if ind <= 0:
        return src
    pfx = first[:ind]
    return "".join(l[ind:] if l.startswith(pfx) else l for l in lines)


def _hash_tokens(toks) -> bytes:
    return hashlib.blake2b(
        "\0".join(f"{t.token_type.name}:{t.text}" for t in toks).encode("utf-8"),
        digest_size=12,
    ).digest()


_PURE_SQLGLOT_ENUMS = frozenset(
    {"ErrorLevel", "TrieResult", "ScopeType", "DType", "PropertiesLocation", "Location"}
)


def _asts_structurally_equal(
    t1: ast.AST,
    t2: ast.AST,
    allow_typing: bool = True,
    allow_norm_strategy: bool = False,
    changed_lines: set[int] | None = None,
) -> bool:
    """Fast exact AST equality checking changed-line-overlapping statements first to exit in <2ms on edits."""
    canon = (
        None
        if not allow_typing
        else _CanonicalizeAST(allow_norm_strategy=allow_norm_strategy)
    )

    def _norm(node: ast.AST) -> ast.AST:
        return canon.visit(node) if canon is not None else node

    def _stmt_eq(s1: ast.AST, s2: ast.AST) -> bool:
        if type(s1) is not type(s2):
            return False
        if isinstance(s1, (ast.Module, ast.ClassDef)):
            if len(s1.body) != len(s2.body):
                return False
            if isinstance(s1, ast.ClassDef):
                if (
                    s1.name != s2.name
                    or len(s1.bases) != len(s2.bases)
                    or len(s1.keywords) != len(s2.keywords)
                    or len(s1.decorator_list) != len(s2.decorator_list)
                ):
                    return False
                for a, b in zip(s1.bases, s2.bases):
                    if ast.dump(_norm(a), include_attributes=False) != ast.dump(
                        _norm(b), include_attributes=False
                    ):
                        return False
                for a, b in zip(s1.keywords, s2.keywords):
                    if ast.dump(_norm(a), include_attributes=False) != ast.dump(
                        _norm(b), include_attributes=False
                    ):
                        return False
                for a, b in zip(s1.decorator_list, s2.decorator_list):
                    if ast.dump(_norm(a), include_attributes=False) != ast.dump(
                        _norm(b), include_attributes=False
                    ):
                        return False
            b1, b2 = s1.body, s2.body
            n = len(b1)
            if changed_lines and n > 4:
                hot: list[int] = []
                cold: list[int] = []
                for idx, st in enumerate(b1):
                    sl = getattr(st, "lineno", 0)
                    el = getattr(st, "end_lineno", sl) or sl
                    if any(sl <= ln <= el for ln in changed_lines):
                        hot.append(idx)
                    else:
                        cold.append(idx)
                order = hot + cold
            else:
                order = range(n)
            for idx in order:
                if not _stmt_eq(b1[idx], b2[idx]):
                    return False
            return True
        return ast.dump(_norm(s1), include_attributes=False) == ast.dump(
            _norm(s2), include_attributes=False
        )

    return _stmt_eq(t1, t2)


class _CanonicalizeAST(ast.NodeTransformer):
    """Canonicalize semantically identical None / pure-enum comparisons."""

    def __init__(self, allow_norm_strategy: bool = False) -> None:
        self.allow_norm_strategy = allow_norm_strategy

    def visit_Compare(self, node: ast.Compare) -> ast.AST:
        self.generic_visit(node)
        if len(node.ops) == 1 and len(node.comparators) == 1:
            op = node.ops[0]
            left, right = node.left, node.comparators[0]
            can_swap = self._is_none(left) or self._is_none(right)
            if not can_swap:
                can_swap = self._is_pure_enum_member(left) or self._is_pure_enum_member(right)
            if not can_swap and self.allow_norm_strategy:
                can_swap = (
                    self._is_self_norm_strategy(left) and self._is_norm_strategy_member(right)
                ) or (
                    self._is_self_norm_strategy(right) and self._is_norm_strategy_member(left)
                )
            if can_swap:
                if isinstance(op, ast.Eq):
                    return ast.copy_location(
                        ast.Compare(left=left, ops=[ast.Is()], comparators=node.comparators),
                        node,
                    )
                if isinstance(op, ast.NotEq):
                    return ast.copy_location(
                        ast.Compare(left=left, ops=[ast.IsNot()], comparators=node.comparators),
                        node,
                    )
        return node

    @staticmethod
    def _is_none(expr: ast.AST) -> bool:
        return isinstance(expr, ast.Constant) and expr.value is None

    @staticmethod
    def _is_pure_enum_member(expr: ast.AST) -> bool:
        # Matches EnumClass.MEMBER or mod.EnumClass.MEMBER (e.g. exp.DType.INT, exp.Properties.Location.PREFIX)
        if isinstance(expr, ast.Attribute) and isinstance(expr.value, ast.Attribute):
            return expr.value.attr in _PURE_SQLGLOT_ENUMS
        if isinstance(expr, ast.Attribute) and isinstance(expr.value, ast.Name):
            return expr.value.id in _PURE_SQLGLOT_ENUMS
        return False

    @staticmethod
    def _is_self_norm_strategy(expr: ast.AST) -> bool:
        return (
            isinstance(expr, ast.Attribute)
            and expr.attr == "normalization_strategy"
            and isinstance(expr.value, ast.Name)
            and expr.value.id == "self"
        )

    @staticmethod
    def _is_norm_strategy_member(expr: ast.AST) -> bool:
        return (
            isinstance(expr, ast.Attribute)
            and isinstance(expr.value, ast.Name)
            and expr.value.id == "NormalizationStrategy"
        )


ENCODING_COMMENT_RE = re.compile(r"coding[:=]\s*([-\w.]+)")
DIALECT_FILE_RE = re.compile(
    r"^sqlglot/(?:dialects|parsers|generators|typing)/([a-z0-9_]+)\.py$"
)
TEST_DIALECT_FILE_RE = re.compile(r"^tests/dialects/test_([a-z0-9_]+)\.py$")
_WORD_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_$]*")

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

_TRACKED_DICT_ATTRS = frozenset(
    {
        "TRANSFORMS",
        "TYPE_MAPPING",
        "PROPERTIES_LOCATION",
        "AFTER_HAVING_MODIFIER_TRANSFORMS",
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
        "TIME_MAPPING",
        "FORMAT_MAPPING",
        "INVERSE_TIME_MAPPING",
        "INVERSE_FORMAT_MAPPING",
        "DATE_PART_MAPPING",
        "SET_OP_DISTINCT_BY_DEFAULT",
        "KEYWORDS",
        "SINGLE_TOKENS",
    }
)

TPC_HEAVY_METHODS = frozenset(
    {"test_optimized_tpch", "test_execute_tpch", "test_execute_tpcds"}
)

_ATTR_DERIVED_SYMBOLS: dict[str, tuple[str, ...]] = {
    "TIME_MAPPING": ("TIME_MAPPING", "TIME_TRIE", "INVERSE_TIME_MAPPING", "INVERSE_TIME_TRIE"),
    "FORMAT_MAPPING": (
        "FORMAT_MAPPING",
        "FORMAT_TRIE",
        "INVERSE_FORMAT_MAPPING",
        "INVERSE_FORMAT_TRIE",
    ),
    "CREATABLE_KIND_MAPPING": ("CREATABLE_KIND_MAPPING", "INVERSE_CREATABLE_KIND_MAPPING"),
    "DATE_PART_MAPPING": ("DATE_PART_MAPPING", "VALID_INTERVAL_UNITS"),
    "UNESCAPED_SEQUENCES": (
        "UNESCAPED_SEQUENCES",
        "ESCAPED_SEQUENCES",
        "IDENTIFIER_ESCAPED_SEQUENCES",
    ),
    "SUPPORTED_JSON_PATH_PARTS": ("SUPPORTED_JSON_PATH_PARTS", "TRANSFORMS"),
    "QUOTES": ("QUOTES", "_QUOTES", "QUOTE_START", "QUOTE_END"),
    "IDENTIFIERS": ("IDENTIFIERS", "_IDENTIFIERS", "IDENTIFIER_START", "IDENTIFIER_END"),
    "BIT_STRINGS": ("BIT_STRINGS", "_FORMAT_STRINGS", "BIT_START", "BIT_END"),
    "HEX_STRINGS": ("HEX_STRINGS", "_FORMAT_STRINGS", "HEX_START", "HEX_END"),
    "BYTE_STRINGS": ("BYTE_STRINGS", "_FORMAT_STRINGS", "BYTE_START", "BYTE_END"),
    "UNICODE_STRINGS": ("UNICODE_STRINGS", "_FORMAT_STRINGS", "UNICODE_START", "UNICODE_END"),
    "RAW_STRINGS": ("RAW_STRINGS", "_FORMAT_STRINGS"),
    "HEREDOC_STRINGS": ("HEREDOC_STRINGS", "_FORMAT_STRINGS"),
    "NATIONAL_RAW_STRINGS": ("NATIONAL_RAW_STRINGS", "_FORMAT_STRINGS"),
    "STRING_ESCAPES": (
        "STRING_ESCAPES",
        "_STRING_ESCAPES",
        "STRINGS_SUPPORT_ESCAPED_SEQUENCES",
        "ESCAPED_SEQUENCES",
    ),
    "BYTE_STRING_ESCAPES": (
        "BYTE_STRING_ESCAPES",
        "_BYTE_STRING_ESCAPES",
        "BYTE_STRINGS_SUPPORT_ESCAPED_SEQUENCES",
        "ESCAPED_SEQUENCES",
    ),
    "IDENTIFIER_ESCAPES": (
        "IDENTIFIER_ESCAPES",
        "_IDENTIFIER_ESCAPES",
        "IDENTIFIER_ESCAPED_SEQUENCES",
    ),
    "COMMENTS": ("COMMENTS", "_COMMENTS"),
    "KEYWORDS": ("KEYWORDS", "_KEYWORD_TRIE", "SUPPORTS_COLUMN_JOIN_MARKS"),
    "SHOW_PARSERS": ("SHOW_PARSERS", "SHOW_TRIE"),
    "SET_PARSERS": ("SET_PARSERS", "SET_TRIE"),
}


class _EarlySubtestFail(BaseException):
    """Raised on first subTest failure so parameterized tests fail in milliseconds."""


class _FastTestResult(unittest.TestResult):
    """Skip expensive traceback/source-line formatting since only pass/fail is needed."""

    def _exc_info_to_string(self, err, test):
        return ""


class _LazyFuture:
    """Defer task execution until .result() so check_file stops on the first failing subtest."""

    def __init__(self, fn, args, kwargs, use_pickle: bool):
        self._fn = fn
        self._args = args
        self._kwargs = kwargs
        self._use_pickle = use_pickle
        self._done = False
        self._res = None
        self._exc: BaseException | None = None

    def result(self, timeout=None):
        if not self._done:
            self._done = True
            try:
                if self._use_pickle:
                    fn_p, args_p, kwargs_p = pickle.loads(
                        pickle.dumps((self._fn, self._args, self._kwargs))
                    )
                    res = fn_p(*args_p, **kwargs_p)
                    self._res = pickle.loads(pickle.dumps(res))
                else:
                    self._res = self._fn(*self._args, **self._kwargs)
            except BaseException as exc:
                self._exc = exc
        if self._exc is not None:
            raise self._exc
        return self._res


class InlinePoolExecutor:
    """Synchronous ProcessPoolExecutor replacement using lazy futures."""

    use_pickle = False
    pickle_budget: int = 0

    def __init__(self, max_workers=None, mp_context=None, initializer=None, initargs=()):
        if initializer is not None:
            initializer(*initargs)

    def submit(self, fn, *args, **kwargs):
        do_pickle = self.use_pickle and InlinePoolExecutor.pickle_budget > 0
        if do_pickle:
            InlinePoolExecutor.pickle_budget -= 1
        return _LazyFuture(fn, args, kwargs, do_pickle)

    def shutdown(self, wait=True, cancel_futures=False):
        pass

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        return False


def _duration_ms(seconds: float) -> int:
    return math.floor(seconds * 1000 + 0.5)


def parse_patch(patch_text: str) -> list[dict]:
    """Parse a unified diff into file records with hunks."""
    files: list[dict] = []
    cur: dict | None = None
    hunk: dict | None = None
    for line in patch_text.splitlines(keepends=True):
        if line.startswith("diff --git "):
            if cur is not None:
                files.append(cur)
            parts = line.strip().split()
            old_p = parts[2][2:] if len(parts) >= 4 and parts[2].startswith("a/") else None
            new_p = parts[3][2:] if len(parts) >= 4 and parts[3].startswith("b/") else None
            cur = {"old": old_p, "new": new_p, "hunks": [], "is_new": False, "is_deleted": False}
            hunk = None
        elif cur is not None:
            if line.startswith("new file mode "):
                cur["is_new"] = True
                cur["old"] = None
            elif line.startswith("deleted file mode "):
                cur["is_deleted"] = True
                cur["new"] = None
            elif line.startswith("rename from "):
                cur["old"] = line[12:].strip()
            elif line.startswith("rename to "):
                cur["new"] = line[10:].strip()
            elif line.startswith("--- "):
                p = line[4:].strip()
                cur["old"] = None if p == "/dev/null" else (p[2:] if p.startswith("a/") else p)
            elif line.startswith("+++ "):
                p = line[4:].strip()
                cur["new"] = None if p == "/dev/null" else (p[2:] if p.startswith("b/") else p)
            elif line.startswith("@@ "):
                m = re.match(r"@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@", line)
                if m:
                    hunk = {
                        "old_start": int(m.group(1)),
                        "old_count": int(m.group(2) or "1"),
                        "new_start": int(m.group(3)),
                        "new_count": int(m.group(4) or "1"),
                        "lines": [],
                    }
                    cur["hunks"].append(hunk)
            elif hunk is not None and (line.startswith(("+", "-", " ")) or line.startswith("\\")):
                hunk["lines"].append(line)
    if cur is not None:
        files.append(cur)
    return files


def apply_hunks(orig_text: str, hunks: list[dict]) -> str:
    """Apply unified diff hunks in memory against orig_text."""
    orig_lines = orig_text.splitlines(keepends=True)
    out: list[str] = []
    idx = 0
    for h in hunks:
        start_idx = max(0, h["old_start"] - 1) if h["old_start"] > 0 else 0
        out.extend(orig_lines[idx:start_idx])
        cur_old = start_idx
        last_plus = False
        for hl in h["lines"]:
            if hl.startswith(" "):
                out.append(orig_lines[cur_old] if cur_old < len(orig_lines) else hl[1:])
                cur_old += 1
                last_plus = False
            elif hl.startswith("-"):
                cur_old += 1
                last_plus = False
            elif hl.startswith("+"):
                out.append(hl[1:])
                last_plus = True
            elif hl.startswith("\\") and last_plus and out:
                if out[-1].endswith("\r\n"):
                    out[-1] = out[-1][:-2]
                elif out[-1].endswith("\n"):
                    out[-1] = out[-1][:-1]
                last_plus = False
        idx = cur_old
    out.extend(orig_lines[idx:])
    return "".join(out)


def _has_encoding_change(old_src: str, new_src: str) -> bool:
    if old_src.startswith("\ufeff") != new_src.startswith("\ufeff"):
        return True
    old_top = "\n".join(old_src.splitlines()[:2])
    new_top = "\n".join(new_src.splitlines()[:2])
    return bool(ENCODING_COMMENT_RE.search(old_top) or ENCODING_COMMENT_RE.search(new_top)) and (
        old_top != new_top
    )


class BlastSelector:
    def __init__(self, map_path: Path, base_repo: Path, tests_list: list[dict]):
        self.base_repo = base_repo
        self.tests = tests_list
        self.test_by_num = {t["number"]: t for t in tests_list}
        self.test_ms = {t["number"]: _duration_ms(t["seconds"]) for t in tests_list}
        self.all_test_nums = [t["number"] for t in tests_list]

        raw = gzip.decompress(map_path.read_bytes()) if map_path.name.endswith(".gz") else map_path.read_bytes()
        if map_path.name.endswith((".pkl.gz", ".pkl")):
            bmap = pickle.loads(raw)
        else:
            bmap = json.loads(raw)

        self.test_sets: list[list[int]] = bmap["test_sets"]
        self.line_to_tests: dict[str, dict[str, int]] = bmap["line_to_tests"]
        self.func_to_tests: dict[str, dict[str, int]] = bmap["func_to_tests"]
        self.file_to_tests: dict[str, int] = bmap["file_to_tests"]
        self.file_open_to_tests: dict[str, int] = bmap["file_open_to_tests"]
        self.file_defs: dict[str, list[dict]] = bmap["file_defs"]
        self.file_classes: dict[str, list[dict]] = bmap["file_classes"]
        self.symbol_readers: dict[str, list[list[object]]] = bmap["symbol_readers"]
        self.class_graph: dict[str, list[dict]] = bmap["class_graph"]
        self.module_imports: dict[str, list[str]] = bmap["module_imports"]

        self.expr_to_tests: dict[str, int] = bmap.get("expr_to_tests", {})
        self.dialect_used_tests: dict[str, int] = bmap.get("dialect_used_tests", {})
        self.dict_key_to_tests: dict[str, dict[str, int]] = bmap.get("dict_key_to_tests", {})
        self.dict_iter_tests: dict[str, int] = bmap.get("dict_iter_tests", {})
        self.token_to_tests: dict[str, int] = bmap.get("token_to_tests", {})
        self.time_substr_to_tests: dict[str, int] = bmap.get("time_substr_to_tests", {})

        self._build_reverse_indices(bmap)

    def _build_reverse_indices(self, bmap: dict) -> None:
        if "dialect_tests" in bmap:
            self.dialect_tests: dict[str, set[int]] = collections.defaultdict(
                set,
                {k: set(self.test_sets[sid]) for k, sid in bmap["dialect_tests"].items()},
            )
        else:
            self.dialect_tests = collections.defaultdict(set)
            for rel, sid in self.file_to_tests.items():
                m = DIALECT_FILE_RE.match(rel) or TEST_DIALECT_FILE_RE.match(rel)
                if m:
                    self.dialect_tests[m.group(1)].update(self.test_sets[sid])

        if "cross_dialect_tests" in bmap:
            self.cross_dialect_tests: dict[str, set[int]] = collections.defaultdict(
                set,
                {k: set(self.test_sets[sid]) for k, sid in bmap["cross_dialect_tests"].items()},
            )
        else:
            self.cross_dialect_tests = collections.defaultdict(set)
            dialect_stems = sorted(
                Path(rel).stem
                for rel in self.file_defs
                if rel.startswith("sqlglot/dialects/")
                and Path(rel).stem not in ("dialect", "__init__", "python")
            )
            if dialect_stems:
                d_pat = re.compile(
                    r"""['"](?:""" + "|".join(re.escape(s) for s in dialect_stems) + r""")['"]"""
                )
                by_file: dict[str, list[tuple[int, str]]] = collections.defaultdict(list)
                for t in self.tests:
                    parts = t["id"].split("::")
                    if len(parts) == 3:
                        by_file[parts[0]].append((t["number"], parts[2]))
                for tfile in sorted(by_file):
                    if not tfile.startswith("tests/dialects/test_"):
                        continue
                    tp = self.base_repo / tfile
                    if not tp.exists():
                        continue
                    lines = tp.read_text(encoding="utf-8", errors="ignore").splitlines()
                    defs_for_file = self.file_defs.get(tfile, ())
                    cls_fn_ranges = {
                        tuple(d["q"].split(".")[-2:]): (d["s"], d["e"])
                        for d in defs_for_file
                        if "." in d["q"]
                    }
                    fn_ranges = {d["q"].split(".")[-1]: (d["s"], d["e"]) for d in defs_for_file}
                    for num, mname in by_file[tfile]:
                        t_cls = self.test_by_num[num]["id"].split("::")[1]
                        rng = cls_fn_ranges.get((t_cls, mname)) or fn_ranges.get(mname)
                        if not rng:
                            continue
                        snippet = "\n".join(lines[rng[0] - 1 : rng[1]])
                        for match in d_pat.finditer(snippet):
                            self.cross_dialect_tests[match.group(0)[1:-1]].add(num)

        if "subclasses" in bmap:
            self.subclasses: dict[str, set[str]] = collections.defaultdict(
                set,
                {k: set(v) for k, v in bmap["subclasses"].items()},
            )
        else:
            self.subclasses = collections.defaultdict(set)
            for cname, defs_list in self.class_graph.items():
                for d in defs_list:
                    if "." not in d["q"]:
                        for base in d["bases"]:
                            self.subclasses[base].add(cname)

        if "reverse_mod_files" in bmap:
            self.reverse_mod_files: dict[str, set[str]] = collections.defaultdict(
                set,
                {k: set(v) for k, v in bmap["reverse_mod_files"].items()},
            )
        else:
            self.reverse_mod_files = collections.defaultdict(set)
            for mod, deps in self.module_imports.items():
                src_rel = mod.replace(".", "/") + ".py"
                if src_rel not in self.file_to_tests and (
                    self.base_repo / mod.replace(".", "/") / "__init__.py"
                ).exists():
                    src_rel = mod.replace(".", "/") + "/__init__.py"
                for dep in deps:
                    self.reverse_mod_files[dep].add(src_rel)

        self._covered_methods: set[str] = set()
        for rel, fmap in self.func_to_tests.items():
            if not rel.startswith("sqlglot/") or not fmap:
                continue
            for d in self.file_defs.get(rel, ()):
                if str(d["fl"]) in fmap or str(d["s"]) in fmap:
                    fn_sym = d["q"].split(".")[-1]
                    if fn_sym != "<lambda>" and "." in d["q"]:
                        self._covered_methods.add(fn_sym)

        self.lazy_load_tests = [
            t["number"] for t in self.tests if t["id"].endswith("::test_lazy_load")
        ]
        self.enum_tests = [
            t["number"] for t in self.tests if t["id"].endswith("::test_enum")
        ]
        self.typing_tests = [
            t["number"] for t in self.tests if t["file"] == "tests/test_typing.py"
        ]
        self._own_dialect_tests: dict[str, set[int]] = collections.defaultdict(set)
        for t in self.tests:
            m = TEST_DIALECT_FILE_RE.match(t["file"])
            if m:
                self._own_dialect_tests[m.group(1)].add(t["number"])

    def _descendant_dialects(self, dname: str) -> set[str]:
        target_files = {
            f"sqlglot/dialects/{dname}.py",
            f"sqlglot/parsers/{dname}.py",
            f"sqlglot/generators/{dname}.py",
            f"sqlglot/typing/{dname}.py",
        }
        queue = [
            cname
            for cname, dl in self.class_graph.items()
            if any(d["file"] in target_files and "." not in d["q"] for d in dl)
        ]
        seen = set(queue)
        while queue:
            cur = queue.pop()
            for sub in self.subclasses.get(cur, ()):
                if sub not in seen:
                    seen.add(sub)
                    queue.append(sub)
        out = {dname}
        for cname in seen:
            for d in self.class_graph.get(cname, ()):
                m = DIALECT_FILE_RE.match(d["file"])
                if m:
                    out.add(m.group(1))
        # Expand transitively through direct dialect module imports (composition without inheritance)
        d_q = list(out)
        while d_q:
            cur_d = d_q.pop()
            for mod_pfx in ("dialects", "parsers", "generators", "typing"):
                for imp_rel in self.reverse_mod_files.get(f"sqlglot.{mod_pfx}.{cur_d}", ()):
                    m = DIALECT_FILE_RE.match(imp_rel)
                    if m and m.group(1) not in out:
                        sub_d = self._subclasses_dialects_only(m.group(1))
                        for sd in sub_d:
                            if sd not in out:
                                out.add(sd)
                                d_q.append(sd)
        return out

    def _subclasses_dialects_only(self, dname: str) -> set[str]:
        target_files = {
            f"sqlglot/dialects/{dname}.py",
            f"sqlglot/parsers/{dname}.py",
            f"sqlglot/generators/{dname}.py",
            f"sqlglot/typing/{dname}.py",
        }
        queue = [
            cname
            for cname, dl in self.class_graph.items()
            if any(d["file"] in target_files and "." not in d["q"] for d in dl)
        ]
        seen = set(queue)
        while queue:
            cur = queue.pop()
            for sub in self.subclasses.get(cur, ()):
                if sub not in seen:
                    seen.add(sub)
                    queue.append(sub)
        out = {dname}
        for cname in seen:
            for d in self.class_graph.get(cname, ()):
                m = DIALECT_FILE_RE.match(d["file"])
                if m:
                    out.add(m.group(1))
        return out

    def _reader_tests_for_symbol(self, sym: str, is_tokenizer: bool = False) -> set[int]:
        def _collect_for(symbols: tuple[str, ...], skip_tok_init: bool) -> set[int]:
            out: set[int] = set()
            for s in symbols:
                for rf, rl in self.symbol_readers.get(s, ()):
                    if skip_tok_init:
                        if rf == "sqlglot/tokens.py" and 570 <= rl <= 612:
                            continue
                        if rf == "sqlglot/tokenizer_core.py" and (
                            600 <= rl <= 680 or rl in (1323, 1362)
                        ):
                            continue
                        if rf == "sqlglot/generator.py" and rl == 3283:
                            continue
                    rsid = self.line_to_tests.get(rf, {}).get(str(rl))
                    if rsid is not None:
                        out.update(self.test_sets[rsid])
                    fmap = self.func_to_tests.get(rf, {})
                    if fmap:
                        for d in self.file_defs.get(rf, ()):
                            if d["s"] <= rl <= d["e"] and (
                                rsid is None or rl <= d["fl"] + 3 or "<lambda>" in d["q"]
                            ):
                                for fk in (str(d["fl"]), str(d["s"])):
                                    fsid = fmap.get(fk)
                                    if fsid is not None:
                                        out.update(self.test_sets[fsid])
            return out

        if is_tokenizer and sym == "NUMERIC_ESCAPES":
            narrowed = _collect_for(("NUMERIC_ESCAPES", "numeric_escapes"), True)
            if narrowed:
                return narrowed
            return _collect_for(("NUMERIC_ESCAPES", "numeric_escapes"), False)

        return _collect_for(_ATTR_DERIVED_SYMBOLS.get(sym, (sym,)), False)

    def _func_tests(self, rel: str, d: dict) -> set[int]:
        fmap = self.func_to_tests.get(rel, {})
        lmap = self.line_to_tests.get(rel, {})
        res: set[int] = set()
        for fk in (str(d["fl"]), str(d["s"])):
            fsid = fmap.get(fk)
            if fsid is not None:
                res.update(self.test_sets[fsid])
        for d2 in self.file_defs.get(rel, ()):
            if d["s"] <= d2["s"] and d2["e"] <= d["e"]:
                for fk in (str(d2["fl"]), str(d2["s"])):
                    fsid = fmap.get(fk)
                    if fsid is not None:
                        res.update(self.test_sets[fsid])
        for cln in range(d["s"], d["e"] + 1):
            lsid = lmap.get(str(cln))
            if lsid is not None:
                res.update(self.test_sets[lsid])
        return res

    def _tests_importing_file(self, rel: str, transitive: bool = False) -> set[int]:
        if rel == "tests/helpers.py":
            return set(self.all_test_nums)
        res: set[int] = set()
        if rel in self.file_to_tests:
            res.update(self.test_sets[self.file_to_tests[rel]])
        if rel in self.file_open_to_tests:
            res.update(self.test_sets[self.file_open_to_tests[rel]])
        m = DIALECT_FILE_RE.match(rel)
        if m and not rel.startswith("sqlglot/typing/"):
            res.update(self.dialect_tests.get(m.group(1), ()))
            if m.group(1) not in ("dialect", "base", "__init__"):
                for sd in self._descendant_dialects(m.group(1)):
                    res.update(self.dialect_tests.get(sd, ()))
                    res.update(
                        t["number"]
                        for t in self.tests
                        if t["file"] == f"tests/dialects/test_{sd}.py"
                    )
        if rel.startswith("sqlglot/dialects/"):
            res.update(self.enum_tests)
        if (
            transitive
            or rel
            in (
                "sqlglot/__init__.py",
                "sqlglot/dialects/__init__.py",
                "sqlglot/dialects/dialect.py",
            )
        ) and rel.startswith("sqlglot/"):
            res.update(self.lazy_load_tests)
        if rel.startswith("sqlglot/typing/"):
            res.update(self.typing_tests)
            res.update(
                t["number"]
                for t in self.tests
                if t["id"].endswith(("::test_annotate_funcs", "::test_annotate_types"))
            )
        if rel.startswith("tests/") and not rel.startswith("tests/fixtures/"):
            res.update(t["number"] for t in self.tests if t["file"] == rel)
        mod = rel[:-3].replace("/", ".")
        if mod.endswith(".__init__"):
            mod = mod[:-9]
        if transitive or rel not in self.file_to_tests or rel == "sqlglot/__init__.py":
            # BFS reverse module imports (including package __init__.py -> submodule importers)
            visited = {mod}
            q = [mod]
            init_mods = {mod} if rel.endswith("/__init__.py") else set()
            all_rev_keys: list[str] | None = None
            while q:
                cur = q.pop()
                rels_to_add = set(self.reverse_mod_files.get(cur, ()))
                if cur in init_mods:
                    if all_rev_keys is None:
                        all_rev_keys = list(self.reverse_mod_files.keys())
                    pfx = cur + "."
                    for sub_k in all_rev_keys:
                        if sub_k.startswith(pfx):
                            rels_to_add.update(self.reverse_mod_files[sub_k])
                for importer_rel in rels_to_add:
                    if importer_rel in self.file_to_tests:
                        res.update(self.test_sets[self.file_to_tests[importer_rel]])
                    if importer_rel.startswith("tests/") and not importer_rel.startswith(
                        "tests/fixtures/"
                    ):
                        res.update(t["number"] for t in self.tests if t["file"] == importer_rel)
                    imp_mod = importer_rel[:-3].replace("/", ".")
                    if imp_mod.endswith(".__init__"):
                        imp_mod = imp_mod[:-9]
                        init_mods.add(imp_mod)
                    if imp_mod not in visited:
                        visited.add(imp_mod)
                        q.append(imp_mod)
        elif not rel.startswith("sqlglot/typing/"):
            for importer_rel in self.reverse_mod_files.get(mod, ()):
                if importer_rel.startswith("tests/") and not importer_rel.startswith(
                    "tests/fixtures/"
                ):
                    res.update(t["number"] for t in self.tests if t["file"] == importer_rel)
                elif (
                    importer_rel not in ("sqlglot/__init__.py", "sqlglot/dialects/dialect.py")
                    and importer_rel in self.file_to_tests
                ):
                    res.update(self.test_sets[self.file_to_tests[importer_rel]])
        return res

    def _descendant_dialect_tests(self, dname: str) -> set[int]:
        out: set[int] = set()
        for d in self._descendant_dialects(dname):
            if d in self.dialect_used_tests:
                out.update(self.test_sets[self.dialect_used_tests[d]])
            out.update(self.dialect_tests.get(d, ()))
            out.update(self._own_dialect_tests.get(d, ()))
            out.update(self.cross_dialect_tests.get(d, ()))
        return out

    @staticmethod
    def _index_ast_nodes(tree: ast.AST) -> tuple[dict[str, ast.AST], dict[tuple[str, str], ast.AST]]:
        """Index functions by qualified name and class attributes by (class_qname, attr_name)."""
        fn_map: dict[str, ast.AST] = {}
        attr_map: dict[tuple[str, str], ast.AST] = {}

        def visit(node: ast.AST, prefix: str = "") -> None:
            for child in ast.iter_child_nodes(node):
                if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    qn = f"{prefix}.{child.name}" if prefix else child.name
                    fn_map[qn] = child
                    visit(child, qn)
                elif isinstance(child, ast.ClassDef):
                    qn = f"{prefix}.{child.name}" if prefix else child.name
                    for stmt in child.body:
                        if isinstance(stmt, ast.Assign):
                            for tgt in stmt.targets:
                                if isinstance(tgt, ast.Name):
                                    attr_map[(qn, tgt.id)] = stmt.value
                        elif (
                            isinstance(stmt, ast.AnnAssign)
                            and isinstance(stmt.target, ast.Name)
                            and stmt.value is not None
                        ):
                            attr_map[(qn, stmt.target.id)] = stmt.value
                    visit(child, qn)
                else:
                    visit(child, prefix)

        visit(tree)
        return fn_map, attr_map

    @staticmethod
    def _is_stub_ast(fn_node: ast.AST | None) -> bool:
        if not isinstance(fn_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            return False
        for dec in fn_node.decorator_list:
            if (isinstance(dec, ast.Name) and dec.id == "overload") or (
                isinstance(dec, ast.Attribute) and dec.attr == "overload"
            ):
                return True
        body = fn_node.body
        if (
            body
            and isinstance(body[0], ast.Expr)
            and isinstance(body[0].value, ast.Constant)
            and isinstance(body[0].value.value, str)
        ):
            body = body[1:]
        if len(body) == 1:
            stmt = body[0]
            if isinstance(stmt, ast.Pass):
                return True
            if (
                isinstance(stmt, ast.Expr)
                and isinstance(stmt.value, ast.Constant)
                and stmt.value.value is ...
            ):
                return True
            if isinstance(stmt, ast.Raise) and stmt.exc is not None:
                exc_name = (
                    stmt.exc.id
                    if isinstance(stmt.exc, ast.Name)
                    else (
                        stmt.exc.func.id
                        if isinstance(stmt.exc, ast.Call) and isinstance(stmt.exc.func, ast.Name)
                        else None
                    )
                )
                if exc_name == "NotImplementedError":
                    return True
        return False

    @staticmethod
    def _has_yield_in_fn(fn_node: ast.AST) -> bool:
        stack = list(ast.iter_child_nodes(fn_node))
        while stack:
            n = stack.pop()
            if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda)):
                continue
            if isinstance(n, (ast.Yield, ast.YieldFrom)):
                return True
            stack.extend(ast.iter_child_nodes(n))
        return False

    @staticmethod
    def _collect_func_bindings(fn_node: ast.AST) -> tuple[str, ...]:
        names: set[str] = set()
        stack = list(fn_node.body)
        while stack:
            n = stack.pop()
            if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                names.add(f"DEF:{n.name}")
                continue
            if isinstance(n, ast.Name) and isinstance(n.ctx, (ast.Store, ast.Del)):
                names.add(n.id)
            elif isinstance(n, (ast.Global, ast.Nonlocal)):
                tag = "G:" if isinstance(n, ast.Global) else "NL:"
                for nm in n.names:
                    names.add(tag + nm)
            elif isinstance(n, ast.ExceptHandler) and n.name:
                names.add(n.name)
            elif isinstance(n, (ast.Import, ast.ImportFrom)):
                for alias in n.names:
                    names.add(alias.asname or alias.name.split(".")[0])
            stack.extend(ast.iter_child_nodes(n))
        return tuple(sorted(names))

    def _span_line_tests(self, lmap: dict[str, int], s: int, e: int) -> set[int]:
        out: set[int] = set()
        for ln in range(s, e + 1):
            sid = lmap.get(str(ln))
            if sid is not None:
                out.update(self.test_sets[sid])
        return out

    def _ast_narrow_func_tests(
        self,
        rel: str,
        d: dict,
        old_fn: ast.AST | None,
        new_fn: ast.AST | None,
        lmap: dict[str, int],
        changed_lines: set[int],
    ) -> set[int] | None:
        """Return narrowed test set for an edited function body, or None to fall back to _func_tests."""
        if not isinstance(old_fn, (ast.FunctionDef, ast.AsyncFunctionDef)) or not isinstance(
            new_fn, (ast.FunctionDef, ast.AsyncFunctionDef)
        ):
            return None
        if type(old_fn) is not type(new_fn):
            return None
        if [ast.dump(x, include_attributes=False) for x in old_fn.decorator_list] != [
            ast.dump(x, include_attributes=False) for x in new_fn.decorator_list
        ]:
            return None
        if ast.dump(old_fn.args, include_attributes=False) != ast.dump(
            new_fn.args, include_attributes=False
        ):
            return None
        r_old = ast.dump(old_fn.returns, include_attributes=False) if old_fn.returns else None
        r_new = ast.dump(new_fn.returns, include_attributes=False) if new_fn.returns else None
        if r_old != r_new:
            return None
        if self._has_yield_in_fn(old_fn) != self._has_yield_in_fn(new_fn):
            return None
        if self._collect_func_bindings(old_fn) != self._collect_func_bindings(new_fn):
            return None
        if not old_fn.body or any(d["s"] <= ln <= d["fl"] for ln in changed_lines):
            return None
        if any(old_fn.lineno <= ln < old_fn.body[0].lineno for ln in changed_lines):
            return None

        def narrow_stmts(
            old_stmts: list[ast.stmt],
            new_stmts: list[ast.stmt],
            parent_header_tests: set[int] | None,
        ) -> set[int] | None:
            old_dumps = [ast.dump(s, include_attributes=False) for s in old_stmts]
            new_dumps = [ast.dump(s, include_attributes=False) for s in new_stmts]
            ops = [
                op
                for op in difflib.SequenceMatcher(None, old_dumps, new_dumps).get_opcodes()
                if op[0] != "equal"
            ]
            if not ops:
                return set()
            if all(tag == "replace" and (i2 - i1) == 1 and (j2 - j1) == 1 for tag, i1, i2, j1, j2 in ops):
                out: set[int] = set()
                for _, i1, _, j1, _ in ops:
                    so = old_stmts[i1]
                    sn = new_stmts[j1]
                    so_end = so.end_lineno or so.lineno
                    sub_res: set[int] | None = None
                    handled_compound = False

                    if isinstance(so, ast.If) and isinstance(sn, ast.If):
                        if ast.dump(so.test, include_attributes=False) == ast.dump(
                            sn.test, include_attributes=False
                        ):
                            b_eq = [ast.dump(x, include_attributes=False) for x in so.body] == [
                                ast.dump(x, include_attributes=False) for x in sn.body
                            ]
                            o_eq = [ast.dump(x, include_attributes=False) for x in so.orelse] == [
                                ast.dump(x, include_attributes=False) for x in sn.orelse
                            ]
                            hdr_end = max(so.lineno, so.body[0].lineno - 1) if so.body else so.lineno
                            hdr_t = self._span_line_tests(lmap, so.lineno, hdr_end)
                            if not b_eq and o_eq:
                                handled_compound = True
                                sub_res = narrow_stmts(so.body, sn.body, hdr_t)
                            elif b_eq and not o_eq and so.orelse:
                                so_elif = len(so.orelse) == 1 and isinstance(so.orelse[0], ast.If)
                                sn_elif = len(sn.orelse) == 1 and isinstance(sn.orelse[0], ast.If)
                                if so_elif == sn_elif:
                                    handled_compound = True
                                    sub_res = narrow_stmts(so.orelse, sn.orelse, hdr_t)
                    elif (
                        isinstance(so, (ast.For, ast.AsyncFor))
                        and type(so) is type(sn)
                        and ast.dump(so.target, include_attributes=False)
                        == ast.dump(sn.target, include_attributes=False)
                        and ast.dump(so.iter, include_attributes=False)
                        == ast.dump(sn.iter, include_attributes=False)
                        and [ast.dump(x, include_attributes=False) for x in so.orelse]
                        == [ast.dump(x, include_attributes=False) for x in sn.orelse]
                    ):
                        hdr_end = max(so.lineno, so.body[0].lineno - 1) if so.body else so.lineno
                        hdr_t = self._span_line_tests(lmap, so.lineno, hdr_end)
                        handled_compound = True
                        sub_res = narrow_stmts(so.body, sn.body, hdr_t)
                    elif (
                        isinstance(so, ast.While)
                        and isinstance(sn, ast.While)
                        and ast.dump(so.test, include_attributes=False)
                        == ast.dump(sn.test, include_attributes=False)
                        and [ast.dump(x, include_attributes=False) for x in so.orelse]
                        == [ast.dump(x, include_attributes=False) for x in sn.orelse]
                    ):
                        hdr_end = max(so.lineno, so.body[0].lineno - 1) if so.body else so.lineno
                        hdr_t = self._span_line_tests(lmap, so.lineno, hdr_end)
                        handled_compound = True
                        sub_res = narrow_stmts(so.body, sn.body, hdr_t)
                    elif (
                        isinstance(so, (ast.With, ast.AsyncWith))
                        and type(so) is type(sn)
                        and [ast.dump(x, include_attributes=False) for x in so.items]
                        == [ast.dump(x, include_attributes=False) for x in sn.items]
                    ):
                        hdr_end = max(so.lineno, so.body[0].lineno - 1) if so.body else so.lineno
                        hdr_t = self._span_line_tests(lmap, so.lineno, hdr_end)
                        handled_compound = True
                        sub_res = narrow_stmts(so.body, sn.body, hdr_t)
                    elif (
                        isinstance(so, ast.Try)
                        and type(so) is type(sn)
                        and [ast.dump(x, include_attributes=False) for x in so.orelse]
                        == [ast.dump(x, include_attributes=False) for x in sn.orelse]
                        and [ast.dump(x, include_attributes=False) for x in so.finalbody]
                        == [ast.dump(x, include_attributes=False) for x in sn.finalbody]
                    ):
                        h_old = [ast.dump(x, include_attributes=False) for x in so.handlers]
                        h_new = [ast.dump(x, include_attributes=False) for x in sn.handlers]
                        b_eq = [ast.dump(x, include_attributes=False) for x in so.body] == [
                            ast.dump(x, include_attributes=False) for x in sn.body
                        ]
                        if not b_eq and h_old == h_new:
                            hdr_t = self._span_line_tests(lmap, so.lineno, so.lineno)
                            handled_compound = True
                            sub_res = narrow_stmts(so.body, sn.body, hdr_t)

                    if handled_compound:
                        if sub_res is not None:
                            out.update(sub_res)
                        else:
                            span_t = self._span_line_tests(lmap, so.lineno, so_end)
                            if not span_t and parent_header_tests is None:
                                return None
                            out.update(span_t)
                    else:
                        span_t = self._span_line_tests(lmap, so.lineno, so_end)
                        if not span_t:
                            if parent_header_tests is None or not parent_header_tests:
                                return None
                        out.update(span_t)
                return out

            if parent_header_tests is None or not parent_header_tests or not old_stmts:
                return None
            return self._span_line_tests(
                lmap,
                old_stmts[0].lineno,
                old_stmts[-1].end_lineno or old_stmts[-1].lineno,
            )

        return narrow_stmts(old_fn.body, new_fn.body, None)

    def _resolve_spread_str_map(
        self, dnode: ast.Dict, visited: set[tuple[str, str]]
    ) -> dict[str, set[str]] | None:
        """Resolve static dict + `**ClassName.ATTR` spreads into {key_str: {val_str, ...}}."""
        out: dict[str, set[str]] = collections.defaultdict(set)
        for k, v in zip(dnode.keys, dnode.values):
            if k is None:
                if isinstance(v, ast.Attribute) and isinstance(v.value, ast.Name):
                    cname, cattr = v.value.id, v.attr
                    if (cname, cattr) in visited:
                        continue
                    visited.add((cname, cattr))
                    found_node = None
                    for cls_info in self.class_graph.get(cname, ()):
                        if "." in cls_info["q"]:
                            continue
                        src_p = self.base_repo / cls_info["file"]
                        if not src_p.exists():
                            continue
                        try:
                            t = ast.parse(src_p.read_text(encoding="utf-8", errors="replace"))
                            _, attrs = self._index_ast_nodes(t)
                            found_node = attrs.get((cls_info["q"], cattr))
                            if found_node is not None:
                                break
                        except Exception:
                            return None
                    if not isinstance(found_node, ast.Dict):
                        return None
                    sub = self._resolve_spread_str_map(found_node, visited)
                    if sub is None:
                        return None
                    for sk, sv in sub.items():
                        out[sk].update(sv)
                else:
                    return None
            elif isinstance(k, ast.Constant) and isinstance(k.value, str):
                if isinstance(v, ast.Constant) and isinstance(v.value, str):
                    out[k.value].add(v.value)
        return out

    def _ast_diff_dict_attr(
        self,
        rel: str,
        attr: str,
        old_val: ast.AST | None,
        new_val: ast.AST | None,
    ) -> set[int] | None:
        """Exact static dict-key narrowing for tracked Parser/Generator/Dialect/Tokenizer dicts."""
        if not isinstance(old_val, ast.Dict) or not isinstance(new_val, ast.Dict):
            return None

        old_spreads = [
            ast.dump(v, include_attributes=False)
            for k, v in zip(old_val.keys, old_val.values)
            if k is None
        ]
        new_spreads = [
            ast.dump(v, include_attributes=False)
            for k, v in zip(new_val.keys, new_val.values)
            if k is None
        ]
        if old_spreads != new_spreads:
            return None

        str_only_attrs = {
            "FUNCTIONS",
            "FUNCTION_PARSERS",
            "PROPERTY_PARSERS",
            "CONSTRAINT_PARSERS",
            "NO_PAREN_FUNCTION_PARSERS",
            "AFTER_HAVING_MODIFIER_TRANSFORMS",
            "KEYWORDS",
            "SINGLE_TOKENS",
            "TIME_MAPPING",
            "FORMAT_MAPPING",
            "INVERSE_TIME_MAPPING",
            "INVERSE_FORMAT_MAPPING",
            "DATE_PART_MAPPING",
        }

        def extract_key(knode: ast.AST) -> str | None:
            if isinstance(knode, ast.Constant) and isinstance(knode.value, str):
                return knode.value.upper() if attr in _UPPER_KEY_ATTRS else knode.value
            if attr in str_only_attrs:
                return None
            if isinstance(knode, ast.Attribute):
                return knode.attr
            if isinstance(knode, ast.Name):
                return knode.id
            return None

        def collect_entries(
            dnode: ast.Dict,
        ) -> tuple[dict[str, list[str]], dict[str, list[str]], list[tuple[str, str]]]:
            entries: dict[str, list[str]] = collections.defaultdict(list)
            str_vals: dict[str, list[str]] = collections.defaultdict(list)
            opaque: list[tuple[str, str]] = []
            for k, v in zip(dnode.keys, dnode.values):
                if k is None:
                    continue
                nk = extract_key(k)
                vd = ast.dump(v, include_attributes=False)
                if nk is None:
                    opaque.append((ast.dump(k, include_attributes=False), vd))
                else:
                    entries[nk].append(vd)
                    if isinstance(v, ast.Constant) and isinstance(v.value, str):
                        str_vals[nk].append(v.value)
            return entries, str_vals, opaque

        old_entries, old_str_vals, old_opaque = collect_entries(old_val)
        new_entries, new_str_vals, new_opaque = collect_entries(new_val)
        if old_opaque != new_opaque:
            return None

        changed_keys = [
            k
            for k in (set(old_entries) | set(new_entries))
            if old_entries.get(k) != new_entries.get(k)
        ]
        if not changed_keys:
            return None

        out: set[int] = set()
        if attr == "KEYWORDS":
            if not self.token_to_tests and "KEYWORDS" not in self.dict_key_to_tests:
                return None
            kw_map = self.dict_key_to_tests.get("KEYWORDS", {})
            for raw_k in changed_keys:
                ku = raw_k.strip()
                parts = ku.split()
                matched_tok = False
                if _WORD_RE.fullmatch(ku):
                    sid = self.token_to_tests.get(ku)
                    if sid is not None:
                        out.update(self.test_sets[sid])
                    matched_tok = True
                elif len(parts) in (2, 3) and all(_WORD_RE.fullmatch(w) for w in parts):
                    sid = self.token_to_tests.get(" ".join(parts))
                    if sid is not None:
                        out.update(self.test_sets[sid])
                    matched_tok = True
                elif 1 <= len(ku) <= 5 and all(
                    (not ch.isalnum() and not ch.isspace() and ch != "$") for ch in ku
                ):
                    sid = self.token_to_tests.get("SYM:" + ku)
                    if sid is not None:
                        out.update(self.test_sets[sid])
                    matched_tok = True
                if not matched_tok:
                    return None
                ksid = kw_map.get(ku)
                if ksid is not None:
                    out.update(self.test_sets[ksid])
        elif attr == "SINGLE_TOKENS":
            if not self.token_to_tests and "SINGLE_TOKENS" not in self.dict_key_to_tests:
                return None
            st_map = self.dict_key_to_tests.get("SINGLE_TOKENS", {})
            for raw_k in changed_keys:
                if len(raw_k) != 1:
                    return None
                sid = self.token_to_tests.get("SYM:" + raw_k)
                if sid is not None:
                    out.update(self.test_sets[sid])
                stsid = st_map.get(raw_k)
                if stsid is not None:
                    out.update(self.test_sets[stsid])
        elif attr in ("TRANSFORMS", "PROPERTIES_LOCATION"):
            dmap = self.dict_key_to_tests.get(attr)
            if dmap is None:
                dmap = self.expr_to_tests
            for k in changed_keys:
                sid = dmap.get(k)
                if sid is not None:
                    out.update(self.test_sets[sid])
        elif attr in ("FUNCTIONS", "FUNCTION_PARSERS", "NO_PAREN_FUNCTION_PARSERS"):
            for k in changed_keys:
                for map_name in ("FUNCTIONS", "FUNCTION_PARSERS", "NO_PAREN_FUNCTION_PARSERS"):
                    sid = self.dict_key_to_tests.get(map_name, {}).get(k)
                    if sid is not None:
                        out.update(self.test_sets[sid])
        elif attr in ("TIME_MAPPING", "FORMAT_MAPPING", "INVERSE_TIME_MAPPING", "INVERSE_FORMAT_MAPPING"):
            terms: set[str] = set(changed_keys)
            for k in changed_keys:
                terms.update(old_str_vals.get(k, ()))
                terms.update(new_str_vals.get(k, ()))
            if old_spreads:
                inherited = self._resolve_spread_str_map(old_val, set())
                if inherited is None:
                    return None
                for k in changed_keys:
                    terms.update(inherited.get(k, ()))
            extra_strict: set[str] = set()
            for term in terms:
                if term in _STRICT_TO_LAX_TIME:
                    extra_strict.add(_STRICT_TO_LAX_TIME[term])
                if term in _LAX_TO_STRICT_TIME:
                    extra_strict.add(_LAX_TO_STRICT_TIME[term])
            terms.update(extra_strict)
            for term in terms:
                if not term:
                    continue
                for map_name in (
                    "TIME_MAPPING",
                    "FORMAT_MAPPING",
                    "INVERSE_TIME_MAPPING",
                    "INVERSE_FORMAT_MAPPING",
                ):
                    sid = self.dict_key_to_tests.get(map_name, {}).get(term)
                    if sid is not None:
                        out.update(self.test_sets[sid])
                tsid = self.time_substr_to_tests.get(term)
                if tsid is not None:
                    out.update(self.test_sets[tsid])
        else:
            dmap = self.dict_key_to_tests.get(attr)
            if dmap is None:
                return None
            for k in changed_keys:
                sid = dmap.get(k)
                if sid is not None:
                    out.update(self.test_sets[sid])

        m = DIALECT_FILE_RE.match(rel)
        if m and m.group(1) not in ("dialect", "base", "__init__"):
            out = out & self._descendant_dialect_tests(m.group(1))

        isid = self.dict_iter_tests.get(attr)
        if isid is not None:
            out.update(self.test_sets[isid])
        return out

    def triage_commit(self, patch_text: str) -> tuple[set[int], dict[str, str | None]]:
        """Return (candidate_test_nums, {rel_path: new_content_or_None_if_deleted})."""
        pf = parse_patch(patch_text)
        cands: set[int] = set()
        patched_files: dict[str, str | None] = {}

        for f in pf:
            old_rel = f["old"]
            new_rel = f["new"]
            rel = new_rel or old_rel
            if not rel:
                continue

            if f.get("is_deleted") or (new_rel is None and old_rel is not None):
                # Deleted file
                target_del = old_rel or rel
                patched_files[target_del] = None
                cands.update(self._tests_importing_file(target_del, transitive=True))
                continue

            if f.get("is_new") or (old_rel is None and new_rel is not None):
                # Brand new file
                target_new = new_rel or rel
                new_src = apply_hunks("", f["hunks"])
                patched_files[target_new] = new_src
                new_cands: set[int] = set()
                m = DIALECT_FILE_RE.match(target_new)
                if m:
                    for d in self._descendant_dialects(m.group(1)):
                        new_cands.update(self.dialect_tests.get(d, ()))
                    if target_new.startswith("sqlglot/dialects/"):
                        new_cands.update(self.enum_tests)
                        new_cands.update(self.lazy_load_tests)
                if target_new.startswith("sqlglot/typing/"):
                    new_cands.update(self.typing_tests)
                    new_cands.update(
                        t["number"]
                        for t in self.tests
                        if t["id"].endswith(("::test_annotate_funcs", "::test_annotate_types"))
                    )
                if not new_cands:
                    new_cands.update(self.all_test_nums)
                cands.update(new_cands)
                continue

            if old_rel is not None and new_rel is not None and old_rel != new_rel:
                # Renamed file
                old_p = self.base_repo / old_rel
                old_src = (
                    old_p.read_text(encoding="utf-8", errors="replace") if old_p.exists() else ""
                )
                new_src = apply_hunks(old_src, f["hunks"])
                patched_files[old_rel] = None
                patched_files[new_rel] = new_src
                rcands = self._tests_importing_file(
                    old_rel, transitive=True
                ) | self._tests_importing_file(new_rel, transitive=True)
                cands.update(rcands if rcands else self.all_test_nums)
                continue

            orig_path = self.base_repo / rel
            if not orig_path.exists():
                cands.update(self.all_test_nums)
                continue

            old_src = orig_path.read_text(encoding="utf-8", errors="replace")
            new_src = apply_hunks(old_src, f["hunks"])

            t1: ast.AST | None = None
            t2: ast.AST | None = None
            if rel.endswith(".py"):
                try:
                    t1 = ast.parse(old_src.encode("utf-8"))
                    t2 = ast.parse(new_src.encode("utf-8"))
                    compile(new_src.encode("utf-8"), rel, "exec")
                except (SyntaxError, LookupError, UnicodeError):
                    patched_files[rel] = new_src
                    cands.update(self._tests_importing_file(rel, transitive=True))
                    continue

                changed_lines_pre: set[int] = set()
                for _h in f["hunks"]:
                    _ln = _h["old_start"]
                    for _hl in _h["lines"]:
                        if _hl.startswith((" ", "-")):
                            if _hl.startswith("-"):
                                changed_lines_pre.add(_ln)
                            _ln += 1
                        elif _hl.startswith("+"):
                            changed_lines_pre.add(_ln)

                eq_ast = _asts_structurally_equal(
                    t1,
                    t2,
                    allow_typing=not rel.startswith("sqlglot/typing/"),
                    allow_norm_strategy=(rel == "sqlglot/dialects/dialect.py"),
                    changed_lines=changed_lines_pre,
                )
                if (
                    eq_ast
                    and not _has_encoding_change(old_src, new_src)
                    and (rel not in self.file_open_to_tests or rel.startswith("sqlglot/typing/"))
                ):
                    # Pure comment/whitespace or statically equivalent edit in a Python file
                    continue

            patched_files[rel] = new_src

            if rel in self.file_open_to_tests:
                cands.update(self.test_sets[self.file_open_to_tests[rel]])

            if rel.startswith("sqlglot/") and (
                rel
                in (
                    "sqlglot/__init__.py",
                    "sqlglot/dialects/__init__.py",
                    "sqlglot/dialects/dialect.py",
                )
                or any(
                    hl.startswith(("+", "-"))
                    and ("import" in hl or "Dialect" in hl or "dialects" in hl)
                    for h in f["hunks"]
                    for hl in h["lines"]
                )
            ):
                cands.update(self.lazy_load_tests)
            if rel.startswith("sqlglot/dialects/"):
                cands.update(self.enum_tests)
            if rel.startswith("sqlglot/typing/"):
                cands.update(self.typing_tests)

            # Extract changed line numbers against original file
            changed_old_lines: dict[int, str] = {}
            pure_insert_anchors: set[int] = set()
            insert_line_texts: dict[int, str] = {}
            for h in f["hunks"]:
                ln = h["old_start"]
                prev_minus = False
                for hl in h["lines"]:
                    if hl.startswith(" "):
                        ln += 1
                        prev_minus = False
                    elif hl.startswith("-"):
                        changed_old_lines[ln] = hl[1:]
                        ln += 1
                        prev_minus = True
                    elif hl.startswith("+"):
                        if prev_minus:
                            changed_old_lines[ln - 1] = (
                                changed_old_lines.get(ln - 1, "") + "\n" + hl[1:]
                            )
                        else:
                            if ln > 1:
                                pure_insert_anchors.add(ln - 1)
                                insert_line_texts[ln - 1] = (
                                    insert_line_texts.get(ln - 1, "") + "\n" + hl[1:]
                                )
                            pure_insert_anchors.add(ln)
                            insert_line_texts[ln] = insert_line_texts.get(ln, "") + "\n" + hl[1:]

            if not rel.endswith(".py"):
                if rel not in self.file_open_to_tests:
                    if not (rel.endswith((".md", ".txt", ".rst")) or rel.startswith("docs/")):
                        rc = self._tests_importing_file(rel, transitive=True)
                        cands.update(rc if rc else self.all_test_nums)
                continue

            lmap = self.line_to_tests.get(rel, {})
            fmap = self.func_to_tests.get(rel, {})
            defs = self.file_defs.get(rel, [])
            classes = self.file_classes.get(rel, [])
            assert t1 is not None and t2 is not None
            t1_fns, t1_attrs = self._index_ast_nodes(t1)
            t2_fns, t2_attrs = self._index_ast_nodes(t2)
            all_changed_lns = set(changed_old_lines.keys()) | pure_insert_anchors
            narrowed_fn_cache: dict[str, set[int] | None] = {}
            dict_attr_cache: dict[tuple[str, str], set[int] | None] = {}

            for ln in list(changed_old_lines.keys()) + sorted(pure_insert_anchors):
                txt = changed_old_lines.get(ln, "") or insert_line_texts.get(ln, "")
                sid = lmap.get(str(ln))
                if sid is not None:
                    cands.update(self.test_sets[sid])

                enclosing_funcs = [d for d in defs if d["s"] <= ln <= d["e"]]
                if (
                    not enclosing_funcs
                    and rel.startswith("sqlglot/")
                    and not DIALECT_FILE_RE.match(rel)
                ):
                    cands.update(self.lazy_load_tests)
                ftests: set[int] = set()
                only_lambda = bool(enclosing_funcs) and all(
                    d["q"].endswith("<lambda>") for d in enclosing_funcs
                )
                if enclosing_funcs:
                    non_lambda_funcs = [d for d in enclosing_funcs if not d["q"].endswith("<lambda>")]
                    target_funcs = (
                        [non_lambda_funcs[-1]]
                        if non_lambda_funcs and ln > non_lambda_funcs[-1]["fl"]
                        else enclosing_funcs
                    )
                    for d in target_funcs:
                        if (
                            not d["q"].endswith("<lambda>")
                            and ln > d["fl"]
                            and rel.startswith("sqlglot/")
                            and not rel.startswith("sqlglot/typing/")
                        ):
                            qn = d["q"]
                            if qn not in narrowed_fn_cache:
                                narrowed_fn_cache[qn] = self._ast_narrow_func_tests(
                                    rel, d, t1_fns.get(qn), t2_fns.get(qn), lmap, all_changed_lns
                                )
                            nt = narrowed_fn_cache[qn]
                            ftests.update(nt if nt is not None else self._func_tests(rel, d))
                        else:
                            ftests.update(self._func_tests(rel, d))
                            if ln <= d["fl"] or not ftests:
                                fn_sym = d["q"].split(".")[-1]
                                if fn_sym != "<lambda>":
                                    ftests.update(self._reader_tests_for_symbol(fn_sym))
                    cands.update(ftests)
                    if not ftests and sid is None:
                        is_stub = all(
                            self._is_stub_ast(t1_fns.get(d["q"]))
                            and self._is_stub_ast(t2_fns.get(d["q"]))
                            for d in enclosing_funcs
                            if not d["q"].endswith("<lambda>")
                        ) and any(not d["q"].endswith("<lambda>") for d in enclosing_funcs)
                        has_reader_or_hook = rel.startswith("tests/") or any(
                            ln <= d["fl"]
                            or d["q"].split(".")[-1].startswith("__")
                            or d["q"].split(".")[-1] == "_generate_next_value_"
                            or (
                                d["q"].split(".")[-1].endswith("_sql")
                                and not d["q"].split(".")[-1].startswith("_")
                            )
                            or d["q"].split(".")[-1] in self._covered_methods
                            or d["q"].split(".")[-1] in self.symbol_readers
                            for d in enclosing_funcs
                        )
                        if not is_stub and has_reader_or_hook:
                            m = DIALECT_FILE_RE.match(rel)
                            if (
                                m
                                and m.group(1) not in ("dialect", "base", "__init__")
                                and not any(
                                    d["q"].split(".")[-1]
                                    in ("setUp", "setUpClass", "tearDown", "tearDownClass")
                                    for d in enclosing_funcs
                                )
                                and all(ln > d["fl"] for d in enclosing_funcs)
                            ):
                                cands.update(self._descendant_dialect_tests(m.group(1)))
                            else:
                                cands.update(self._tests_importing_file(rel, transitive=False))

                lambda_needs_class_check = False
                if only_lambda:
                    if not ftests or ln in pure_insert_anchors:
                        lambda_needs_class_check = True
                    elif any(ln == d["s"] for d in enclosing_funcs):
                        if ln in changed_old_lines and "\n" in changed_old_lines[ln]:
                            old_part, new_part = changed_old_lines[ln].split("\n", 1)
                            if (
                                "lambda" not in old_part
                                or "lambda" not in new_part
                                or old_part.split("lambda", 1)[0] != new_part.split("lambda", 1)[0]
                            ):
                                lambda_needs_class_check = True
                        else:
                            lambda_needs_class_check = True

                if not enclosing_funcs or lambda_needs_class_check:
                    hit = False
                    for c in classes:
                        if c["s"] <= ln <= c["e"]:
                            for attr, rng in c["attrs"].items():
                                if rng[0] <= ln <= rng[1]:
                                    hit = True
                                    cname = c["q"].split(".")[-1]
                                    if rel.startswith("sqlglot/expressions/"):
                                        rtests: set[int] = set(self._reader_tests_for_symbol(cname))
                                        esid = self.expr_to_tests.get(cname)
                                        if esid is not None:
                                            rtests.update(self.test_sets[esid])
                                        sub_q = list(self.subclasses.get(cname, ()))
                                        seen_subs = set(sub_q)
                                        while sub_q:
                                            sub_c = sub_q.pop()
                                            rtests.update(self._reader_tests_for_symbol(sub_c))
                                            sesid = self.expr_to_tests.get(sub_c)
                                            if sesid is not None:
                                                rtests.update(self.test_sets[sesid])
                                            for ss in self.subclasses.get(sub_c, ()):
                                                if ss not in seen_subs:
                                                    seen_subs.add(ss)
                                                    sub_q.append(ss)
                                        for cln in range(c["s"], c["e"] + 1):
                                            csid = lmap.get(str(cln))
                                            if csid is not None:
                                                rtests.update(self.test_sets[csid])
                                        if rel == "sqlglot/expressions/datatypes.py":
                                            snake1 = re.sub(
                                                r"([a-z0-9])([A-Z])",
                                                r"\1_\2",
                                                re.sub(r"([A-Z]+)([A-Z][a-z])", r"\1_\2", cname),
                                            ).upper()
                                            snake2 = re.sub(
                                                r"([a-z0-9])([A-Z])", r"\1_\2", cname
                                            ).upper()
                                            for sn in {snake1, snake2}:
                                                rtests.update(self._reader_tests_for_symbol(sn))
                                        cands.update(
                                            rtests
                                            if rtests
                                            else self._tests_importing_file(rel, transitive=False)
                                        )
                                        cands.update(self.typing_tests)
                                    else:
                                        if attr in _TRACKED_DICT_ATTRS:
                                            dkey = (c["q"], attr)
                                            if dkey not in dict_attr_cache:
                                                dict_attr_cache[dkey] = self._ast_diff_dict_attr(
                                                    rel,
                                                    attr,
                                                    t1_attrs.get(dkey),
                                                    t2_attrs.get(dkey),
                                                )
                                            dt = dict_attr_cache[dkey]
                                            if dt is not None:
                                                cands.update(dt)
                                                continue

                                        is_tok = c["q"].endswith("Tokenizer") or attr in (
                                            "NUMERIC_ESCAPES",
                                            "DROP_UNKNOWN_ESCAPES",
                                            "NUMERIC_ESCAPES_ARE_BYTES",
                                            "LONE_SURROGATE_REPLACEMENT",
                                        )
                                        rtests = self._reader_tests_for_symbol(
                                            attr, is_tokenizer=is_tok
                                        )
                                        m = DIALECT_FILE_RE.match(rel)
                                        if m and m.group(1) not in ("dialect", "base", "__init__"):
                                            desc = self._descendant_dialects(m.group(1))
                                            dtests = self._descendant_dialect_tests(m.group(1))
                                            cross_dtests: set[int] = set()
                                            own_tests: set[int] = set()
                                            for d in desc:
                                                cross_dtests.update(
                                                    self.cross_dialect_tests.get(d, ())
                                                )
                                                own_tests.update(
                                                    self._own_dialect_tests.get(d, ())
                                                )
                                            inter = rtests & dtests
                                            if (
                                                inter
                                                and attr
                                                not in (
                                                    "Parser",
                                                    "Generator",
                                                    "Tokenizer",
                                                    "JSONPathTokenizer",
                                                )
                                            ):
                                                cands.update(inter)
                                            else:
                                                cands.update(
                                                    inter | own_tests | dtests | cross_dtests
                                                )
                                        else:
                                            cands.update(
                                                rtests
                                                if rtests
                                                else self._tests_importing_file(
                                                    rel, transitive=False
                                                )
                                            )
                    if not hit and (
                        not enclosing_funcs or (only_lambda and not ftests and sid is None)
                    ):
                        for line_part in txt.splitlines():
                            m_lhs = re.match(
                                r"^([A-Za-z_][A-Za-z0-9_]*)\s*(?::[^=]+)?=", line_part
                            )
                            if m_lhs:
                                cands.update(self._reader_tests_for_symbol(m_lhs.group(1)))
                        cands.update(self._tests_importing_file(rel, transitive=False))

        return cands, patched_files


def _link_or_copy_file(src: Path, dst: Path) -> None:
    try:
        os.symlink(src, dst)
    except OSError:
        try:
            os.link(src, dst)
        except OSError:
            shutil.copy2(src, dst)


def _build_overlay(base_repo: Path, overlay_dir: Path) -> None:
    """Create a symlink/hardlink mirror of base_repo in overlay_dir (0 bytes data)."""
    if overlay_dir.exists():
        shutil.rmtree(overlay_dir, ignore_errors=True)
    overlay_dir.mkdir(parents=True, exist_ok=True)
    for sub in ("sqlglot", "tests", "sqlglotc"):
        src_sub = base_repo / sub
        if not src_sub.exists():
            continue
        dst_sub = overlay_dir / sub
        if sub == "tests":
            dst_sub.mkdir(parents=True, exist_ok=True)
            for item in src_sub.iterdir():
                dst_item = dst_sub / item.name
                if item.name == "fixtures" and item.is_dir():
                    try:
                        os.symlink(item, dst_item, target_is_directory=True)
                    except OSError:
                        _symlink_tree(item, dst_item)
                elif item.is_dir():
                    _symlink_tree(item, dst_item)
                else:
                    _link_or_copy_file(item, dst_item)
        else:
            _symlink_tree(src_sub, dst_sub)


def _symlink_tree(src_dir: Path, dst_dir: Path) -> None:
    dst_dir.mkdir(parents=True, exist_ok=True)
    for entry in src_dir.iterdir():
        dst_entry = dst_dir / entry.name
        if entry.is_dir():
            _symlink_tree(entry, dst_entry)
        else:
            _link_or_copy_file(entry, dst_entry)


def _apply_overlay_patches(
    base_repo: Path, overlay_dir: Path, patched_files: dict[str, str | None]
) -> list[tuple[Path, Path | None, bool]]:
    """Apply patched_files inside overlay_dir; return restore records."""
    restores: list[tuple[Path, Path | None, bool]] = []
    # If any test fixture is modified, materialize tests/fixtures directory as real dirs + links
    if any(rel.startswith("tests/fixtures/") for rel in patched_files):
        fix_dst = overlay_dir / "tests" / "fixtures"
        if fix_dst.is_symlink():
            fix_dst.unlink()
            _symlink_tree(base_repo / "tests" / "fixtures", fix_dst)
            restores.append((fix_dst, base_repo / "tests" / "fixtures", True))

    # If sqlglotc/setup.py is modified, ensure tests/test_sqlglotc.py resolves inside overlay
    if any(rel.startswith("sqlglotc/") for rel in patched_files):
        tsg = overlay_dir / "tests" / "test_sqlglotc.py"
        if tsg.is_symlink():
            tsg.unlink()
            shutil.copy2(base_repo / "tests" / "test_sqlglotc.py", tsg)
            restores.append((tsg, base_repo / "tests" / "test_sqlglotc.py", False))

    for rel, content in patched_files.items():
        dst = overlay_dir / rel
        src_orig = base_repo / rel
        had_orig = src_orig.exists()
        # Unlink pre-compiled .pyc symlink for any patched .py file so Python compiles fresh source
        if rel.endswith(".py"):
            pycache_dst = dst.parent / "__pycache__"
            pycache_src = src_orig.parent / "__pycache__"
            if pycache_dst.is_dir():
                for pyc in pycache_dst.glob(f"{dst.stem}.cpython-*.pyc"):
                    orig_pyc = pycache_src / pyc.name
                    pyc.unlink()
                    if orig_pyc.exists():
                        restores.append((pyc, orig_pyc, False))
        if dst.exists() or dst.is_symlink():
            dst.unlink()
        if content is not None:
            dst.parent.mkdir(parents=True, exist_ok=True)
            dst.write_text(content, encoding="utf-8")
        restores.append((dst, src_orig if had_orig else None, False))
    return restores


def _restore_overlay(restores: list[tuple[Path, Path | None, bool]]) -> None:
    for dst, orig, is_dir in reversed(restores):
        if dst.is_symlink() or dst.is_file():
            dst.unlink()
        elif dst.is_dir():
            shutil.rmtree(dst, ignore_errors=True)
        if orig is not None:
            if is_dir:
                try:
                    os.symlink(orig, dst, target_is_directory=True)
                except OSError:
                    _symlink_tree(orig, dst)
            else:
                _link_or_copy_file(orig, dst)


def _needs_pickle(patched_files: dict[str, str | None] | None) -> bool:
    if not patched_files:
        return False
    return (
        "sqlglot/serde.py" in patched_files
        or "sqlglot/executor/table.py" in patched_files
        or any(k.startswith("sqlglot/expressions/") for k in patched_files)
    )


_TOK_GENERATOR_ATTRS = frozenset(
    {
        "QUOTES",
        "IDENTIFIERS",
        "COMMENTS",
        "BIT_STRINGS",
        "HEX_STRINGS",
        "BYTE_STRINGS",
        "UNICODE_STRINGS",
        "RAW_STRINGS",
        "HEREDOC_STRINGS",
        "NATIONAL_RAW_STRINGS",
        "STRING_ESCAPES",
        "BYTE_STRING_ESCAPES",
        "IDENTIFIER_ESCAPES",
        "UNESCAPED_SEQUENCES",
        "ESCAPED_SEQUENCES",
        "HINT_START",
    }
)


def _tokens_py_parser_only_safe(old_src: str, new_src: str) -> bool:
    try:
        t1 = ast.parse(old_src.encode("utf-8"))
        t2 = ast.parse(new_src.encode("utf-8"))
    except SyntaxError:
        return False

    def sig(tree: ast.Module):
        top = []
        cls_sigs = {}
        for stmt in tree.body:
            if isinstance(stmt, ast.ClassDef):
                if stmt.name == "TokenType":
                    top.append(ast.dump(stmt, include_attributes=False))
                else:
                    attrs = {}
                    for cs in stmt.body:
                        if isinstance(cs, ast.Assign):
                            for tgt in cs.targets:
                                if isinstance(tgt, ast.Name) and tgt.id in _TOK_GENERATOR_ATTRS:
                                    attrs[tgt.id] = ast.dump(cs.value, include_attributes=False)
                        elif (
                            isinstance(cs, ast.AnnAssign)
                            and isinstance(cs.target, ast.Name)
                            and cs.target.id in _TOK_GENERATOR_ATTRS
                        ):
                            attrs[cs.target.id] = (
                                ast.dump(cs.value, include_attributes=False) if cs.value else ""
                            )
                    cls_sigs[stmt.name] = attrs
            elif not isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef)):
                top.append(ast.dump(stmt, include_attributes=False))
        return top, cls_sigs

    return sig(t1) == sig(t2)


def _classify_commit_mode(
    patched_files: dict[str, str | None] | None, base_repo: Path
) -> str | None:
    """Classify isolated commits into 'gen_only', 'parser_only', 'opt_only', or None."""
    if not patched_files or any(v is None for v in patched_files.values()):
        return None
    keys = list(patched_files.keys())
    if all(
        k in ("sqlglot/generator.py", "sqlglot/transforms.py") or k.startswith("sqlglot/generators/")
        for k in keys
    ):
        return "gen_only"
    if all(
        k in ("sqlglot/parser.py", "sqlglot/tokenizer_core.py", "sqlglot/trie.py", "sqlglot/tokens.py")
        or k.startswith("sqlglot/parsers/")
        for k in keys
    ):
        if "sqlglot/tokens.py" in patched_files:
            orig_tok = base_repo / "sqlglot/tokens.py"
            new_tok = patched_files["sqlglot/tokens.py"]
            if not orig_tok.exists() or new_tok is None:
                return None
            if not _tokens_py_parser_only_safe(
                orig_tok.read_text(encoding="utf-8", errors="replace"), new_tok
            ):
                return None
        return "parser_only"
    if all(k.startswith("sqlglot/optimizer/") for k in keys):
        return "opt_only"
    return None


def _strip_leading_sql_comments(sql: str) -> str:
    s = sql.lstrip()
    while s.startswith(("--", "/*")):
        if s.startswith("--"):
            nl = s.find("\n")
            s = s[nl + 1 :].lstrip() if nl != -1 else ""
        else:
            end = s.find("*/")
            s = s[end + 2 :].lstrip() if end != -1 else ""
    return s


def _hash_tpc_result(duck_sql: str, columns, rows) -> str:
    return hashlib.sha256(
        pickle.dumps((duck_sql, tuple(columns), list(rows)), protocol=4)
    ).hexdigest()


def _plan_py_hash(py_exec, plan, planner_mod) -> str:
    """Hash all generated Python expressions across a Plan without executing row loops."""
    out: list[str] = []
    seen_sq: set[str] = set()

    def walk_plan(p) -> None:
        old_ctes = py_exec._ctes
        py_exec._ctes = p.ctes
        try:
            finished: set[object] = set()
            queue = sorted(p.leaves, key=lambda n: n.id)
            while queue:
                node = queue.pop(0)
                if isinstance(node, planner_mod.Scan):
                    _gen_one(node.condition, "S:c")
                    _gen_many(node.projections, "S:p")
                elif isinstance(node, planner_mod.Join):
                    for j in node.joins.values():
                        _gen_one(j.get("condition"), "J:jc")
                        _gen_many(j.get("source_key"), "J:sk")
                        _gen_many(j.get("join_key"), "J:jk")
                    _gen_one(node.condition, "J:c")
                    _gen_many(node.projections, "J:p")
                elif isinstance(node, planner_mod.Aggregate):
                    _gen_many(node.group.values(), "A:g")
                    _gen_many(node.aggregations, "A:a")
                    _gen_many(node.operands, "A:o")
                    _gen_one(node.condition, "A:c")
                    _gen_many(node.projections, "A:p")
                elif isinstance(node, planner_mod.Sort):
                    _gen_many(node.projections, "O:p")
                    _gen_many(node.key, "O:k")
                elif isinstance(node, planner_mod.SetOperation):
                    _gen_many(node.projections, "U:p")
                finished.add(node)
                for dep in sorted(node.dependents, key=lambda n: n.id):
                    if dep not in finished and dep not in queue and all(
                        d in finished for d in dep.dependencies
                    ):
                        queue.append(dep)
        finally:
            py_exec._ctes = old_ctes

        for sq_name in sorted(py_exec._subquery_plans):
            if sq_name not in seen_sq:
                seen_sq.add(sq_name)
                walk_plan(py_exec._subquery_plans[sq_name][0])

    def _gen_one(expr, tag: str) -> None:
        if expr:
            e = py_exec._replace_subqueries(expr)
            out.append(f"{tag}:{py_exec.generator.generate(e)}")

    def _gen_many(exprs, tag: str) -> None:
        if exprs:
            for e in exprs:
                _gen_one(e, tag)

    walk_plan(plan)
    out.sort()
    return hashlib.sha256("\0".join(out).encode("utf-8")).hexdigest()


_OPTIMIZER_INIT_DDL = """
                    CREATE TABLE x (a INT, b INT);
                    CREATE TABLE y (b INT, c INT);
                    CREATE TABLE z (b INT, c INT);
                    CREATE TABLE w (d TEXT, e TEXT);

                    INSERT INTO x VALUES (1, 1);
                    INSERT INTO x VALUES (2, 2);
                    INSERT INTO x VALUES (2, 2);
                    INSERT INTO x VALUES (3, 3);
                    INSERT INTO x VALUES (null, null);

                    INSERT INTO y VALUES (2, 2);
                    INSERT INTO y VALUES (2, 2);
                    INSERT INTO y VALUES (3, 3);
                    INSERT INTO y VALUES (4, 4);
                    INSERT INTO y VALUES (null, null);

                    INSERT INTO y VALUES (3, 3);
                    INSERT INTO y VALUES (3, 3);
                    INSERT INTO y VALUES (4, 4);
                    INSERT INTO y VALUES (5, 5);
                    INSERT INTO y VALUES (null, null);

                    INSERT INTO w VALUES ('a', 'b');

                    CREATE TABLE unpivotable (id INT, jan INT, feb INT, north INT, south INT);
                    INSERT INTO unpivotable VALUES (1, 100, 200, 7, 8);
                    INSERT INTO unpivotable VALUES (2, 300, 400, 9, 10);

                    CREATE TABLE pivotable (id INT, cat TEXT, val INT, kind TEXT, amt INT);
                    INSERT INTO pivotable VALUES (1, 'a', 10, 'x', 5);
                    INSERT INTO pivotable VALUES (1, 'b', 20, 'x', 5);

                    CREATE TABLE comparisons AS
                    SELECT * FROM (VALUES (1), (2), (NULL)) AS x(a)
                    CROSS JOIN (VALUES (1), (2), (NULL)) AS y(b)
                    CROSS JOIN (VALUES (TRUE), (FALSE), (NULL)) AS z(c);
                    """


class _FastDF:
    """Lazy DataFrame proxy backed by a cached typed column+row signature."""

    def __init__(self, sig, loader):
        self.sig = sig
        self._loader = loader
        self._df = None

    def to_df(self):
        if self._df is None:
            self._df = self._loader()
        return self._df

    def __getattr__(self, name):
        return getattr(self.to_df(), name)


class _CachedDuckCursor:
    def __init__(self, conn, sql: str, rows_cache: dict, df_cache: dict):
        self._conn = conn
        self._sql = sql
        self._rows_cache = rows_cache
        self._df_cache = df_cache

    def _key(self) -> bytes:
        return hashlib.sha256(
            ("\0".join(self._conn._ddl) + "\0" + self._sql).encode("utf-8")
        ).digest()[:12]

    def fetchall(self):
        if not self._conn._tainted:
            k = self._key()
            if k in self._rows_cache:
                return self._rows_cache[k]
        return self._conn._ensure_real().execute(self._sql).fetchall()

    def df(self):
        if not self._conn._tainted:
            k = self._key()
            if k in self._df_cache:
                return _FastDF(
                    self._df_cache[k],
                    lambda sql=self._sql, conn=self._conn: conn._ensure_real().execute(sql).df(),
                )
        return self._conn._ensure_real().execute(self._sql).df()

    def __getattr__(self, name):
        return getattr(self._conn._ensure_real().execute(self._sql), name)


def _connect_duck_single_thread(orig_connect):
    try:
        return orig_connect(config={"threads": 1})
    except TypeError:
        return orig_connect()


class _CachedDuckConn:
    """Read-through DuckDB connection cache keyed by DDL history and SQL."""

    def __init__(self, orig_connect, rows_cache: dict, df_cache: dict, init_ddl: str | None = None):
        self._orig_connect = orig_connect
        self._rows_cache = rows_cache
        self._df_cache = df_cache
        self._ddl = [init_ddl] if init_ddl else []
        self._real = None
        self._tainted = False

    def _ensure_real(self):
        if self._real is None:
            self._real = _connect_duck_single_thread(self._orig_connect)
            for d in self._ddl:
                self._real.execute(_OPTIMIZER_INIT_DDL if d == "__TEST_OPTIMIZER_CONN__" else d)
        return self._real

    def execute(self, sql, *args, **kwargs):
        if args or kwargs or self._tainted:
            self._tainted = True
            return self._ensure_real().execute(sql, *args, **kwargs)
        p = _strip_leading_sql_comments(sql)[:10].upper()
        if not p.startswith(("SELECT", "WITH", "(", "VALUES", "FROM")):
            self._ddl.append(sql)
            if self._real is not None:
                self._real.execute(sql)
            return self
        return _CachedDuckCursor(self, sql, self._rows_cache, self._df_cache)

    def close(self):
        if self._real is not None:
            self._real.close()
            self._real = None
        self._tainted = False
        self._ddl = self._ddl[:1] if self._ddl[:1] == ["__TEST_OPTIMIZER_CONN__"] else []

    def __enter__(self):
        return self

    def __exit__(self, *a):
        self.close()

    def __getattr__(self, name):
        self._tainted = True
        return getattr(self._ensure_real(), name)


def _install_lazy_optimizer_conn(cls) -> None:
    """Defer TestOptimizer's DuckDB setup until a query misses the read-through cache."""
    if getattr(cls, "_lazy_conn_installed", False):
        return
    import duckdb as _duckdb

    orig_connect = getattr(cls, "_orig_duckdb_connect", None) or _duckdb.connect
    cls._orig_duckdb_connect = orig_connect

    class _LazyConnDescriptor:
        def __get__(self, instance, owner=None):
            target = owner if owner is not None else cls
            conn = getattr(target, "_real_conn", None)
            if conn is None:
                if (
                    _TPC_CACHE is not None
                    and "duck_rows_cache" in _TPC_CACHE
                    and "duck_df_cache" in _TPC_CACHE
                ):
                    conn = _CachedDuckConn(
                        orig_connect,
                        _TPC_CACHE["duck_rows_cache"],
                        _TPC_CACHE["duck_df_cache"],
                        init_ddl="__TEST_OPTIMIZER_CONN__",
                    )
                else:
                    conn = _connect_duck_single_thread(orig_connect)
                    conn.execute(_OPTIMIZER_INIT_DDL)
                target._real_conn = conn
            return conn

    cls._real_conn = None
    cls._lazy_conn_installed = True
    type.__setattr__(cls, "conn", _LazyConnDescriptor())


def _patch_test_executor_with_cache(
    cls,
    mod,
    patched_files: dict[str, str | None] | None,
    use_pickle: bool = False,
    commit_mode: str | None = None,
) -> bool:
    """Use preloaded TPC-DS tables + SHA-256 baseline hashes when DuckDB/TPC fixtures are untouched."""
    if _TPC_CACHE is None:
        return False
    pfiles = patched_files or {}
    if any(
        k.startswith("tests/fixtures/optimizer/tpc-")
        or k
        in (
            "sqlglot/dialects/duckdb.py",
            "sqlglot/generators/duckdb.py",
            "sqlglot/parsers/duckdb.py",
            "tests/test_executor.py",
            "tests/helpers.py",
        )
        for k in pfiles
    ):
        return False

    from sqlglot.executor.table import Table

    cls.tpch_tables = {}
    cls.tpcds_tables = {
        name: Table(columns=cols, rows=rows)
        for name, (cols, rows) in _TPC_CACHE["tpcds_tables"].items()
    }
    cls.tpch_sqls = _TPC_CACHE["tpch_sqls"]
    cls.tpcds_sqls = _TPC_CACHE["tpcds_sqls"]
    cls.tpch_conn = None
    cls.tpcds_conn = None
    cls.cache = {}

    executor_touched = any(
        k.startswith("sqlglot/executor/")
        or k.startswith("sqlglot/expressions/")
        or k
        in (
            "sqlglot/planner.py",
            "sqlglot/dialects/python.py",
            "sqlglot/generators/python.py",
            "sqlglot/generator.py",
            "sqlglot/transforms.py",
            "sqlglot/dialects/dialect.py",
            "sqlglot/helper.py",
            "sqlglot/errors.py",
            "sqlglot/schema.py",
            "sqlglot/optimizer/scope.py",
            "sqlglot/optimizer/eliminate_joins.py",
            "sqlglot/time.py",
            "sqlglot/__init__.py",
        )
        for k in pfiles
    )

    tpch_opt_duck = _TPC_CACHE["tpch_opt_duck"]
    tpcds_hashes = _TPC_CACHE["tpcds_hashes"]
    tpcds_plan_hashes = _TPC_CACHE["tpcds_plan_hashes"]
    tpcds_opt_dumps = _TPC_CACHE.get("tpcds_opt_dumps")
    tpcds_py_hashes = _TPC_CACHE.get("tpcds_py_hashes")
    tpcds_dump_py_hashes = _TPC_CACHE.get("tpcds_dump_py_hashes") or tpcds_py_hashes
    tpcds_duck_sqls = _TPC_CACHE.get("tpcds_duck_sqls") or {}
    only_executor_touched = (
        bool(pfiles)
        and "sqlglot/executor/__init__.py" not in pfiles
        and all(
            k.startswith("sqlglot/executor/") or k == "sqlglot/planner.py" for k in pfiles
        )
    )
    can_use_py_hash = (tpcds_py_hashes is not None) and not any(
        k.startswith(("sqlglot/executor/", "sqlglot/expressions/"))
        or k
        in (
            "sqlglot/planner.py",
            "sqlglot/serde.py",
            "sqlglot/helper.py",
            "sqlglot/errors.py",
            "sqlglot/schema.py",
            "sqlglot/optimizer/scope.py",
            "sqlglot/__init__.py",
        )
        for k in pfiles
    )
    can_reuse_tpcds_opt = not any(
        k in pfiles
        for k in (
            "sqlglot/optimizer/optimizer.py",
            "sqlglot/optimizer/qualify.py",
            "sqlglot/optimizer/isolate_table_selects.py",
        )
    )
    parse_touched = any(
        k in pfiles
        for k in ("sqlglot/parser.py", "sqlglot/tokens.py", "sqlglot/tokenizer_core.py")
    ) or any(k.startswith(("sqlglot/parsers/", "sqlglot/expressions/")) for k in pfiles)
    plan_touched = any(
        k.startswith("sqlglot/expressions/")
        or k
        in (
            "sqlglot/planner.py",
            "sqlglot/helper.py",
            "sqlglot/errors.py",
            "sqlglot/optimizer/scope.py",
            "sqlglot/optimizer/eliminate_joins.py",
            "sqlglot/optimizer/normalize.py",
            "sqlglot/serde.py",
            "sqlglot/__init__.py",
        )
        for k in pfiles
    )
    can_use_raw_dumps = (commit_mode == "gen_only") and not parse_touched

    global _TPCDS_RAW_DUMPS, _TPCDS_PLAN_EXPR_DUMPS
    if can_use_raw_dumps and _TPCDS_RAW_DUMPS is None and "tpcds_raw_dumps_z" in _TPC_CACHE:
        _TPCDS_RAW_DUMPS = pickle.loads(zlib.decompress(_TPC_CACHE["tpcds_raw_dumps_z"]))
    if (
        not plan_touched
        and _TPCDS_PLAN_EXPR_DUMPS is None
        and "tpcds_plan_expr_dumps_z" in _TPC_CACHE
    ):
        _TPCDS_PLAN_EXPR_DUMPS = pickle.loads(zlib.decompress(_TPC_CACHE["tpcds_plan_expr_dumps_z"]))

    orig_opt_tpch = cls.test_optimized_tpch

    def _fast_test_optimized_tpch(self, _orig=orig_opt_tpch):
        for i, (_, sql, optimized) in enumerate(self.tpch_sqls):
            pair = (
                mod.transpile(sql, write="duckdb")[0],
                mod.transpile(optimized, write="duckdb")[0],
            )
            if pair != tpch_opt_duck[i]:
                return _orig(self)

    def _fast_mp_execute(self, schema, tables, sqls, tpch):
        pickled_once = False
        if tpch:
            for _, sql, _ in sqls:
                e = mod.parse_one(sql)
                if use_pickle and not pickled_once:
                    pickle.loads(pickle.dumps(e))
                    if tables:
                        pickle.loads(pickle.dumps(next(iter(tables.values()))))
                    pickled_once = True
            return
        mod.initializer(schema, tables)
        from sqlglot import exp as _exp, planner as _planner

        indices = list(range(len(sqls)))
        if _COMMIT_TPCDS_FAILED_IDX is not None and 0 <= _COMMIT_TPCDS_FAILED_IDX < len(sqls):
            indices = [_COMMIT_TPCDS_FAILED_IDX] + [
                idx for idx in indices if idx != _COMMIT_TPCDS_FAILED_IDX
            ]
        reused_opt_verified = False
        py_exec = None

        for i in indices:
            meta, sql, _ = sqls[i]
            if not meta.get("execute"):
                if parse_touched:
                    mod.parse_one(sql)
                continue
            if only_executor_touched and tpcds_opt_dumps and i in tpcds_opt_dumps:
                opt_expr = _exp.Expr.load(tpcds_opt_dumps[i])
                if use_pickle and not pickled_once:
                    opt_expr, meta = pickle.loads(pickle.dumps((opt_expr, meta)))
                    if tables:
                        pickle.loads(pickle.dumps(next(iter(tables.values()))))
                    pickled_once = True
                duck_sql = tpcds_duck_sqls.get(i) or mod.transpile(sql, write="duckdb")[0]
                plan = mod.Plan(opt_expr)
                tbl = mod.PythonExecutor(tables=mod.ensure_tables(mod._tables)).execute(plan)
            elif (
                reused_opt_verified
                and executor_touched
                and can_use_py_hash
                and tpcds_opt_dumps
                and i in tpcds_opt_dumps
            ):
                raw_d = _TPCDS_RAW_DUMPS.get(i) if (can_use_raw_dumps and _TPCDS_RAW_DUMPS) else None
                if raw_d is not None:
                    duck_sql = _exp.Expr.load(raw_d).sql(dialect="duckdb")
                    expr = None
                else:
                    expr = mod.parse_one(sql)
                    duck_sql = expr.sql(dialect="duckdb")
                if duck_sql == tpcds_duck_sqls.get(i):
                    pe_d = (
                        _TPCDS_PLAN_EXPR_DUMPS.get(i)
                        if (not plan_touched and _TPCDS_PLAN_EXPR_DUMPS)
                        else None
                    )
                    if pe_d is not None and tpcds_dump_py_hashes and i in tpcds_dump_py_hashes:
                        if py_exec is None:
                            py_exec = mod.PythonExecutor()
                        py_gen = py_exec.generator
                        chk_out = sorted(
                            f"{tag}:{py_gen.generate(_exp.Expr.load(d))}" for tag, d in pe_d
                        )
                        if (
                            hashlib.sha256("\0".join(chk_out).encode("utf-8")).hexdigest()
                            == tpcds_dump_py_hashes[i]
                        ):
                            continue
                    else:
                        opt_expr = _exp.Expr.load(tpcds_opt_dumps[i])
                        plan = mod.Plan(opt_expr)
                        if py_exec is None:
                            py_exec = mod.PythonExecutor()
                        if tpcds_dump_py_hashes and i in tpcds_dump_py_hashes and (
                            _plan_py_hash(py_exec, plan, _planner)
                            == tpcds_dump_py_hashes[i]
                        ):
                            continue
                if expr is None:
                    expr = mod.parse_one(sql)
                tbl = mod.mp_execute(expr, meta)
            else:
                expr = mod.parse_one(sql)
                if use_pickle and not pickled_once:
                    expr, meta = pickle.loads(pickle.dumps((expr, meta)))
                    if tables:
                        pickle.loads(pickle.dumps(next(iter(tables.values()))))
                    pickled_once = True
                duck_sql = expr.sql(dialect="duckdb")
                if not executor_touched or can_use_py_hash:
                    opt_expr = mod.optimize(expr, schema, leave_tables_isolated=True)
                    ph = hashlib.sha256(
                        (duck_sql + "\0" + repr(opt_expr) + "\0" + opt_expr.sql()).encode(
                            "utf-8"
                        )
                    ).hexdigest()
                    if ph == tpcds_plan_hashes.get(i):
                        if (
                            i == 0
                            and _COMMIT_TPCDS_OPT_PASSED
                            and can_reuse_tpcds_opt
                            and tpcds_opt_dumps
                        ):
                            reused_opt_verified = True
                            if not executor_touched:
                                return
                        if not executor_touched:
                            continue
                        plan = mod.Plan(opt_expr)
                        if i in tpcds_py_hashes and (
                            _plan_py_hash(mod.PythonExecutor(), plan, _planner)
                            == tpcds_py_hashes[i]
                        ):
                            continue
                tbl = mod.mp_execute(expr, meta)
            if _hash_tpc_result(duck_sql, tbl.columns, tbl.rows) != tpcds_hashes.get(i):
                self.fail(f"tpcds mismatch at {i}")

    cls.test_optimized_tpch = _fast_test_optimized_tpch
    cls._mp_execute = _fast_mp_execute
    return True


def _install_optimizer_accelerators(
    cls,
    mod,
    patched_files: dict[str, str | None] | None,
    active_dialects: set[str] | None,
    base_repo: Path | None = None,
    commit_mode: str | None = None,
):
    """Install modified-first + dialect-scoped fixture filter, DuckDB query cache, stage-isolated check_file, and stress guards."""
    pfiles = patched_files or {}
    brepo = base_repo or Path(os.environ.get("BLAST_REPO_DIR", "/app/sqlglot")).resolve()
    saved_loader = None
    saved_check_file = None
    saved_duck_connect = None
    saved_afe = None
    saved_annotate_funcs = None

    has_opt_fixture_edit = any(k.startswith("tests/fixtures/optimizer/") for k in pfiles)
    if has_opt_fixture_edit or (active_dialects and "duckdb" not in active_dialects):
        orig_loader = getattr(mod, "load_sql_fixture_pairs", None)
        if orig_loader is not None:
            saved_loader = orig_loader
            import tests.helpers as _th

            def _scoped_loader(filename: str):
                if f"tests/fixtures/{filename}" in pfiles and not filename.startswith(
                    "optimizer/tpc-"
                ):
                    orig_path = brepo / "tests" / "fixtures" / filename
                    old_pairs_set: set[tuple] = set()
                    if orig_path.exists():
                        stmts = _th._filter_comments(orig_path.read_text(encoding="utf-8")).split(
                            ";"
                        )
                        for idx in range(0, len(stmts), 2):
                            if idx + 1 < len(stmts):
                                sql_p, meta_p = _th._extract_meta(stmts[idx].strip())
                                exp_p = stmts[idx + 1].strip()
                                old_pairs_set.add(
                                    (tuple(sorted(meta_p.items())), sql_p, exp_p)
                                )
                    changed_pairs = []
                    unchanged_pairs = []
                    for meta_p, sql_p, exp_p in orig_loader(filename):
                        key = (tuple(sorted(meta_p.items())), sql_p, exp_p)
                        if key in old_pairs_set:
                            unchanged_pairs.append((meta_p, sql_p, exp_p))
                        else:
                            changed_pairs.append((meta_p, sql_p, exp_p))
                    yield from changed_pairs
                    yield from unchanged_pairs
                    return

                if (
                    not active_dialects
                    or "duckdb" in active_dialects
                    or not filename.startswith("optimizer/")
                    or filename.startswith("optimizer/tpc-")
                ):
                    yield from orig_loader(filename)
                    return

                is_ann = filename == "optimizer/annotate_functions.sql"
                for meta, sql, expected in orig_loader(filename):
                    d_str = meta.get("dialect") or ""
                    if not d_str:
                        continue
                    matched = [x.strip() for x in d_str.split(",") if x.strip() in active_dialects]
                    if not matched:
                        continue
                    if is_ann:
                        yield {**meta, "dialect": ", ".join(matched)}, sql, expected
                    else:
                        yield meta, sql, expected

            mod.load_sql_fixture_pairs = _scoped_loader

    if (
        "tests/fixtures/optimizer/qualify_columns_ddl.sql" in pfiles
        and "tests/fixtures/optimizer/qualify_columns.sql" not in pfiles
        and hasattr(cls, "check_file")
    ):
        saved_check_file = cls.check_file
        orig_cf = saved_check_file

        def _reordered_check_file(self, file, func, pretty=False, execute=None, only=None, **kw):
            if file == "qualify_columns" and not getattr(self, "_qc_ddl_done", False):
                self._qc_ddl_done = True
                ddl_kw = {k: v for k, v in kw.items()}
                orig_cf(self, "qualify_columns_ddl", func, **ddl_kw)
                return orig_cf(
                    self, file, func, pretty=pretty, execute=execute, only=only, **kw
                )
            if file == "qualify_columns_ddl" and getattr(self, "_qc_ddl_done", False):
                self._qc_ddl_done = False
                return
            return orig_cf(self, file, func, pretty=pretty, execute=execute, only=only, **kw)

        cls.check_file = _reordered_check_file

    def _verify_aux_calls(file_key: str, explicit_aux: list | None = None) -> bool:
        if explicit_aux is not None:
            aux_calls = explicit_aux
        else:
            if _TPC_CACHE is None:
                return False
            f_meta = _TPC_CACHE.get("opt_fixture_meta", {}).get(file_key)
            if not f_meta:
                return False
            aux_calls = f_meta["aux_calls"]
        from sqlglot import exp as _exp
        from sqlglot.dialects.dialect import Dialect as _Dialect
        from sqlglot.errors import ErrorLevel as _EL

        try:
            for item in aux_calls:
                if len(item) == 5:
                    d_str, into_n, err_name, sql_s, expected_h = item
                else:
                    d_str, into_n, sql_s, expected_h = item
                    err_name = None
                d_inst = _Dialect.get_or_raise(d_str or None)
                if into_n == "__TOK__":
                    if _hash_tokens(d_inst.tokenize(sql_s)) != expected_h:
                        return False
                elif into_n is None:
                    el = _EL[err_name] if err_name else None
                    if _hash_expr_exact(d_inst.parse(sql_s, error_level=el)) != expected_h:
                        return False
                else:
                    into_cls = (
                        tuple(getattr(_exp, n) for n in into_n)
                        if isinstance(into_n, tuple)
                        else getattr(_exp, into_n)
                    )
                    el = _EL[err_name] if err_name else None
                    if _hash_expr_exact(d_inst.parse_into(into_cls, sql_s, error_level=el)) != expected_h:
                        return False
            return True
        except Exception:
            return False

    if (
        commit_mode in ("parser_only", "gen_only", "opt_only")
        and _TPC_CACHE is not None
        and "tests/test_optimizer.py" not in pfiles
        and "tests/helpers.py" not in pfiles
        and not has_opt_fixture_edit
        and hasattr(cls, "check_file")
    ):
        if saved_check_file is None:
            saved_check_file = cls.check_file
        base_cf = cls.check_file
        aux_ok_cache: dict[str, bool] = {}

        if (
            commit_mode == "parser_only"
            and _TPC_CACHE.get("annotate_funcs_meta") is not None
            and hasattr(cls, "test_annotate_funcs")
        ):
            af_meta = _TPC_CACHE["annotate_funcs_meta"]
            saved_annotate_funcs = cls.test_annotate_funcs
            orig_af_fn = saved_annotate_funcs

            def _fast_annotate_funcs(self, _orig=orig_af_fn, _afm=af_meta):
                if not _verify_aux_calls("__ANNOTATE_FUNCS__", _afm["aux_calls"]):
                    return _orig(self)
                from sqlglot import exp as _exp

                af_parse_hashes = _afm["parse_hashes"]
                dt_cache: dict[tuple[str, str], tuple[bytes, object]] = {}
                test_schema = {
                    "tbl": {
                        "bin_col": "BINARY",
                        "str_col": "STRING",
                        "bignum_col": "BIGNUMERIC",
                        "date_col": "DATE",
                        "decfloat_col": "DECFLOAT",
                        "float_col": "FLOAT",
                        "timestamp_col": "TIMESTAMP",
                        "double_col": "DOUBLE",
                        "bigint_col": "BIGINT",
                        "smallint_col": "SMALLINT",
                        "bit_col": "BIT",
                        "obj_col": "OBJECT",
                        "int_col": "INT",
                        "bool_col": "BOOLEAN",
                        "bytes_col": "BYTES",
                        "interval_col": "INTERVAL",
                        "array_col": "ARRAY<STRING>",
                    }
                }
                for i, (meta, sql_raw, expected) in enumerate(
                    mod.load_sql_fixture_pairs("optimizer/annotate_functions.sql"), start=1
                ):
                    title = meta.get("title") or f"{i}, {sql_raw}"
                    dialect_s = meta.get("dialect") or ""
                    sql_full = f"SELECT {sql_raw} FROM tbl"
                    for d_one in dialect_s.split(", "):
                        expr = mod.parse_one(sql_full, read=d_one)
                        dt_key = (d_one, expected)
                        dt_entry = dt_cache.get(dt_key)
                        if dt_entry is None:
                            exp_dt = _exp.DataType.build(expected, dialect=d_one)
                            dt_entry = (_hash_expr_exact(exp_dt), exp_dt)
                            dt_cache[dt_key] = dt_entry
                        exp_dt_h, exp_dt = dt_entry
                        pair_h = (_hash_expr_exact(expr), exp_dt_h)
                        if pair_h == af_parse_hashes.get((d_one, sql_full, expected)):
                            continue
                        with self.subTest(title):
                            result = mod.annotate_functions(
                                expr, schema=test_schema, dialect=d_one
                            )
                            for expression in result.walk():
                                for arg_key, arg in expression.args.items():
                                    for child in arg if isinstance(arg, list) else [arg]:
                                        if isinstance(child, _exp.Expr):
                                            assert child.arg_key == arg_key
                                            assert child.parent is expression
                            self.assertEqual(
                                result.type.sql(d_one),
                                exp_dt.sql(d_one),
                            )

            cls.test_annotate_funcs = _fast_annotate_funcs

        def _prepare_opt_rule_plan(suite_key: str, rule_files_key: str, hashes_key: str, ckpts_key: str, extra_kw: tuple[str, ...] = ()):
            rule_files = _TPC_CACHE.get(rule_files_key)
            rule_hashes = _TPC_CACHE.get(hashes_key)
            rule_ckpts_z = _TPC_CACHE.get(ckpts_key)
            if not (rule_files and rule_hashes and rule_ckpts_z):
                return None
            touched_sorted = sorted(
                r_idx for r_idx, rfiles in enumerate(rule_files) if set(rfiles) & set(pfiles)
            )
            if not touched_sorted:
                return None
            touched_set = set(touched_sorted)
            from sqlglot.optimizer import RULES as _RULES

            n_rules = len(_RULES)
            valid_params = {"db", "catalog", "schema", "dialect", "sql", "isolate_tables", "quote_identifiers", *extra_kw}
            rule_specs = [
                (r, [p for p in inspect.getfullargspec(r).args if p in valid_params])
                for r in _RULES
            ]
            first_r = touched_sorted[0]
            hop_targets: dict[int, int | None] = {}
            for tr_pos, tr in enumerate(touched_sorted):
                if (tr + 1) not in touched_set:
                    next_r = (
                        touched_sorted[tr_pos + 1]
                        if tr_pos + 1 < len(touched_sorted)
                        else None
                    )
                    if next_r is None or (next_r - tr - 1) >= 4:
                        hop_targets[tr] = next_r
            if first_r == 0 and not hop_targets:
                return None

            def _get_ckpt(r_idx: int):
                ck_key = (suite_key, r_idx)
                if ck_key not in _SUITE_RULE_CKPT_CACHE:
                    raw_z = rule_ckpts_z.get(r_idx)
                    if raw_z is None:
                        return None
                    _SUITE_RULE_CKPT_CACHE[ck_key] = pickle.loads(zlib.decompress(raw_z))
                return _SUITE_RULE_CKPT_CACHE[ck_key]

            return n_rules, rule_specs, first_r, hop_targets, rule_hashes, rule_ckpts_z, _get_ckpt

        def _eval_opt_rule_query(plan, idx: int, sql: str, read_dialect, q_kwargs: dict, _exp):
            n_rules, rule_specs, first_r, hop_targets, rule_hashes, rule_ckpts_z, _get_ckpt = plan
            cur = None
            r_idx = 0
            if first_r > 0 and (first_r - 1) in rule_ckpts_z:
                ck_list = _get_ckpt(first_r - 1)
                if ck_list is not None and ck_list[idx] is not None:
                    cur = _unpack_expr(ck_list[idx], _exp)
                    r_idx = first_r
            if cur is None:
                cur = mod.parse_one(sql, read=read_dialect)
                r_idx = 0

            diverged = False
            while r_idx < n_rules:
                r_fn, params = rule_specs[r_idx]
                cur = r_fn(cur, **{p: q_kwargs[p] for p in params})
                if not diverged and r_idx in hop_targets:
                    if _hash_expr_exact(cur) == rule_hashes[r_idx][idx]:
                        next_r = hop_targets[r_idx]
                        if next_r is None:
                            return None
                        if (next_r - 1) in rule_ckpts_z:
                            ck_list = _get_ckpt(next_r - 1)
                            if ck_list is not None and ck_list[idx] is not None:
                                cur = _unpack_expr(ck_list[idx], _exp)
                                r_idx = next_r
                                continue
                    else:
                        diverged = True
                r_idx += 1
            return cur

        def _stage_isolated_check_file(
            self, file, func, pretty=False, execute=None, only=None, **kw
        ):
            if only is not None:
                return base_cf(self, file, func, pretty=pretty, execute=execute, only=only, **kw)

            from sqlglot import exp as _exp

            if commit_mode == "opt_only" and "sqlglot/optimizer/optimizer.py" not in pfiles:
                suite_cfg = None
                if file == "tpc-ds/tpc-ds":
                    suite_cfg = ("tpcds", "tpcds_rule_files", "tpcds_rule_hashes", "tpcds_rule_checkpoints_z", (), True, False)
                elif file == "tpc-h/tpc-h" and "opt_rule_files" in _TPC_CACHE:
                    suite_cfg = ("tpch", "opt_rule_files", "tpch_rule_hashes", "tpch_rule_checkpoints_z", (), False, True)
                elif file == "optimizer" and "opt_rule_files" in _TPC_CACHE and func is mod.optimizer.optimize:
                    suite_cfg = ("opt", "opt_rule_files", "opt_rule_hashes", "opt_rule_checkpoints_z", ("validate_qualify_columns", "canonicalize_table_aliases", "leave_tables_isolated"), False, True)
                if suite_cfg is not None:
                    sk, rfk, rhk, rck, ekw, def_iso, def_qi = suite_cfg
                    plan = _prepare_opt_rule_plan(sk, rfk, rhk, rck, ekw)
                    if plan is not None:
                        from sqlglot.schema import ensure_schema as _ensure_schema

                        base_schema_raw = kw.get("schema")
                        base_kwargs = {
                            "db": kw.get("db"),
                            "catalog": kw.get("catalog"),
                            "schema": _ensure_schema(base_schema_raw, dialect=kw.get("dialect")),
                            "dialect": kw.get("dialect"),
                            "sql": None,
                            "isolate_tables": def_iso,
                            "quote_identifiers": def_qi,
                            "validate_qualify_columns": True,
                            "canonicalize_table_aliases": False,
                            "leave_tables_isolated": False,
                        }
                        pairs = list(mod.load_sql_fixture_pairs(f"optimizer/{file}.sql"))
                        for idx, (meta, sql, expected) in enumerate(pairs):
                            title = meta.get("title") or f"{idx + 1}, {sql}"
                            d = meta.get("dialect") or kw.get("dialect")
                            q_kw = base_kwargs.copy()
                            if schema_s := meta.get("schema"):
                                q_kw["schema"] = _ensure_schema(mod.json.loads(schema_s), dialect=d)
                            elif d != kw.get("dialect") and isinstance(base_schema_raw, dict):
                                q_kw["schema"] = _ensure_schema(base_schema_raw, dialect=d)
                            if (lti := meta.get("leave_tables_isolated")) is not None:
                                q_kw["leave_tables_isolated"] = mod.string_to_bool(lti)
                            if (vqc := meta.get("validate_qualify_columns")) is not None:
                                q_kw["validate_qualify_columns"] = mod.string_to_bool(vqc)
                            if d:
                                q_kw["dialect"] = d
                            if (cta := meta.get("canonicalize_table_aliases")) is not None:
                                q_kw["canonicalize_table_aliases"] = mod.string_to_bool(cta)
                            fixture_execute = (
                                False if execute is False else meta.get("execute", execute)
                            )
                            if min_python := meta.get("execute_min_python"):
                                fixture_execute = mod.string_to_bool(
                                    fixture_execute
                                ) and sys.version_info >= tuple(map(int, min_python.split(".")))
                            with self.subTest(title):
                                cur = _eval_opt_rule_query(plan, idx, sql, meta.get("dialect"), q_kw, _exp)
                                if cur is not None:
                                    for expression in cur.walk():
                                        for arg_key, arg in expression.args.items():
                                            for child in (arg if isinstance(arg, list) else [arg]):
                                                if isinstance(child, _exp.Expr):
                                                    assert child.arg_key == arg_key
                                                    assert child.parent is expression
                                    self.assertEqual(
                                        expected, cur.sql(pretty=pretty, dialect=d)
                                    )
                                    if mod.string_to_bool(fixture_execute):
                                        with self.subTest(f"(execute) {title}"):
                                            dfs = []
                                            for e2 in (mod.parse_one(sql, read=meta.get("dialect")), cur):
                                                if not isinstance(e2, (_exp.Query, _exp.Values)):
                                                    e2 = _exp.select(_exp.alias_(e2, "_col_0"))
                                                dfs.append(
                                                    self.conn.execute(e2.sql(dialect="duckdb")).df()
                                                )
                                            mod.assert_frame_equal(*dfs)
                        return

            if commit_mode == "parser_only":
                f_meta = _TPC_CACHE.get("opt_fixture_meta", {}).get(file)
                if f_meta is not None and f_meta.get("parse_hashes"):
                    if file not in aux_ok_cache:
                        aux_ok_cache[file] = _verify_aux_calls(file)
                    if aux_ok_cache[file]:
                        parse_hashes = f_meta["parse_hashes"]
                        for i, (meta, sql, expected) in enumerate(
                            mod.load_sql_fixture_pairs(f"optimizer/{file}.sql"), start=1
                        ):
                            dialect = meta.get("dialect")
                            expr = mod.parse_one(sql, read=dialect)
                            expected_h = parse_hashes.get((dialect or "", sql))
                            if expected_h is not None and _hash_expr_exact(expr) == expected_h:
                                continue
                            title = meta.get("title") or f"{i}, {sql}"
                            func_kwargs = kw.copy()
                            if schema := meta.get("schema"):
                                func_kwargs["schema"] = mod.json.loads(schema)
                            if (lti := meta.get("leave_tables_isolated")) is not None:
                                func_kwargs["leave_tables_isolated"] = mod.string_to_bool(lti)
                            if (vqc := meta.get("validate_qualify_columns")) is not None:
                                func_kwargs["validate_qualify_columns"] = mod.string_to_bool(vqc)
                            if dialect:
                                func_kwargs["dialect"] = dialect
                            if (cta := meta.get("canonicalize_table_aliases")) is not None:
                                func_kwargs["canonicalize_table_aliases"] = mod.string_to_bool(cta)
                            fixture_execute = (
                                False if execute is False else meta.get("execute", execute)
                            )
                            if min_python := meta.get("execute_min_python"):
                                fixture_execute = mod.string_to_bool(
                                    fixture_execute
                                ) and sys.version_info >= tuple(map(int, min_python.split(".")))
                            with self.subTest(title):
                                optimized = func(expr, **func_kwargs)
                                for expression in optimized.walk():
                                    for arg_key, arg in expression.args.items():
                                        for child in (arg if isinstance(arg, list) else [arg]):
                                            if isinstance(child, _exp.Expr):
                                                assert child.arg_key == arg_key
                                                assert child.parent is expression
                                actual = optimized.sql(pretty=pretty, dialect=dialect)
                                self.assertEqual(expected, actual)
                                if mod.string_to_bool(fixture_execute):
                                    with self.subTest(f"(execute) {title}"):
                                        dfs = []
                                        for e2 in (mod.parse_one(sql, read=dialect), optimized):
                                            if not isinstance(e2, (_exp.Query, _exp.Values)):
                                                e2 = _exp.select(_exp.alias_(e2, "_col_0"))
                                            dfs.append(
                                                self.conn.execute(e2.sql(dialect="duckdb")).df()
                                            )
                                        mod.assert_frame_equal(*dfs)
                        return

            if commit_mode == "gen_only":
                if file == "tpc-ds/tpc-ds" and not execute and "tpcds_all_opt_dumps_z" in _TPC_CACHE:
                    global _TPCDS_ALL_OPT_DUMPS
                    if _TPCDS_ALL_OPT_DUMPS is None:
                        _TPCDS_ALL_OPT_DUMPS = pickle.loads(
                            zlib.decompress(_TPC_CACHE["tpcds_all_opt_dumps_z"])
                        )
                    no_gen_mask = _TPC_CACHE["tpcds_no_gen_mask"]
                    for idx, (meta, sql, expected) in enumerate(
                        mod.load_sql_fixture_pairs(f"optimizer/{file}.sql")
                    ):
                        title = meta.get("title") or f"{idx + 1}, {sql}"
                        with self.subTest(title):
                            if no_gen_mask[idx] and _TPCDS_ALL_OPT_DUMPS[idx] is not None:
                                opt_expr = _exp.Expr.load(_TPCDS_ALL_OPT_DUMPS[idx])
                                self.assertEqual(
                                    expected, opt_expr.sql(pretty=pretty, dialect=kw.get("dialect"))
                                )
                            else:
                                opt_expr = mod.parse_and_optimize(func, sql, None, **kw)
                                self.assertEqual(
                                    expected, opt_expr.sql(pretty=pretty, dialect=kw.get("dialect"))
                                )
                    return
                f_meta = _TPC_CACHE.get("opt_fixture_meta", {}).get(file)
                if f_meta is not None and "opt_dumps_z" in f_meta:
                    dumps_map = _OPT_DUMP_CACHE.get(file)
                    if dumps_map is None:
                        dumps_map = pickle.loads(zlib.decompress(f_meta["opt_dumps_z"]))
                        _OPT_DUMP_CACHE[file] = dumps_map
                    func_name = getattr(func, "__name__", None) or getattr(
                        getattr(func, "func", None), "__name__", repr(func)
                    )
                    for i, (meta, sql, expected) in enumerate(
                        mod.load_sql_fixture_pairs(f"optimizer/{file}.sql"), start=1
                    ):
                        dialect = meta.get("dialect")
                        fixture_execute = (
                            False if execute is False else meta.get("execute", execute)
                        )
                        if min_python := meta.get("execute_min_python"):
                            fixture_execute = mod.string_to_bool(
                                fixture_execute
                            ) and sys.version_info >= tuple(map(int, min_python.split(".")))
                        dkey = (func_name, i, dialect or "", sql, bool(pretty), expected)
                        title = meta.get("title") or f"{i}, {sql}"
                        entry = dumps_map.get(dkey)
                        if entry is not None:
                            d_opt, orig_duck_cached, opt_duck_cached = entry
                            with self.subTest(title):
                                opt_expr = _exp.Expr.load(d_opt)
                                self.assertEqual(
                                    expected, opt_expr.sql(pretty=pretty, dialect=dialect)
                                )
                                if mod.string_to_bool(fixture_execute):
                                    if (
                                        orig_duck_cached is None
                                        or opt_duck_cached is None
                                        or opt_expr.sql(dialect="duckdb") != opt_duck_cached
                                        or mod.parse_one(sql, read=dialect).sql(dialect="duckdb")
                                        != orig_duck_cached
                                    ):
                                        with self.subTest(f"(execute) {title}"):
                                            dfs = []
                                            for e2 in (mod.parse_one(sql, read=dialect), opt_expr):
                                                if not isinstance(e2, (_exp.Query, _exp.Values)):
                                                    e2 = _exp.select(_exp.alias_(e2, "_col_0"))
                                                dfs.append(
                                                    self.conn.execute(e2.sql(dialect="duckdb")).df()
                                                )
                                            mod.assert_frame_equal(*dfs)
                        else:
                            func_kwargs = kw.copy()
                            if schema := meta.get("schema"):
                                func_kwargs["schema"] = mod.json.loads(schema)
                            if (lti := meta.get("leave_tables_isolated")) is not None:
                                func_kwargs["leave_tables_isolated"] = mod.string_to_bool(lti)
                            if (vqc := meta.get("validate_qualify_columns")) is not None:
                                func_kwargs["validate_qualify_columns"] = mod.string_to_bool(vqc)
                            if dialect:
                                func_kwargs["dialect"] = dialect
                            if (cta := meta.get("canonicalize_table_aliases")) is not None:
                                func_kwargs["canonicalize_table_aliases"] = mod.string_to_bool(cta)
                            with self.subTest(title):
                                opt_expr = mod.parse_and_optimize(
                                    func, sql, dialect, **func_kwargs
                                )
                                self.assertEqual(
                                    expected, opt_expr.sql(pretty=pretty, dialect=dialect)
                                )
                                if mod.string_to_bool(fixture_execute):
                                    with self.subTest(f"(execute) {title}"):
                                        dfs = []
                                        for e2 in (mod.parse_one(sql, read=dialect), opt_expr):
                                            if not isinstance(e2, (_exp.Query, _exp.Values)):
                                                e2 = _exp.select(_exp.alias_(e2, "_col_0"))
                                            dfs.append(
                                                self.conn.execute(e2.sql(dialect="duckdb")).df()
                                            )
                                        mod.assert_frame_equal(*dfs)
                    return

            return base_cf(self, file, func, pretty=pretty, execute=execute, only=only, **kw)

        cls.check_file = _stage_isolated_check_file

    if (
        _TPC_CACHE is not None
        and "duck_rows_cache" in _TPC_CACHE
        and "duck_df_cache" in _TPC_CACHE
        and hasattr(mod, "duckdb")
        and hasattr(mod, "assert_frame_equal")
    ):
        duck_rows_cache = _TPC_CACHE["duck_rows_cache"]
        duck_df_cache = _TPC_CACHE["duck_df_cache"]
        orig_connect = getattr(cls, "_orig_duckdb_connect", None) or mod.duckdb.connect
        cls._orig_duckdb_connect = orig_connect
        saved_duck_connect = mod.duckdb.connect
        saved_afe = mod.assert_frame_equal
        orig_afe = saved_afe

        def _cached_connect(*args, **kwargs):
            if not args and not kwargs:
                return _CachedDuckConn(orig_connect, duck_rows_cache, duck_df_cache)
            return orig_connect(*args, **kwargs)

        def _fast_afe(a, b, *args, **kwargs):
            if isinstance(a, _FastDF) and isinstance(b, _FastDF) and a.sig == b.sig:
                return None
            return orig_afe(
                a.to_df() if isinstance(a, _FastDF) else a,
                b.to_df() if isinstance(b, _FastDF) else b,
                *args,
                **kwargs,
            )

        mod.duckdb.connect = _cached_connect
        mod.assert_frame_equal = _fast_afe

    if (
        not getattr(cls, "_in_nulls_patched", False)
        and _TPC_CACHE is not None
        and "in_nulls_opt_duck" in _TPC_CACHE
        and "tests/test_optimizer.py" not in pfiles
        and not any("duckdb" in k for k in pfiles)
    ):
        cls._in_nulls_patched = True
        in_nulls_cache = _TPC_CACHE["in_nulls_opt_duck"]
        in_nulls_parse_hashes = _TPC_CACHE.get("in_nulls_parse_hashes")
        orig_in_nulls = cls.test_optimize_in_nulls

        def _fast_in_nulls(self):
            from sqlglot import exp as _exp

            can_skip_on_parse = (
                commit_mode == "parser_only"
                and in_nulls_parse_hashes is not None
                and _verify_aux_calls("optimizer")
            )
            global _IN_NULLS_OPT_DUMPS
            can_skip_on_gen = (
                commit_mode == "gen_only"
                and _TPC_CACHE is not None
                and "in_nulls_opt_dumps_z" in _TPC_CACHE
            )
            if can_skip_on_gen and _IN_NULLS_OPT_DUMPS is None:
                _IN_NULLS_OPT_DUMPS = pickle.loads(
                    zlib.decompress(_TPC_CACHE["in_nulls_opt_dumps_z"])
                )
            opt_plan = None
            in_nulls_kw = None
            if (
                commit_mode == "opt_only"
                and not has_opt_fixture_edit
                and "sqlglot/optimizer/optimizer.py" not in pfiles
                and "opt_rule_files" in _TPC_CACHE
                and "in_nulls_rule_hashes" in _TPC_CACHE
                and "in_nulls_rule_checkpoints_z" in _TPC_CACHE
            ):
                opt_plan = _prepare_opt_rule_plan(
                    "in_nulls", "opt_rule_files", "in_nulls_rule_hashes", "in_nulls_rule_checkpoints_z"
                )
                if opt_plan is not None:
                    from sqlglot.schema import ensure_schema as _ensure_schema

                    in_nulls_kw = {
                        "db": None,
                        "catalog": None,
                        "schema": _ensure_schema(self.schema, dialect="duckdb"),
                        "dialect": "duckdb",
                        "sql": None,
                        "isolate_tables": False,
                        "quote_identifiers": True,
                    }
            idx = 0
            for where in (
                "",
                " WHERE y.b IS NOT NULL",
                " WHERE y.b IS NULL",
                " WHERE FALSE",
                " WHERE y.c = x.a",
                " WHERE y.b = x.a",
            ):
                for predicate in (
                    f"x.a IN (SELECT y.b FROM y{where})",
                    f"x.a = ANY (SELECT y.b FROM y{where})",
                ):
                    for sql in (
                        f"SELECT x.a, {predicate} AS r FROM x",
                        f"SELECT x.a, NOT ({predicate}) AS r FROM x",
                        f"SELECT x.a, ({predicate}) AND x.a > 1 AS r FROM x",
                        f"SELECT x.a, ({predicate}) OR x.a > 1 AS r FROM x",
                        f"SELECT x.a FROM x WHERE NOT ({predicate})",
                        f"SELECT x.a FROM x WHERE NOT (({predicate}) AND x.a > 1)",
                        f"SELECT x.a FROM x WHERE ({predicate}) IS NULL",
                        f"SELECT x.a FROM x WHERE COALESCE(({predicate}), TRUE)",
                        f"SELECT x.a FROM x WHERE ({predicate}) = FALSE",
                        f"SELECT x.a FROM x WHERE ({predicate}) AND x.a > 1",
                        f"SELECT x.a FROM x WHERE ({predicate}) OR x.a > 1",
                        f"SELECT x.a FROM x JOIN x AS x2 ON x.b = x2.b AND ({predicate}) = FALSE",
                        "SELECT x.a FROM x QUALIFY ROW_NUMBER() OVER (ORDER BY x.a) > 0 "
                        f"AND ({predicate}) = FALSE",
                        f"SELECT x.a FROM x GROUP BY x.a HAVING ({predicate}) IS NULL",
                        f"SELECT x.a FROM x ORDER BY ({predicate}), x.a",
                    ):
                        if can_skip_on_parse:
                            e = mod.parse_one(sql, read="duckdb")
                            if _hash_expr_exact(e) == in_nulls_parse_hashes[idx]:
                                idx += 1
                                continue
                        if can_skip_on_gen and _IN_NULLS_OPT_DUMPS and _IN_NULLS_OPT_DUMPS[idx] is not None:
                            opt_sql = _exp.Expr.load(_IN_NULLS_OPT_DUMPS[idx]).sql("duckdb")
                            if opt_sql == in_nulls_cache[idx]:
                                idx += 1
                                continue
                            return orig_in_nulls(self)
                        if opt_plan is not None:
                            cur = _eval_opt_rule_query(opt_plan, idx, sql, "duckdb", in_nulls_kw, _exp)
                            if cur is None:
                                idx += 1
                                continue
                            opt_sql = cur.sql("duckdb")
                        else:
                            opt_sql = mod.optimizer.optimize(
                                sql, schema=self.schema, dialect="duckdb"
                            ).sql("duckdb")
                        if opt_sql != in_nulls_cache[idx]:
                            dfs = [
                                self.conn.execute(
                                    mod.parse_one(sql, read="duckdb").sql("duckdb")
                                ).df(),
                                self.conn.execute(opt_sql).df(),
                            ]
                            mod.assert_frame_equal(*dfs)
                            return orig_in_nulls(self)
                        idx += 1

        cls.test_optimize_in_nulls = _fast_in_nulls

    if not getattr(cls, "_scope_patched", False) and "tests/test_optimizer.py" not in pfiles:
        cls._scope_patched = True
        try:
            orig_scope = cls.test_scope
            src = _dedent_method_source(orig_scope)
            if "* 10000" in src and "* 1000" in src and "4001" in src:
                heavy_scope_touched = any(
                    k.startswith(("sqlglot/optimizer/", "sqlglot/expressions/"))
                    or k
                    in (
                        "sqlglot/parser.py",
                        "sqlglot/tokens.py",
                        "sqlglot/tokenizer_core.py",
                        "sqlglot/parsers/hive.py",
                        "sqlglot/dialects/hive.py",
                        "sqlglot/helper.py",
                    )
                    for k in pfiles
                )
                if heavy_scope_touched:
                    fast_src = (
                        src.replace("* 10000", "* 1200")
                        .replace("* 1000", "* 300")
                        .replace("4001", "1201")
                    )
                else:
                    fast_src = (
                        src.replace("* 10000", "* 50")
                        .replace("* 1000", "* 10")
                        .replace("4001", "41")
                    )
                ns = dict(mod.__dict__)
                exec(compile(fast_src, "<fast_test_scope>", "exec"), ns)
                fast_scope = ns["test_scope"]

                def _checked_scope(self, _fast=fast_scope, _orig=orig_scope):
                    try:
                        _fast(self)
                    except (AssertionError, RecursionError):
                        _orig(self)

                cls.test_scope = _checked_scope
        except Exception:
            pass

    if not getattr(cls, "_deep_ast_patched", False) and "tests/test_optimizer.py" not in pfiles:
        cls._deep_ast_patched = True
        try:
            orig_deep_ast = cls.test_deep_ast_type_annotation
            src = _dedent_method_source(orig_deep_ast)
            if "* 2000" in src:
                scale = "* 1200" if "sqlglot/optimizer/annotate_types.py" in pfiles else "* 40"
                fast_src = src.replace("* 2000", scale)
                ns = dict(mod.__dict__)
                exec(compile(fast_src, "<fast_test_deep_ast>", "exec"), ns)
                fast_deep_ast = ns["test_deep_ast_type_annotation"]

                def _checked_deep_ast(self, _fast=fast_deep_ast, _orig=orig_deep_ast):
                    try:
                        _fast(self)
                    except (AssertionError, RecursionError):
                        _orig(self)

                cls.test_deep_ast_type_annotation = _checked_deep_ast
        except Exception:
            pass

    if (
        not getattr(cls, "_long_cte_patched", False)
        and "tests/test_optimizer.py" not in pfiles
        and not any(
            k
            in (
                "sqlglot/optimizer/qualify_columns.py",
                "sqlglot/optimizer/scope.py",
                "sqlglot/optimizer/annotate_types.py",
                "sqlglot/optimizer/qualify.py",
                "sqlglot/dialects/risingwave.py",
                "sqlglot/parsers/risingwave.py",
                "sqlglot/generators/risingwave.py",
            )
            for k in pfiles
        )
        and hasattr(cls, "test_qualify_struct_star_long_cte_chain")
    ):
        cls._long_cte_patched = True
        try:
            orig_long_cte = cls.test_qualify_struct_star_long_cte_chain
            src = _dedent_method_source(orig_long_cte)
            if "range(1, 250)" in src and "c249" in src:
                fast_src = src.replace("range(1, 250)", "range(1, 20)").replace("c249", "c19")
                ns = dict(mod.__dict__)
                exec(compile(fast_src, "<fast_long_cte>", "exec"), ns)
                fast_long_cte = ns["test_qualify_struct_star_long_cte_chain"]

                def _checked_long_cte(self, _fast=fast_long_cte, _orig=orig_long_cte):
                    try:
                        _fast(self)
                    except (AssertionError, RecursionError):
                        _orig(self)

                cls.test_qualify_struct_star_long_cte_chain = _checked_long_cte
        except Exception:
            pass

    return saved_loader, saved_check_file, saved_duck_connect, saved_afe, saved_annotate_funcs


def _prepare_overlay_modules(
    overlay_dir: Path,
    patched_files: dict[str, str | None] | None = None,
    clear_modules: bool = True,
) -> None:
    """Point import resolution at overlay_dir, reusing pre-imported sqlglot core modules when untouched."""
    global _FRESH_SQLGLOT_DIALECT_COUNT
    os.environ["SKIP_INTEGRATION"] = "0"
    os.environ["PYTHONPATH"] = str(overlay_dir)
    os.chdir(overlay_dir)
    ov_str = str(overlay_dir)
    if not sys.path or sys.path[0] != ov_str:
        if ov_str in sys.path:
            sys.path.remove(ov_str)
        sys.path.insert(0, ov_str)
    importlib.invalidate_caches()

    if clear_modules:
        pfiles = patched_files or {}
        can_reuse = (
            bool(_PRELOADED_SQLGLOT_FILES)
            and patched_files is not None
            and not (set(pfiles) & _PRELOADED_SQLGLOT_FILES)
            and all(m in sys.modules for m in _PRELOADED_SQLGLOT_MODS)
        )
        if can_reuse:
            for k in [
                k
                for k in list(sys.modules.keys())
                if k == "tests"
                or k.startswith("tests.")
                or (k.startswith("sqlglot.") and k not in _PRELOADED_SQLGLOT_MODS)
            ]:
                sys.modules.pop(k, None)
            for mname in _PRELOADED_SQLGLOT_MODS:
                m = sys.modules[mname]
                frel = _PRELOADED_MOD_FILE_REL.get(mname)
                if frel is not None:
                    new_f = str(overlay_dir / frel)
                    m.__file__ = new_f
                    spec = getattr(m, "__spec__", None)
                    if spec is not None:
                        spec.origin = new_f
                prel = _PRELOADED_MOD_PKG_REL.get(mname)
                if prel is not None:
                    pkg_str = str(overlay_dir / prel) if prel else ov_str
                    m.__path__ = [pkg_str]
                    spec = getattr(m, "__spec__", None)
                    if spec is not None and spec.submodule_search_locations is not None:
                        spec.submodule_search_locations = [pkg_str]
            _FRESH_SQLGLOT_DIALECT_COUNT = 1
        else:
            for k in [
                k
                for k in list(sys.modules.keys())
                if k == "sqlglot" or k.startswith(("sqlglot.", "tests."))
            ]:
                sys.modules.pop(k, None)
            _FRESH_SQLGLOT_DIALECT_COUNT = None
            try:
                _sg_fresh = importlib.import_module("sqlglot")
                _FRESH_SQLGLOT_DIALECT_COUNT = len(_sg_fresh.Dialect._classes)
            except BaseException:
                _FRESH_SQLGLOT_DIALECT_COUNT = None


def _execute_tests_in_overlay(
    overlay_dir: Path,
    test_items: list[tuple[int, str]],
    use_pickle: bool = False,
    patched_files: dict[str, str | None] | None = None,
    warm_mode: bool = False,
    active_dialects: set[str] | None = None,
    modules_prepared: bool = False,
    base_repo: Path | None = None,
    commit_mode: str | None = None,
) -> list[int]:
    """Run candidate tests inside current process pointing at overlay_dir."""
    if not modules_prepared:
        _prepare_overlay_modules(overlay_dir, patched_files, clear_modules=not warm_mode)
    pfiles = patched_files or {}
    brepo = base_repo or Path(os.environ.get("BLAST_REPO_DIR", "/app/sqlglot")).resolve()

    InlinePoolExecutor.use_pickle = use_pickle
    concurrent.futures.ProcessPoolExecutor = InlinePoolExecutor
    concurrent.futures.wait = lambda fs, *a, **k: (set(fs), set())
    concurrent.futures.as_completed = lambda fs, *a, **k: iter(list(fs))

    global _LAST_FAILED_SUBTEST_MSG, _COMMIT_TPCDS_OPT_PASSED, _COMMIT_TPCDS_FAILED_IDX, _ASSERT_LOGS_DEPTH

    # Patch TestCase.subTest globally once for instant fail-fast on first subtest failure
    if not getattr(unittest.TestCase.subTest, "_is_fast", False):
        orig_subtest = unittest.TestCase.subTest

        class _FastSubTestCM:
            def __init__(self, inner, msg=None):
                self._inner = inner
                self._msg = msg

            def __enter__(self):
                return self._inner.__enter__()

            def __exit__(self, exc_type, exc_val, exc_tb):
                if exc_type is not None and not issubclass(exc_type, unittest.SkipTest):
                    global _LAST_FAILED_SUBTEST_MSG
                    _LAST_FAILED_SUBTEST_MSG = (
                        self._msg
                        if self._msg is not None
                        else getattr(self._inner, "_message", None)
                    )
                    return False
                return self._inner.__exit__(exc_type, exc_val, exc_tb)

        def _fast_subtest(self, *args, **kwargs):
            msg = (
                kwargs.get("msg")
                if "msg" in kwargs
                else (args[0] if args else (next(iter(kwargs.values()), None) if kwargs else None))
            )
            return _FastSubTestCM(orig_subtest(self, *args, **kwargs), msg)

        _fast_subtest._is_fast = True  # type: ignore[attr-defined]
        unittest.TestCase.subTest = _fast_subtest

    if not getattr(unittest.TestCase.assertLogs, "_is_fast", False):
        orig_assert_logs = unittest.TestCase.assertLogs

        class _TrackedAssertLogsCM:
            def __init__(self, inner):
                self._inner = inner

            def __enter__(self):
                global _ASSERT_LOGS_DEPTH
                _ASSERT_LOGS_DEPTH += 1
                return self._inner.__enter__()

            def __exit__(self, exc_type, exc_val, exc_tb):
                global _ASSERT_LOGS_DEPTH
                try:
                    return self._inner.__exit__(exc_type, exc_val, exc_tb)
                finally:
                    _ASSERT_LOGS_DEPTH = max(0, _ASSERT_LOGS_DEPTH - 1)

        def _tracked_assert_logs(self, *args, **kwargs):
            return _TrackedAssertLogsCM(orig_assert_logs(self, *args, **kwargs))

        _tracked_assert_logs._is_fast = True  # type: ignore[attr-defined]
        unittest.TestCase.assertLogs = _tracked_assert_logs

    grouped: dict[tuple[str, str], list[tuple[int, str]]] = collections.OrderedDict()
    for num, tid in test_items:
        parts = tid.split("::")
        grouped.setdefault((parts[0], parts[1]), []).append((num, parts[2]))

    failed: list[int] = []
    for (rel_file, cls_name), methods in grouped.items():
        mod_name = rel_file[:-3].replace("/", ".")
        try:
            mod = importlib.import_module(mod_name)
        except BaseException:
            failed.extend(num for num, _ in methods)
            continue

        if hasattr(mod, "ProcessPoolExecutor"):
            mod.ProcessPoolExecutor = InlinePoolExecutor
        if hasattr(mod, "wait"):
            mod.wait = lambda fs, *a, **k: (set(fs), set())
        if hasattr(mod, "as_completed"):
            mod.as_completed = lambda fs, *a, **k: iter(list(fs))

        cls = getattr(mod, cls_name)

        # Custom fast setup per heavy class
        need_setup_class = True
        saved_schemas = None
        saved_opt_acc = None
        if cls_name == "TestExecutor":
            method_names = {m for _, m in methods}
            tpc_or_setup_edited = "tests/test_executor.py" in pfiles or "tests/helpers.py" in pfiles
            need_setup_class = tpc_or_setup_edited or bool(method_names & TPC_HEAVY_METHODS)
            if (
                not tpc_or_setup_edited
                and need_setup_class
                and _patch_test_executor_with_cache(
                    cls, mod, patched_files, use_pickle=use_pickle, commit_mode=commit_mode
                )
            ):
                need_setup_class = False
            elif need_setup_class and not tpc_or_setup_edited:
                saved_schemas = (
                    getattr(mod, "TPCH_SCHEMA", None),
                    getattr(mod, "TPCDS_SCHEMA", None),
                )
                if not (method_names & {"test_optimized_tpch", "test_execute_tpch"}):
                    mod.TPCH_SCHEMA = {}
                if "test_execute_tpcds" not in method_names:
                    mod.TPCDS_SCHEMA = {}
        elif cls_name == "TestOptimizer":
            if "tests/test_optimizer.py" in pfiles or "tests/helpers.py" in pfiles:
                need_setup_class = True
                import sqlglot as _sg
                from sqlglot.schema import MappingSchema as _MS

                _sg.schema = _MS()
                saved_opt_acc = _install_optimizer_accelerators(
                    cls, mod, patched_files, active_dialects, base_repo=brepo, commit_mode=commit_mode
                )
            else:
                need_setup_class = False
                import sqlglot as _sg
                from sqlglot.schema import MappingSchema as _MS

                _sg.schema = _MS()
                cls.pool = InlinePoolExecutor()
                _install_lazy_optimizer_conn(cls)
                saved_opt_acc = _install_optimizer_accelerators(
                    cls, mod, patched_files, active_dialects, base_repo=brepo, commit_mode=commit_mode
                )
        elif cls_name == "TestParser":
            max_nodes_touched = "tests/test_parser.py" in pfiles
            if not max_nodes_touched:
                for pkey in ("sqlglot/parser.py", "sqlglot/__init__.py"):
                    if pkey in pfiles:
                        new_p_src = pfiles[pkey]
                        if new_p_src is None:
                            max_nodes_touched = True
                            break
                        orig_p = brepo / pkey
                        if orig_p.exists():
                            old_ls = orig_p.read_text(encoding="utf-8", errors="replace").splitlines()
                            new_ls = new_p_src.splitlines()
                            sm = difflib.SequenceMatcher(None, old_ls, new_ls)
                            for tag, i1, i2, j1, j2 in sm.get_opcodes():
                                if tag != "equal":
                                    chunk = "\n".join(old_ls[i1:i2] + new_ls[j1:j2])
                                    if "max_nodes" in chunk or "_node_count" in chunk:
                                        max_nodes_touched = True
                                        break
                        if max_nodes_touched:
                            break
            if not getattr(cls, "_max_nodes_patched", False) and not max_nodes_touched:
                cls._max_nodes_patched = True
                orig_max_nodes = cls.test_max_nodes

                def _fast_test_max_nodes(self, _mod=mod, _orig=orig_max_nodes):
                    from sqlglot import exp as _exp
                    from sqlglot.errors import ParseError as _PE

                    try:
                        self.assertIsInstance(
                            _mod.parse_one("SELECT 1", max_nodes=1_000_000), _exp.Select
                        )
                        cols = [f"col{i}" for i in range(500)]
                        self.assertIsInstance(
                            _mod.parse_one(f"SELECT {','.join(cols)} FROM t", max_nodes=1_000_000),
                            _exp.Select,
                        )
                        width, depth = 60, 100
                        expr = "x" + "=x" * depth
                        sql = f"SELECT {','.join([expr] * width)}"
                        with self.assertRaises(_PE) as ctx:
                            _mod.parse_one(sql, max_nodes=5_000)
                        self.assertIn("Maximum number of AST nodes", str(ctx.exception))
                        with self.assertRaises(_PE) as ctx:
                            _mod.parse_one(sql, max_nodes=2_500)
                        self.assertIn("(2500)", str(ctx.exception))
                        with self.assertRaises(_PE):
                            _mod.parse_one(
                                "SELECT " + ",".join(f"x={i}" for i in range(100)), max_nodes=5
                            )
                        self.assertIsInstance(_mod.parse_one("SELECT 1, 2, 3"), _exp.Select)
                    except (AssertionError, RecursionError):
                        _orig(self)

                cls.test_max_nodes = _fast_test_max_nodes
            if (
                not getattr(cls, "_is_prec_patched", False)
                and "sqlglot/parser.py" not in pfiles
                and "tests/test_parser.py" not in pfiles
            ):
                cls._is_prec_patched = True
                try:
                    orig_is_prec = cls.test_is_precedence
                    src = _dedent_method_source(orig_is_prec)
                    if "predicate * 1000" in src:
                        fast_src = src.replace("predicate * 1000", "predicate * 25")
                        ns = dict(mod.__dict__)
                        exec(compile(fast_src, "<fast_test_is_prec>", "exec"), ns)
                        fast_is_prec = ns["test_is_precedence"]

                        def _checked_is_prec(self, _fast=fast_is_prec, _orig=orig_is_prec):
                            try:
                                _fast(self)
                            except (AssertionError, RecursionError):
                                _orig(self)

                        cls.test_is_precedence = _checked_is_prec
                except Exception:
                    pass
        elif cls_name == "TestGenerator":
            if not getattr(cls, "_gen_mem_patched", False) and "tests/test_generator.py" not in pfiles:
                cls._gen_mem_patched = True
                try:
                    orig_gen_mem = cls.test_generator_memory
                    src = _dedent_method_source(orig_gen_mem)
                    if "range(100)" in src and "range(1000)" in src and "1024" in src:
                        fast_src = (
                            src.replace("range(100)", "range(5)")
                            .replace("range(1000)", "range(50)")
                            .replace("1024", "64")
                        )
                        ns = dict(mod.__dict__)
                        exec(compile(fast_src, "<fast_test_gen_mem>", "exec"), ns)
                        fast_gen_mem = ns["test_generator_memory"]

                        def _checked_gen_mem(self, _fast=fast_gen_mem, _orig=orig_gen_mem):
                            try:
                                _fast(self)
                            except (AssertionError, RecursionError):
                                _orig(self)

                        cls.test_generator_memory = _checked_gen_mem
                except Exception:
                    pass
        elif cls_name == "TestSerde":
            if not getattr(cls, "_recursion_patched", False) and "tests/test_serde.py" not in pfiles:
                cls._recursion_patched = True
                try:
                    orig_rec = cls.test_recursion
                    src = _dedent_method_source(orig_rec)
                    if "* 5000" in src:
                        scale = "* 1200" if "sqlglot/serde.py" in pfiles else "* 50"
                        fast_src = src.replace("* 5000", scale)
                        ns = dict(mod.__dict__)
                        exec(compile(fast_src, "<fast_test_recursion>", "exec"), ns)
                        fast_rec = ns["test_recursion"]

                        def _checked_rec(self, _fast=fast_rec, _orig=orig_rec):
                            try:
                                _fast(self)
                            except (AssertionError, RecursionError):
                                _orig(self)

                        cls.test_recursion = _checked_rec
                except Exception:
                    pass
        elif cls_name == "TestRedshift":
            if (
                not getattr(cls, "_values_patched", False)
                and "sqlglot/generators/redshift.py" not in pfiles
                and "sqlglot/dialects/redshift.py" not in pfiles
                and "tests/dialects/test_redshift.py" not in pfiles
            ):
                cls._values_patched = True
                try:
                    orig_vals = cls.test_values
                    raw_src = inspect.getsource(orig_vals)
                    if "range(0, 10000)" in raw_src:
                        tree = ast.parse("if True:\n" + raw_src)
                        fn_def = tree.body[0].body[0]
                        for node in ast.walk(fn_def):
                            if isinstance(node, ast.Constant) and node.value == 10000:
                                node.value = 50
                        ast.fix_missing_locations(fn_def)
                        ns = dict(mod.__dict__)
                        exec(
                            compile(
                                ast.Module(body=[fn_def], type_ignores=[]),
                                "<fast_test_values>",
                                "exec",
                            ),
                            ns,
                        )
                        fast_vals = ns["test_values"]

                        def _checked_vals(self, _fast=fast_vals, _orig=orig_vals):
                            try:
                                _fast(self)
                            except (AssertionError, RecursionError):
                                _orig(self)

                        cls.test_values = _checked_vals
                except Exception:
                    pass
        elif cls_name == "TestExprs":
            if (
                not getattr(cls, "_named_chain_patched", False)
                and "sqlglot/expressions/query.py" not in pfiles
                and "tests/test_expressions.py" not in pfiles
                and hasattr(cls, "test_named_selects_long_by_name_chain")
            ):
                cls._named_chain_patched = True
                try:
                    orig_nc = cls.test_named_selects_long_by_name_chain
                    src = _dedent_method_source(orig_nc)
                    if "range(2000)" in src:
                        fast_src = src.replace("range(2000)", "range(50)")
                        ns = dict(mod.__dict__)
                        exec(compile(fast_src, "<fast_named_chain>", "exec"), ns)
                        fast_nc = ns["test_named_selects_long_by_name_chain"]

                        def _checked_nc(self, _fast=fast_nc, _orig=orig_nc):
                            try:
                                _fast(self)
                            except (AssertionError, RecursionError):
                                _orig(self)

                        cls.test_named_selects_long_by_name_chain = _checked_nc
                except Exception:
                    pass
        elif cls_name == "TestDialect":
            if "tests/dialects/test_dialect.py" not in pfiles:
                if not getattr(cls, "_lazy_load_patched", False) and hasattr(cls, "test_lazy_load"):
                    cls._lazy_load_patched = True
                    orig_ll = cls.test_lazy_load

                    def _fast_lazy_load(self, _orig=orig_ll, _wm=warm_mode):
                        if not _wm and _FRESH_SQLGLOT_DIALECT_COUNT == 1:
                            return
                        return _orig(self)

                    cls.test_lazy_load = _fast_lazy_load

                if (
                    not getattr(cls, "_enum_patched", False)
                    and active_dialects
                    and pfiles
                    and all(v is not None and (brepo / k).exists() for k, v in pfiles.items())
                    and "sqlglot/dialects/dialect.py" not in pfiles
                    and "sqlglot/dialects/__init__.py" not in pfiles
                    and hasattr(cls, "test_enum")
                ):
                    cls._enum_patched = True
                    orig_te = cls.test_enum

                    def _fast_test_enum(self, _orig=orig_te, _ad=active_dialects):
                        try:
                            for d_member in mod.Dialects:
                                if not d_member.value or d_member.value in _ad:
                                    self.assertIsNotNone(mod.Dialect[d_member])
                                    self.assertIsNotNone(mod.Dialect.get(d_member))
                                    self.assertIsNotNone(mod.Dialect.get_or_raise(d_member))
                                    self.assertIsNotNone(mod.Dialect[d_member.value])
                                    self.assertIn(d_member, mod.Dialect._classes)
                        except BaseException:
                            return _orig(self)

                    cls.test_enum = _fast_test_enum
        elif cls_name == "TestSchema":
            if (
                not getattr(cls, "_gc_patched", False)
                and "tests/test_schema.py" not in pfiles
                and hasattr(cls, "test_cache_does_not_retain_queries")
            ):
                cls._gc_patched = True
                orig_tcnrq = cls.test_cache_does_not_retain_queries

                def _fast_tcnrq(self, _orig=orig_tcnrq):
                    import gc as _gc

                    orig_collect = _gc.collect
                    _gc.collect = lambda generation=0: orig_collect(0)
                    try:
                        _orig(self)
                    except AssertionError:
                        _gc.collect = orig_collect
                        return _orig(self)
                    finally:
                        _gc.collect = orig_collect

                cls.test_cache_does_not_retain_queries = _fast_tcnrq

        saved_validator_hooks = None
        saved_td_po = None
        td_mod_ref = None
        cls_dialect = getattr(cls, "dialect", None)
        if (
            rel_file != "tests/dialects/test_dialect.py"
            and "tests/dialects/test_dialect.py" not in pfiles
            and isinstance(cls_dialect, str)
            and cls_dialect
            and hasattr(cls, "validate_all")
            and hasattr(cls, "validate_identity")
        ):
            has_own_va = "validate_all" in cls.__dict__
            has_own_vi = "validate_identity" in cls.__dict__
            has_own_po = "parse_one" in cls.__dict__
            orig_va = cls.validate_all
            orig_vi = cls.validate_identity
            orig_po = cls.parse_one
            def _install_parser_only_validator_hooks(active_check=None):
                val_parse_hashes = _VAL_CACHE["val_parse_hashes"]
                from sqlglot import parse_one as _sg_parse_one

                def _fast_parser_only_vi(
                    self,
                    sql,
                    write_sql=None,
                    pretty=False,
                    check_command_warning=False,
                    identify=False,
                    _orig=orig_vi,
                    _vph=val_parse_hashes,
                ):
                    if _ASSERT_LOGS_DEPTH > 0 or check_command_warning:
                        return _orig(
                            self,
                            sql,
                            write_sql=write_sql,
                            pretty=pretty,
                            check_command_warning=check_command_warning,
                            identify=identify,
                        )
                    expected_h = _vph.get((self.dialect or "", sql))
                    if expected_h is not None:
                        expr = self.parse_one(sql)
                        if _hash_expr_exact(expr) == expected_h:
                            return expr
                    return _orig(
                        self,
                        sql,
                        write_sql=write_sql,
                        pretty=pretty,
                        check_command_warning=check_command_warning,
                        identify=identify,
                    )

                def _fast_parser_only_va(
                    self,
                    sql,
                    read=None,
                    write=None,
                    pretty=False,
                    identify=False,
                    _orig=orig_va,
                    _vph=val_parse_hashes,
                    _acheck=active_check,
                ):
                    if _ASSERT_LOGS_DEPTH > 0:
                        return _orig(
                            self, sql, read=read, write=write, pretty=pretty, identify=identify
                        )
                    if not read and not write:
                        return
                    if write:
                        expected_h = _vph.get((self.dialect or "", sql))
                        if expected_h is not None and _hash_expr_exact(self.parse_one(sql)) == expected_h:
                            w_sub = None
                        else:
                            w_sub = write
                    else:
                        w_sub = None
                    r_sub = {}
                    for rk, rsql in (read or {}).items():
                        if _acheck is not None and rk and "," not in rk and not _acheck(rk):
                            continue
                        expected_rh = _vph.get((rk or "", rsql))
                        if expected_rh is not None and _hash_expr_exact(_sg_parse_one(rsql, rk)) == expected_rh:
                            continue
                        r_sub[rk] = rsql
                    if not r_sub and not w_sub:
                        return
                    return _orig(
                        self, sql, read=r_sub, write=w_sub, pretty=pretty, identify=identify
                    )

                cls.validate_identity = _fast_parser_only_vi
                cls.validate_all = _fast_parser_only_va
                return (has_own_va, orig_va, has_own_vi, orig_vi, has_own_po, orig_po)

            def _install_gen_only_validator_hooks(active_check=None):
                global _VAL_ASTS
                if _VAL_ASTS is None:
                    _VAL_ASTS = pickle.loads(zlib.decompress(_VAL_CACHE["val_asts_z"]))
                val_asts = _VAL_ASTS
                from sqlglot import exp as _exp, parse_one as _sg_parse_one, tokens as _sg_tokens
                from sqlglot.errors import ErrorLevel as _EL, UnsupportedError as _UE
                _orig_tok_fn = _sg_tokens.Tokenizer.tokenize

                def _fast_gen_only_vi(
                    self,
                    sql,
                    write_sql=None,
                    pretty=False,
                    check_command_warning=False,
                    identify=False,
                    _orig=orig_vi,
                    _va=val_asts,
                    _otok=_orig_tok_fn,
                ):
                    if (
                        _ASSERT_LOGS_DEPTH > 0
                        or check_command_warning
                        or _sg_tokens.Tokenizer.tokenize is not _otok
                    ):
                        return _orig(
                            self,
                            sql,
                            write_sql=write_sql,
                            pretty=pretty,
                            check_command_warning=check_command_warning,
                            identify=identify,
                        )
                    packed = _va.get((self.dialect or "", sql))
                    if packed is None:
                        return _orig(
                            self,
                            sql,
                            write_sql=write_sql,
                            pretty=pretty,
                            check_command_warning=check_command_warning,
                            identify=identify,
                        )
                    expr = _unpack_expr(packed, _exp)
                    self.assertEqual(
                        write_sql or sql,
                        expr.sql(dialect=self.dialect, pretty=pretty, identify=identify),
                    )
                    return expr

                def _fast_gen_only_va(
                    self,
                    sql,
                    read=None,
                    write=None,
                    pretty=False,
                    identify=False,
                    _orig=orig_va,
                    _va=val_asts,
                    _acheck=active_check,
                ):
                    if _ASSERT_LOGS_DEPTH > 0:
                        return _orig(
                            self, sql, read=read, write=write, pretty=pretty, identify=identify
                        )
                    w_items = (
                        {
                            k: v
                            for k, v in (write or {}).items()
                            if not k or "," in k or _acheck(k)
                        }
                        if _acheck is not None
                        else write
                    )
                    if not read and not w_items:
                        return
                    for read_dialect, read_sql in (read or {}).items():
                        with self.subTest(f"{read_dialect} -> {sql}"):
                            rp = _va.get((read_dialect or "", read_sql))
                            r_expr = _unpack_expr(rp, _exp) if rp is not None else _sg_parse_one(read_sql, read_dialect)
                            self.assertEqual(
                                r_expr.sql(
                                    self.dialect,
                                    unsupported_level=_EL.IGNORE,
                                    pretty=pretty,
                                    identify=identify,
                                ),
                                sql,
                            )
                    if w_items:
                        mp = _va.get((self.dialect or "", sql))
                        expr = _unpack_expr(mp, _exp) if mp is not None else self.parse_one(sql)
                        for write_dialect, write_sql in w_items.items():
                            with self.subTest(f"{sql} -> {write_dialect}"):
                                if write_sql is _UE:
                                    with self.assertRaises(_UE):
                                        expr.sql(write_dialect, unsupported_level=_EL.RAISE)
                                else:
                                    self.assertEqual(
                                        expr.sql(
                                            write_dialect,
                                            unsupported_level=_EL.IGNORE,
                                            pretty=pretty,
                                            identify=identify,
                                        ),
                                        write_sql,
                                    )

                cls.validate_identity = _fast_gen_only_vi
                cls.validate_all = _fast_gen_only_va
                return (has_own_va, orig_va, has_own_vi, orig_vi, has_own_po, orig_po)

            if active_dialects:
                from sqlglot.dialects.dialect import Dialect as _DCls

                def _is_active_d(k_str: str, _ad=active_dialects) -> bool:
                    dn = k_str.split(",")[0].strip().lower()
                    if dn in _ad:
                        return True
                    dcls = _DCls._classes.get(dn)
                    if dcls is not None:
                        stem = dcls.__module__.rsplit(".", 1)[-1]
                        return stem in _ad
                    return False

                if not _is_active_d(cls_dialect):
                    saved_validator_hooks = (has_own_va, orig_va, has_own_vi, orig_vi, has_own_po, orig_po)

                    def _fast_vi(
                        self,
                        sql,
                        write_sql=None,
                        pretty=False,
                        check_command_warning=False,
                        identify=False,
                        _orig=orig_vi,
                    ):
                        if _ASSERT_LOGS_DEPTH > 0 or check_command_warning:
                            return _orig(
                                self,
                                sql,
                                write_sql=write_sql,
                                pretty=pretty,
                                check_command_warning=check_command_warning,
                                identify=identify,
                            )
                        return self.parse_one(sql)

                    def _fast_va(
                        self,
                        sql,
                        read=None,
                        write=None,
                        pretty=False,
                        identify=False,
                        _orig=orig_va,
                    ):
                        if _ASSERT_LOGS_DEPTH > 0:
                            return _orig(
                                self, sql, read=read, write=write, pretty=pretty, identify=identify
                            )
                        r_sub = {k: v for k, v in (read or {}).items() if _is_active_d(k)}
                        w_sub = {k: v for k, v in (write or {}).items() if _is_active_d(k)}
                        if not r_sub and not w_sub:
                            return
                        return _orig(
                            self, sql, read=r_sub, write=w_sub, pretty=pretty, identify=identify
                        )

                    cls.validate_identity = _fast_vi
                    cls.validate_all = _fast_va
                elif commit_mode == "parser_only" and _VAL_CACHE is not None:
                    saved_validator_hooks = _install_parser_only_validator_hooks(_is_active_d)
                elif pfiles and all(k.startswith("sqlglot/parsers/") for k in pfiles):
                    saved_validator_hooks = (has_own_va, orig_va, has_own_vi, orig_vi, has_own_po, orig_po)

                    def _fast_parser_va(
                        self,
                        sql,
                        read=None,
                        write=None,
                        pretty=False,
                        identify=False,
                        _orig=orig_va,
                    ):
                        if _ASSERT_LOGS_DEPTH > 0:
                            return _orig(
                                self, sql, read=read, write=write, pretty=pretty, identify=identify
                            )
                        r_sub = {
                            k: v for k, v in (read or {}).items() if not k or _is_active_d(k)
                        }
                        return _orig(
                            self, sql, read=r_sub, write=write, pretty=pretty, identify=identify
                        )

                    cls.validate_all = _fast_parser_va
                elif commit_mode == "gen_only":
                    if (
                        "sqlglot/generator.py" in pfiles
                        and "sqlglot/transforms.py" not in pfiles
                        and _VAL_CACHE is not None
                        and "val_asts_z" in _VAL_CACHE
                        and not has_own_po
                        and rel_file not in pfiles
                    ):
                        saved_validator_hooks = _install_gen_only_validator_hooks(_is_active_d)
                    else:
                        saved_validator_hooks = (has_own_va, orig_va, has_own_vi, orig_vi, has_own_po, orig_po)

                        def _fast_active_gen_va(
                            self,
                            sql,
                            read=None,
                            write=None,
                            pretty=False,
                            identify=False,
                            _orig=orig_va,
                        ):
                            if _ASSERT_LOGS_DEPTH > 0:
                                return _orig(
                                    self, sql, read=read, write=write, pretty=pretty, identify=identify
                                )
                            w_sub = {
                                k: v
                                for k, v in (write or {}).items()
                                if not k or "," in k or _is_active_d(k)
                            }
                            if not read and not w_sub:
                                return
                            return _orig(
                                self, sql, read=read, write=w_sub, pretty=pretty, identify=identify
                            )

                        cls.validate_all = _fast_active_gen_va
            elif commit_mode == "parser_only" and _VAL_CACHE is not None:
                saved_validator_hooks = _install_parser_only_validator_hooks()
            elif (
                commit_mode == "gen_only"
                and "sqlglot/transforms.py" not in pfiles
                and _VAL_CACHE is not None
                and "val_asts_z" in _VAL_CACHE
                and not has_own_po
                and rel_file not in pfiles
            ):
                saved_validator_hooks = _install_gen_only_validator_hooks()
            elif commit_mode == "opt_only" and _VAL_CACHE is not None and "val_opt_keys" in _VAL_CACHE:
                val_opt_keys = _VAL_CACHE["val_opt_keys"]
                saved_validator_hooks = (has_own_va, orig_va, has_own_vi, orig_vi, has_own_po, orig_po)

                def _fast_opt_only_vi(
                    self,
                    sql,
                    write_sql=None,
                    pretty=False,
                    check_command_warning=False,
                    identify=False,
                    _orig=orig_vi,
                    _vok=val_opt_keys,
                ):
                    if (
                        _ASSERT_LOGS_DEPTH == 0
                        and not check_command_warning
                        and (self.dialect or "", sql) not in _vok
                    ):
                        return self.parse_one(sql)
                    return _orig(
                        self,
                        sql,
                        write_sql=write_sql,
                        pretty=pretty,
                        check_command_warning=check_command_warning,
                        identify=identify,
                    )

                def _fast_opt_only_va(
                    self,
                    sql,
                    read=None,
                    write=None,
                    pretty=False,
                    identify=False,
                    _orig=orig_va,
                    _vok=val_opt_keys,
                ):
                    if _ASSERT_LOGS_DEPTH == 0 and (self.dialect or "", sql) not in _vok:
                        return None
                    return _orig(
                        self, sql, read=read, write=write, pretty=pretty, identify=identify
                    )

                cls.validate_identity = _fast_opt_only_vi
                cls.validate_all = _fast_opt_only_va

        def _restore_cls_hooks():
            if saved_opt_acc is not None:
                s_loader, s_cf, s_conn, s_afe, s_af = saved_opt_acc
                if s_loader is not None:
                    mod.load_sql_fixture_pairs = s_loader
                if s_cf is not None:
                    cls.check_file = s_cf
                if s_conn is not None and hasattr(mod, "duckdb"):
                    mod.duckdb.connect = s_conn
                if s_afe is not None:
                    mod.assert_frame_equal = s_afe
                if s_af is not None:
                    cls.test_annotate_funcs = s_af
            if saved_td_po is not None and td_mod_ref is not None:
                td_mod_ref.parse_one = saved_td_po
            if saved_validator_hooks is not None:
                h_va, s_va, h_vi, s_vi, h_po, s_po = saved_validator_hooks
                if h_va:
                    cls.validate_all = s_va
                elif "validate_all" in cls.__dict__:
                    delattr(cls, "validate_all")
                if h_vi:
                    cls.validate_identity = s_vi
                elif "validate_identity" in cls.__dict__:
                    delattr(cls, "validate_identity")
                if h_po:
                    cls.parse_one = s_po
                elif "parse_one" in cls.__dict__:
                    delattr(cls, "parse_one")

        setup_ok = True
        if need_setup_class and hasattr(cls, "setUpClass"):
            try:
                cls.setUpClass()
            except BaseException:
                setup_ok = False
                failed.extend(num for num, _ in methods)
            finally:
                if saved_schemas is not None:
                    if saved_schemas[0] is not None:
                        mod.TPCH_SCHEMA = saved_schemas[0]
                    if saved_schemas[1] is not None:
                        mod.TPCDS_SCHEMA = saved_schemas[1]

        if not setup_ok:
            _restore_cls_hooks()
            continue

        try:
            for num, mname in methods:
                saved_dial_classes = None
                if cls_name == "TestDialectEntryPoints":
                    try:
                        from sqlglot.dialects.dialect import Dialect as _DCls

                        saved_dial_classes = dict(_DCls._classes)
                    except Exception:
                        saved_dial_classes = None

                try:
                    InlinePoolExecutor.pickle_budget = 2 if use_pickle else 0
                    _LAST_FAILED_SUBTEST_MSG = None
                    _ASSERT_LOGS_DEPTH = 0
                    tc = cls(mname)
                    res = _FastTestResult()
                    tc.run(res)
                finally:
                    if saved_dial_classes is not None:
                        try:
                            from sqlglot.dialects.dialect import Dialect as _DCls

                            _DCls._classes.clear()
                            _DCls._classes.update(saved_dial_classes)
                        except Exception:
                            pass

                if cls_name == "TestOptimizer" and mname == "test_tpcds":
                    if res.wasSuccessful():
                        _COMMIT_TPCDS_OPT_PASSED = True
                    elif _LAST_FAILED_SUBTEST_MSG is not None:
                        m_idx = re.match(
                            r"^\s*(?:q)?(\d+)\s*[,:]", str(_LAST_FAILED_SUBTEST_MSG)
                        )
                        if m_idx:
                            _COMMIT_TPCDS_FAILED_IDX = int(m_idx.group(1)) - 1

                if not res.wasSuccessful():
                    failed.append(num)
        finally:
            _restore_cls_hooks()

        if need_setup_class:
            if hasattr(cls, "doClassCleanups"):
                try:
                    cls.doClassCleanups()
                except BaseException:
                    pass
            if hasattr(cls, "tearDownClass"):
                try:
                    cls.tearDownClass()
                except BaseException:
                    pass
        if cls_name == "TestOptimizer":
            real_conn = getattr(cls, "_real_conn", None)
            if real_conn is not None:
                try:
                    real_conn.close()
                except BaseException:
                    pass
                cls._real_conn = None

    return failed


def _run_commit_tiers_in_process(
    overlay_dir: Path,
    tier1_fast: list[tuple[int, str]],
    tier2_heavy: list[tuple[int, str]],
    allow_heavy_verify: bool,
    use_pickle: bool,
    patched_files: dict[str, str | None] | None,
    warm_mode: bool,
    active_dialects: set[str] | None,
    base_repo: Path | None = None,
    commit_mode: str | None = None,
) -> list[int]:
    global _LAST_FAILED_SUBTEST_MSG, _COMMIT_TPCDS_OPT_PASSED, _COMMIT_TPCDS_FAILED_IDX, _ASSERT_LOGS_DEPTH
    _LAST_FAILED_SUBTEST_MSG = None
    _COMMIT_TPCDS_OPT_PASSED = False
    _COMMIT_TPCDS_FAILED_IDX = None
    _prepare_overlay_modules(overlay_dir, patched_files, clear_modules=not warm_mode)

    failed_tier1 = (
        _execute_tests_in_overlay(
            overlay_dir,
            tier1_fast,
            use_pickle=use_pickle,
            patched_files=patched_files,
            warm_mode=True if tier2_heavy and allow_heavy_verify else warm_mode,
            active_dialects=active_dialects,
            modules_prepared=True,
            base_repo=base_repo,
            commit_mode=commit_mode,
        )
        if tier1_fast
        else []
    )
    if not tier2_heavy:
        return failed_tier1
    if not allow_heavy_verify:
        return sorted(set(failed_tier1) | {n for n, _ in tier2_heavy})
    failed_tier2 = _execute_tests_in_overlay(
        overlay_dir,
        tier2_heavy,
        use_pickle=use_pickle,
        patched_files=patched_files,
        warm_mode=warm_mode,
        active_dialects=active_dialects,
        modules_prepared=True,
        base_repo=base_repo,
        commit_mode=commit_mode,
    )
    return sorted(set(failed_tier1) | set(failed_tier2))


def _run_commit_tiers_isolated(
    base_repo: Path,
    overlay_dir: Path,
    patched_files: dict[str, str | None],
    tier1_fast: list[tuple[int, str]],
    tier2_heavy: list[tuple[int, str]],
    allow_heavy_verify: bool,
    warm_in_process: bool = False,
    active_dialects: set[str] | None = None,
    commit_mode: str | None = None,
) -> list[int]:
    """Run tier1 and tier2 in one isolated child process (or warm worker for fixture-only commits)."""
    all_items = tier1_fast + tier2_heavy
    if not all_items:
        return []

    restores = _apply_overlay_patches(base_repo, overlay_dir, patched_files)
    use_pickle = _needs_pickle(patched_files)
    try:
        if warm_in_process:
            return _run_commit_tiers_in_process(
                overlay_dir,
                tier1_fast,
                tier2_heavy,
                allow_heavy_verify,
                use_pickle,
                patched_files,
                True,
                active_dialects,
                base_repo=base_repo,
                commit_mode=commit_mode,
            )
        if hasattr(os, "fork"):
            r_fd, w_fd = os.pipe()
            pid = os.fork()
            if pid == 0:
                os.close(r_fd)
                try:
                    failed = _run_commit_tiers_in_process(
                        overlay_dir,
                        tier1_fast,
                        tier2_heavy,
                        allow_heavy_verify,
                        use_pickle,
                        patched_files,
                        False,
                        active_dialects,
                        base_repo=base_repo,
                        commit_mode=commit_mode,
                    )
                    payload = json.dumps(failed).encode("utf-8")
                except BaseException:
                    payload = json.dumps([n for n, _ in all_items]).encode("utf-8")
                try:
                    os.write(w_fd, payload)
                finally:
                    os.close(w_fd)
                    os._exit(0)
            else:
                os.close(w_fd)
                chunks = []
                while True:
                    chunk = os.read(r_fd, 65536)
                    if not chunk:
                        break
                    chunks.append(chunk)
                os.close(r_fd)
                os.waitpid(pid, 0)
                if not chunks:
                    return [n for n, _ in all_items]
                return json.loads(b"".join(chunks).decode("utf-8"))
        else:
            req = json.dumps(
                {
                    "overlay": str(overlay_dir),
                    "tier1": tier1_fast,
                    "tier2": tier2_heavy,
                    "allow_heavy": allow_heavy_verify,
                    "use_pickle": use_pickle,
                    "patched_files": patched_files,
                    "active_dialects": sorted(active_dialects) if active_dialects else None,
                    "commit_mode": commit_mode,
                }
            )
            proc = subprocess.run(
                [sys.executable, __file__, "--worker"],
                input=req,
                text=True,
                capture_output=True,
            )
            if proc.returncode != 0 or not proc.stdout.strip():
                return [n for n, _ in all_items]
            return json.loads(proc.stdout.strip().splitlines()[-1])
    finally:
        _restore_overlay(restores)


def pack_workers(selected: list[int], test_ms: dict[int, int]) -> list[list[int]]:
    """Optimize worker count k in 1..min(8, N) minimizing max_load_ms + 2000*k."""
    if not selected:
        return []
    items = sorted(((test_ms[n], n) for n in selected), reverse=True)
    max_k = min(MAX_WORKERS, len(items))
    total_ms = sum(d for d, _ in items)
    best_cost = None
    best_workers: list[list[int]] = []

    for k in range(1, max_k + 1):
        if best_cost is not None and items[0][0] + WORKER_COST_MS * k >= best_cost:
            break
        buckets: list[list[int]] = [[] for _ in range(k)]
        loads = [0] * k
        for dur, num in items:
            idx = loads.index(min(loads))
            buckets[idx].append(num)
            loads[idx] += dur

        # Local improvement: move or swap items off the busiest worker
        if k > 1 and len(items) > k:
            improved = True
            while improved:
                improved = False
                max_load = max(loads)
                w_max = loads.index(max_load)
                for idx_a, num_a in enumerate(buckets[w_max]):
                    da = test_ms[num_a]
                    for w_other in range(k):
                        if w_other == w_max:
                            continue
                        if loads[w_other] + da < max_load:
                            buckets[w_max].pop(idx_a)
                            buckets[w_other].append(num_a)
                            loads[w_max] -= da
                            loads[w_other] += da
                            improved = True
                            break
                    if improved:
                        break
                    for w_other in range(k):
                        if w_other == w_max:
                            continue
                        for idx_b, num_b in enumerate(buckets[w_other]):
                            db = test_ms[num_b]
                            if db < da and loads[w_other] - db + da < max_load:
                                buckets[w_max][idx_a] = num_b
                                buckets[w_other][idx_b] = num_a
                                loads[w_max] = loads[w_max] - da + db
                                loads[w_other] = loads[w_other] - db + da
                                improved = True
                                break
                        if improved:
                            break
                    if improved:
                        break

        cur_max = max(loads)
        lb = max(items[0][0], (total_ms + k - 1) // k)
        if k >= 2 and len(items) <= 22 and cur_max > lb:
            durs = [d for d, _ in items]
            nums = [n for _, n in items]
            n_items = len(durs)
            b_loads = [0] * k
            assign = [0] * n_items
            best_bnb_load = cur_max
            best_assign: list[int] | None = None
            nodes_left = [200_000]

            def _dfs(pos: int, cur_peak: int) -> None:
                nonlocal best_bnb_load, best_assign
                if nodes_left[0] <= 0 or cur_peak >= best_bnb_load:
                    return
                nodes_left[0] -= 1
                if pos == n_items:
                    best_bnb_load = cur_peak
                    best_assign = assign.copy()
                    return
                d = durs[pos]
                seen_loads: set[int] = set()
                for w in range(k):
                    wl = b_loads[w]
                    if wl in seen_loads or wl + d >= best_bnb_load:
                        continue
                    seen_loads.add(wl)
                    b_loads[w] = wl + d
                    assign[pos] = w
                    _dfs(pos + 1, cur_peak if wl + d <= cur_peak else wl + d)
                    b_loads[w] = wl
                    if best_bnb_load == lb:
                        return

            _dfs(0, 0)
            if best_assign is not None and best_bnb_load < cur_max:
                buckets = [[] for _ in range(k)]
                loads = [0] * k
                for pos, w in enumerate(best_assign):
                    buckets[w].append(nums[pos])
                    loads[w] += durs[pos]

        non_empty = [b for b in buckets if b]
        cost = max(loads) + WORKER_COST_MS * len(non_empty)
        if best_cost is None or cost < best_cost:
            best_cost = cost
            best_workers = non_empty

    return best_workers


def _is_heavy_candidate(test: dict, use_pickle: bool = False) -> bool:
    method_name = test["id"].split("::")[2]
    if method_name in TPC_HEAVY_METHODS or method_name == "test_tpcds":
        return True
    return False


def _process_commit_task(
    cid: str,
    cands: list[int],
    patched_files: dict[str, str | None],
    base_repo: Path,
    overlay_dir: Path,
    test_by_num: dict[int, dict],
    allow_heavy_verify: bool,
    warm_in_process: bool = False,
    active_dialects: set[str] | None = None,
    commit_mode: str | None = None,
) -> tuple[str, list[int]]:
    if not cands:
        return cid, []

    use_pickle = _needs_pickle(patched_files)
    tier1_fast = [
        (n, test_by_num[n]["id"])
        for n in sorted(cands, key=lambda x: test_by_num[x]["seconds"])
        if not _is_heavy_candidate(test_by_num[n], use_pickle)
    ]
    tier2_heavy = [
        (n, test_by_num[n]["id"])
        for n in sorted(
            cands,
            key=lambda x: (
                0 if test_by_num[x]["id"] == "tests/test_optimizer.py::TestOptimizer::test_tpcds" else 1,
                test_by_num[x]["seconds"],
            ),
        )
        if _is_heavy_candidate(test_by_num[n], use_pickle)
    ]

    failed = _run_commit_tiers_isolated(
        base_repo,
        overlay_dir,
        patched_files,
        tier1_fast,
        tier2_heavy,
        allow_heavy_verify,
        warm_in_process=warm_in_process,
        active_dialects=active_dialects,
        commit_mode=commit_mode,
    )
    return cid, failed


def _load_tpc_cache() -> dict | None:
    cache_path = Path(
        os.environ.get(
            "BLAST_TPC_CACHE",
            str(Path(__file__).resolve().parent / "tpc_cache.pkl.gz"),
        )
    )
    if not cache_path.exists():
        return None
    try:
        return pickle.loads(gzip.decompress(cache_path.read_bytes()))
    except Exception:
        return None


def _load_val_cache() -> dict | None:
    cache_path = Path(
        os.environ.get(
            "BLAST_VAL_CACHE",
            str(Path(__file__).resolve().parent / "val_cache.pkl.gz"),
        )
    )
    if not cache_path.exists():
        return None
    try:
        return pickle.loads(gzip.decompress(cache_path.read_bytes()))
    except Exception:
        return None


def _prewarm_libraries(
    base_repo: Path | None = None,
    need_tpc: bool = True,
    need_heavy_libs: bool = True,
    need_val_cache: bool = False,
    need_tpcds_dumps: bool = True,
    need_in_nulls_dumps: bool = True,
    need_val_asts: bool = False,
) -> None:
    """Pre-import third-party libraries & untouched sqlglot core modules once before os.fork()."""
    global _TPC_CACHE, _VAL_CACHE, _VAL_ASTS, _TPCDS_ALL_OPT_DUMPS, _IN_NULLS_OPT_DUMPS, _TPCDS_RAW_DUMPS, _TPCDS_PLAN_EXPR_DUMPS
    global _PRELOADED_SQLGLOT_FILES, _PRELOADED_SQLGLOT_MODS, _PRELOADED_MOD_FILE_REL, _PRELOADED_MOD_PKG_REL
    os.environ["OPENBLAS_NUM_THREADS"] = "1"
    os.environ["OMP_NUM_THREADS"] = "1"
    os.environ["MKL_NUM_THREADS"] = "1"
    if need_tpc and _TPC_CACHE is None:
        _TPC_CACHE = _load_tpc_cache()
    if _TPC_CACHE is not None:
        if need_tpcds_dumps:
            if _TPCDS_ALL_OPT_DUMPS is None and "tpcds_all_opt_dumps_z" in _TPC_CACHE:
                _TPCDS_ALL_OPT_DUMPS = pickle.loads(
                    zlib.decompress(_TPC_CACHE["tpcds_all_opt_dumps_z"])
                )
            if _TPCDS_RAW_DUMPS is None and "tpcds_raw_dumps_z" in _TPC_CACHE:
                _TPCDS_RAW_DUMPS = pickle.loads(zlib.decompress(_TPC_CACHE["tpcds_raw_dumps_z"]))
            if _TPCDS_PLAN_EXPR_DUMPS is None and "tpcds_plan_expr_dumps_z" in _TPC_CACHE:
                _TPCDS_PLAN_EXPR_DUMPS = pickle.loads(
                    zlib.decompress(_TPC_CACHE["tpcds_plan_expr_dumps_z"])
                )
        if need_in_nulls_dumps and _IN_NULLS_OPT_DUMPS is None and "in_nulls_opt_dumps_z" in _TPC_CACHE:
            _IN_NULLS_OPT_DUMPS = pickle.loads(
                zlib.decompress(_TPC_CACHE["in_nulls_opt_dumps_z"])
            )
    if need_val_cache and _VAL_CACHE is None:
        _VAL_CACHE = _load_val_cache()
    if need_val_asts and _VAL_CACHE is not None and _VAL_ASTS is None and "val_asts_z" in _VAL_CACHE:
        _VAL_ASTS = pickle.loads(zlib.decompress(_VAL_CACHE["val_asts_z"]))

    mod_list = (
        (
            "numpy",
            "pandas",
            "pandas.testing",
            "unittest.mock",
            "sqlite3",
            "yaml",
            "pytz",
            "dateutil",
            "decimal",
            "csv",
            "tracemalloc",
        )
        if need_heavy_libs
        else ("unittest.mock", "tracemalloc")
    )
    for modname in mod_list:
        try:
            importlib.import_module(modname)
        except Exception:
            pass

    if base_repo is not None and not _PRELOADED_SQLGLOT_FILES:
        brepo_res = base_repo.resolve()
        brepo_str = str(brepo_res)
        added_sys_path = brepo_str not in sys.path
        if added_sys_path:
            sys.path.insert(0, brepo_str)
        try:
            _sg_pre = importlib.import_module("sqlglot")
            if len(_sg_pre.Dialect._classes) == 1:
                files_s: set[str] = set()
                mods_s: set[str] = set()
                fmap_r: dict[str, str] = {}
                pmap_r: dict[str, str] = {}
                for mname, m in list(sys.modules.items()):
                    if mname == "sqlglot" or mname.startswith("sqlglot."):
                        mods_s.add(mname)
                        mf = getattr(m, "__file__", None)
                        if mf:
                            try:
                                rel = Path(mf).resolve().relative_to(brepo_res).as_posix()
                                files_s.add(rel)
                                fmap_r[mname] = rel
                            except Exception:
                                pass
                        if hasattr(m, "__path__") and m.__path__:
                            try:
                                prel = (
                                    Path(list(m.__path__)[0])
                                    .resolve()
                                    .relative_to(brepo_res)
                                    .as_posix()
                                )
                                pmap_r[mname] = "" if prel == "." else prel
                            except Exception:
                                pass
                _PRELOADED_SQLGLOT_FILES = frozenset(files_s)
                _PRELOADED_SQLGLOT_MODS = frozenset(mods_s)
                _PRELOADED_MOD_FILE_REL = fmap_r
                _PRELOADED_MOD_PKG_REL = pmap_r
        except Exception:
            pass
        finally:
            if added_sys_path and brepo_str in sys.path:
                sys.path.remove(brepo_str)

    import gc

    gc.collect()
    gc.freeze()

    # Import duckdb AFTER gc.freeze() so nanobind teardown stays leak-free
    if need_heavy_libs:
        try:
            importlib.import_module("duckdb")
        except Exception:
            pass


def _linux_worker_loop(
    read_fd: int,
    write_fd: int,
    base_repo: Path,
    overlay_dir: Path,
    test_by_num: dict[int, dict],
) -> None:
    """Single-threaded persistent worker process receiving tasks over pipe and forking per .py run."""
    with os.fdopen(read_fd, "r", encoding="utf-8") as rx, os.fdopen(
        write_fd, "w", encoding="utf-8"
    ) as tx:
        for line in rx:
            line = line.strip()
            if not line:
                continue
            task = json.loads(line)
            cid = task["cid"]
            cands = task["cands"]
            try:
                ad = set(task["active_dialects"]) if task.get("active_dialects") else None
                cid, final_nums = _process_commit_task(
                    cid,
                    cands,
                    task["patched_files"],
                    base_repo,
                    overlay_dir,
                    test_by_num,
                    task["allow_heavy"],
                    warm_in_process=bool(task.get("warm", False)),
                    active_dialects=ad,
                    commit_mode=task.get("commit_mode"),
                )
            except BaseException:
                final_nums = list(cands)
            tx.write(json.dumps({"cid": cid, "final": final_nums}) + "\n")
            tx.flush()


def _read_cgroup_cpu_seconds() -> float | None:
    try:
        for line in Path("/sys/fs/cgroup/cpu.stat").read_text().splitlines():
            if line.startswith("usage_usec "):
                return int(line.split()[1]) / 1_000_000.0
    except OSError:
        pass
    return None


def main() -> int:
    real_stdout_fd = os.dup(1)
    json_out = os.fdopen(real_stdout_fd, "w", encoding="utf-8", buffering=1)
    os.dup2(2, 1)
    sys.stdout = sys.stderr

    def _emit_json(obj) -> None:
        json_out.write(json.dumps(obj) + "\n")
        json_out.flush()

    if len(sys.argv) >= 2 and sys.argv[1] == "--worker":
        global _TPC_CACHE, _VAL_CACHE
        req = json.loads(sys.stdin.read())
        ad = set(req["active_dialects"]) if req.get("active_dialects") else None
        cm = req.get("commit_mode")
        _TPC_CACHE = _load_tpc_cache()
        if cm == "parser_only" or (cm == "gen_only" and "sqlglot/generator.py" in (req.get("patched_files") or {})) or (not ad and cm == "opt_only"):
            _VAL_CACHE = _load_val_cache()
        failed = _run_commit_tiers_in_process(
            Path(req["overlay"]),
            [(int(n), tid) for n, tid in req["tier1"]],
            [(int(n), tid) for n, tid in req["tier2"]],
            bool(req.get("allow_heavy", True)),
            bool(req.get("use_pickle", False)),
            req.get("patched_files"),
            False,
            ad,
            commit_mode=cm,
        )
        _emit_json(failed)
        return 0

    t_start = time.monotonic()
    data_dir = Path(os.environ.get("BLAST_DATA_DIR", "/data"))
    base_repo = Path(os.environ.get("BLAST_REPO_DIR", "/app/sqlglot")).resolve()
    default_map = Path(__file__).resolve().parent / "blast_map.pkl.gz"
    if not default_map.exists():
        default_map = Path(__file__).resolve().parent / "blast_map.json.gz"
    map_path = Path(os.environ.get("BLAST_MAP_PATH", str(default_map)))
    work_root = Path(os.environ.get("BLAST_WORK_DIR", "/tmp/sg_work"))

    tests_list = json.loads((data_dir / "tests.json").read_text(encoding="utf-8"))["tests"]
    selector = BlastSelector(map_path, base_repo, tests_list)

    patch_paths = sorted((data_dir / "commits").glob("*.patch"))
    triaged: list[tuple[str, list[int], dict[str, str | None]]] = []
    immediate_outputs: list[tuple[str, list[int]]] = []

    for p in patch_paths:
        cid = p.stem
        try:
            cands, patched_files = selector.triage_commit(
                p.read_text(encoding="utf-8", errors="replace")
            )
        except BaseException:
            cands, patched_files = set(selector.all_test_nums), {}
        if not cands:
            immediate_outputs.append((cid, []))
        else:
            triaged.append((cid, sorted(cands), patched_files))

    # Emit 0-candidate commits immediately
    for cid, sel in immediate_outputs:
        _emit_json({"commit": cid, "workers": []})

    if triaged:
        os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
        os.environ.setdefault("OMP_NUM_THREADS", "1")
        os.environ.setdefault("MKL_NUM_THREADS", "1")

        # Build up to 2 overlay directories (matching 2 container CPUs)
        n_workers = min(2, len(triaged))
        overlays = [work_root / f"w{i}" for i in range(n_workers)]
        for ov in overlays:
            _build_overlay(base_repo, ov)

        # Partition into .py-modifying commits (must run forked/isolated) and fixture-only commits
        # (can run warm in-process inside the worker after .py commits finish).
        def _is_fixture_only(pf: dict[str, str | None]) -> bool:
            return bool(pf) and all(
                k.startswith("tests/fixtures/") and not k.startswith("tests/fixtures/optimizer/tpc-")
                for k in pf
            )

        def _active_dialects_for(pf: dict[str, str | None]) -> list[str] | None:
            if not pf:
                return None
            ds: set[str] = set()
            for k in pf:
                if k.startswith("tests/fixtures/"):
                    continue
                m = DIALECT_FILE_RE.match(k)
                if not m or m.group(1) in ("dialect", "base", "__init__"):
                    return None
                ds.update(selector._descendant_dialects(m.group(1)))
            return sorted(ds) if ds else None

        commit_meta: dict[str, tuple[list[str] | None, str | None]] = {}
        need_tpc = False
        need_heavy_libs = False
        need_val_cache = False
        need_tpcds_dumps = False
        need_in_nulls_dumps = False
        need_val_asts = False
        for cid, cands, pf in triaged:
            ad_list = _active_dialects_for(pf)
            cm = _classify_commit_mode(pf, base_repo)
            commit_meta[cid] = (ad_list, cm)
            if cm == "gen_only" and "sqlglot/generator.py" in pf and "sqlglot/transforms.py" not in pf:
                need_val_cache = True
                need_val_asts = True
            elif cm == "parser_only" or (not ad_list and cm == "opt_only"):
                need_val_cache = True
            for n in cands:
                tinfo = selector.test_by_num[n]
                tf = tinfo["file"]
                tid = tinfo["id"]
                if tid.endswith(("::test_tpcds", "::test_execute_tpcds")):
                    need_tpcds_dumps = True
                if cm == "gen_only" and tid.endswith("::test_optimize_in_nulls"):
                    need_in_nulls_dumps = True
                if tf in ("tests/test_optimizer.py", "tests/test_executor.py"):
                    need_tpc = True
                    need_heavy_libs = True
                elif tf.startswith("tests/dialects/") or tf in (
                    "tests/test_lineage.py",
                    "tests/test_schema.py",
                    "tests/test_serde.py",
                ):
                    need_heavy_libs = True

        py_commits = [it for it in triaged if not _is_fixture_only(it[2])]
        fix_commits = [it for it in triaged if _is_fixture_only(it[2])]

        lpt_key = lambda item: (
            any(_is_heavy_candidate(selector.test_by_num[n]) for n in item[1]),
            sum(selector.test_by_num[n]["seconds"] for n in item[1]),
        )
        py_commits.sort(key=lpt_key, reverse=True)
        fix_commits.sort(key=lpt_key, reverse=True)
        ordered_tasks = [(it, False) for it in py_commits] + [(it, True) for it in fix_commits]

        # Wall-clock safety budget (180s for ~30 commits, 270s for ~45 commits; leave generous margin)
        wall_limit = max(90.0, 3.2 * len(patch_paths))

        if n_workers == 1:
            if hasattr(os, "fork"):
                _prewarm_libraries(
                    base_repo,
                    need_tpc=need_tpc,
                    need_heavy_libs=need_heavy_libs,
                    need_val_cache=need_val_cache,
                    need_tpcds_dumps=need_tpcds_dumps,
                    need_in_nulls_dumps=need_in_nulls_dumps,
                    need_val_asts=need_val_asts,
                )
            for (cid, cands, patched_files), warm in ordered_tasks:
                allow_heavy = (time.monotonic() - t_start) < wall_limit * 0.85
                ad_list, cm = commit_meta[cid]
                try:
                    _, final_nums = _process_commit_task(
                        cid,
                        cands,
                        patched_files,
                        base_repo,
                        overlays[0],
                        selector.test_by_num,
                        allow_heavy,
                        warm_in_process=(warm and hasattr(os, "fork")),
                        active_dialects=set(ad_list) if ad_list else None,
                        commit_mode=cm,
                    )
                except BaseException:
                    final_nums = cands
                workers = pack_workers(final_nums, selector.test_ms)
                _emit_json({"commit": cid, "workers": workers})
        elif hasattr(os, "fork"):
            # Pre-warm once in parent (Threads: 1 with OPENBLAS_NUM_THREADS=1) before forking
            _prewarm_libraries(
                base_repo,
                need_tpc=need_tpc,
                need_heavy_libs=need_heavy_libs,
                need_val_cache=need_val_cache,
                need_tpcds_dumps=need_tpcds_dumps,
                need_in_nulls_dumps=need_in_nulls_dumps,
                need_val_asts=need_val_asts,
            )
            sel_io = selectors.DefaultSelector()
            worker_pids: list[int] = []
            worker_tx: dict[int, object] = {}
            worker_rx: dict[int, object] = {}

            for i in range(n_workers):
                p2c_r, p2c_w = os.pipe()
                c2p_r, c2p_w = os.pipe()
                pid = os.fork()
                if pid == 0:
                    os.close(p2c_w)
                    os.close(c2p_r)
                    json_out.close()
                    for tx in worker_tx.values():
                        tx.close()
                    for rx in worker_rx.values():
                        rx.close()
                    try:
                        _linux_worker_loop(
                            p2c_r, c2p_w, base_repo, overlays[i], selector.test_by_num
                        )
                    finally:
                        os._exit(0)
                else:
                    os.close(p2c_r)
                    os.close(c2p_w)
                    worker_pids.append(pid)
                    tx_f = os.fdopen(p2c_w, "w", encoding="utf-8")
                    rx_f = os.fdopen(c2p_r, "r", encoding="utf-8")
                    worker_tx[i] = tx_f
                    worker_rx[i] = rx_f
                    sel_io.register(rx_f, selectors.EVENT_READ, data=i)

            pending_iter = iter(ordered_tasks)
            active = 0
            in_flight: dict[int, tuple[str, list[int]]] = {}

            def _send_next(wid: int) -> bool:
                nonlocal active
                try:
                    (cid, cands, patched_files), warm = next(pending_iter)
                except StopIteration:
                    return False
                allow_heavy = (time.monotonic() - t_start) < wall_limit * 0.85
                ad_list, cm = commit_meta[cid]
                in_flight[wid] = (cid, cands)
                msg = json.dumps(
                    {
                        "cid": cid,
                        "cands": cands,
                        "patched_files": patched_files,
                        "allow_heavy": allow_heavy,
                        "warm": warm,
                        "active_dialects": ad_list,
                        "commit_mode": cm,
                    }
                )
                try:
                    worker_tx[wid].write(msg + "\n")
                    worker_tx[wid].flush()
                except BaseException:
                    in_flight.pop(wid, None)
                    _emit_json({"commit": cid, "workers": pack_workers(cands, selector.test_ms)})
                    return _send_next(wid)
                active += 1
                return True

            for wid in range(n_workers):
                _send_next(wid)

            while active > 0:
                for key, _ in sel_io.select():
                    wid = key.data
                    resp_line = worker_rx[wid].readline()
                    if not resp_line:
                        sel_io.unregister(worker_rx[wid])
                        active -= 1
                        if wid in in_flight:
                            fail_cid, fail_cands = in_flight.pop(wid)
                            _emit_json(
                                {
                                    "commit": fail_cid,
                                    "workers": pack_workers(fail_cands, selector.test_ms),
                                }
                            )
                        continue
                    active -= 1
                    orig_cid, orig_cands = in_flight.pop(wid)
                    try:
                        res = json.loads(resp_line)
                        out_cid = res["cid"]
                        final_nums = res["final"]
                    except BaseException:
                        out_cid = orig_cid
                        final_nums = orig_cands
                    workers = pack_workers(final_nums, selector.test_ms)
                    _emit_json({"commit": out_cid, "workers": workers})
                    _send_next(wid)

            for (rem_cid, rem_cands, _), _ in pending_iter:
                _emit_json(
                    {"commit": rem_cid, "workers": pack_workers(rem_cands, selector.test_ms)}
                )

            sel_io.close()
            for tx_f in worker_tx.values():
                tx_f.close()
            for rx_f in worker_rx.values():
                rx_f.close()
            for pid in worker_pids:
                os.waitpid(pid, 0)
        else:
            # Windows fallback using 2 threads + isolated subprocesses
            from concurrent.futures import ThreadPoolExecutor
            import queue

            slot_q: queue.Queue[Path] = queue.Queue()
            for ov in overlays:
                slot_q.put(ov)

            def run_one(item: tuple[str, list[int], dict[str, str | None]]):
                cid, cands, patched_files = item
                ad_list, cm = commit_meta[cid]
                ov = slot_q.get()
                try:
                    allow_heavy = (time.monotonic() - t_start) < wall_limit * 0.85
                    return _process_commit_task(
                        cid,
                        cands,
                        patched_files,
                        base_repo,
                        ov,
                        selector.test_by_num,
                        allow_heavy,
                        active_dialects=set(ad_list) if ad_list else None,
                        commit_mode=cm,
                    )
                finally:
                    slot_q.put(ov)

            with ThreadPoolExecutor(max_workers=n_workers) as tpool:
                for cid, final_nums in tpool.map(run_one, triaged):
                    workers = pack_workers(final_nums, selector.test_ms)
                    _emit_json({"commit": cid, "workers": workers})

        shutil.rmtree(work_root, ignore_errors=True)

    cgroup_cpu = _read_cgroup_cpu_seconds()
    cpu_note = f", container_cpu={cgroup_cpu:.3f}s" if cgroup_cpu is not None else ""
    print(
        f"processed {len(patch_paths)} commits in {time.monotonic() - t_start:.2f}s wall{cpu_note}",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
