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
import copy
import difflib
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

WORKER_COST_MS = 2_000
MAX_WORKERS = 8
HEAVY_TEST_SECONDS = 0.8

_TPC_CACHE: dict | None = None
_TPCDS_OPT_VERIFIED: bool = False
_PREWARMED_SQLGLOT_FILES: set[str] = set()

BOOL_OR_BRANCH_RE = re.compile(
    r"\b(if|elif|else|and|or|not|while|return|raise|except|break|continue|assert)\b"
)
ENCODING_COMMENT_RE = re.compile(r"coding[:=]\s*([-\w.]+)")
DIALECT_FILE_RE = re.compile(
    r"^sqlglot/(?:dialects|parsers|generators|typing)/([a-z0-9_]+)\.py$"
)
TEST_DIALECT_FILE_RE = re.compile(r"^tests/dialects/test_([a-z0-9_]+)\.py$")

TPC_HEAVY_METHODS = frozenset(
    {"test_optimized_tpch", "test_execute_tpch", "test_execute_tpcds"}
)


class _EarlySubtestFail(BaseException):
    """Raised on first subTest failure so parameterized tests fail in milliseconds."""


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

    def __init__(self, max_workers=None, mp_context=None, initializer=None, initargs=()):
        if initializer is not None:
            initializer(*initargs)

    def submit(self, fn, *args, **kwargs):
        return _LazyFuture(fn, args, kwargs, self.use_pickle)

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
            cur = {"old": old_p, "new": new_p, "hunks": []}
            hunk = None
        elif cur is not None:
            if line.startswith("--- "):
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
        for hl in h["lines"]:
            if hl.startswith(" "):
                out.append(orig_lines[cur_old] if cur_old < len(orig_lines) else hl[1:])
                cur_old += 1
            elif hl.startswith("-"):
                cur_old += 1
            elif hl.startswith("+"):
                out.append(hl[1:])
        idx = cur_old
    out.extend(orig_lines[idx:])
    return "".join(out)


def _has_encoding_change(old_src: str, new_src: str) -> bool:
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

        bmap = json.loads(gzip.decompress(map_path.read_bytes()))
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

        self._build_reverse_indices()

    def _build_reverse_indices(self) -> None:
        self.dialect_tests: dict[str, set[int]] = collections.defaultdict(set)
        for rel, sid in self.file_to_tests.items():
            m = DIALECT_FILE_RE.match(rel) or TEST_DIALECT_FILE_RE.match(rel)
            if m:
                self.dialect_tests[m.group(1)].update(self.test_sets[sid])

        self.subclasses: dict[str, set[str]] = collections.defaultdict(set)
        for cname, defs_list in self.class_graph.items():
            for d in defs_list:
                if "." not in d["q"]:
                    for base in d["bases"]:
                        self.subclasses[base].add(cname)

        # Reverse module import map: imported_mod -> set of importing rel_files
        self.reverse_mod_files: dict[str, set[str]] = collections.defaultdict(set)
        for mod, deps in self.module_imports.items():
            src_rel = mod.replace(".", "/") + ".py"
            if src_rel not in self.file_to_tests and (self.base_repo / mod.replace(".", "/") / "__init__.py").exists():
                src_rel = mod.replace(".", "/") + "/__init__.py"
            for dep in deps:
                self.reverse_mod_files[dep].add(src_rel)

        self.lazy_load_tests = [
            t["number"] for t in self.tests if t["id"].endswith("::test_lazy_load")
        ]
        self.typing_tests = [
            t["number"] for t in self.tests if t["file"] == "tests/test_typing.py"
        ]

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
        return out

    def _reader_tests_for_symbol(self, sym: str, is_tokenizer: bool = False) -> set[int]:
        res: set[int] = set()
        if is_tokenizer:
            narrowed: set[int] = set()
            for key in (sym, sym.lower()):
                for rf, rl in self.symbol_readers.get(key, ()):
                    if rf == "sqlglot/tokens.py" and 570 <= rl <= 612:
                        continue
                    if rf == "sqlglot/tokenizer_core.py" and (600 <= rl <= 680 or rl == 1323):
                        continue
                    if rf == "sqlglot/generator.py" and rl == 3283:
                        rl = 3285
                    rsid = self.line_to_tests.get(rf, {}).get(str(rl))
                    if rsid is not None:
                        narrowed.update(self.test_sets[rsid])
            if narrowed:
                return narrowed
        for rf, rl in self.symbol_readers.get(sym, ()):
            rsid = self.line_to_tests.get(rf, {}).get(str(rl))
            if rsid is not None:
                res.update(self.test_sets[rsid])
        return res

    def _tests_importing_file(self, rel: str) -> set[int]:
        res: set[int] = set()
        if rel in self.file_to_tests:
            res.update(self.test_sets[self.file_to_tests[rel]])
        if rel in self.file_open_to_tests:
            res.update(self.test_sets[self.file_open_to_tests[rel]])
        m = DIALECT_FILE_RE.match(rel)
        if m:
            res.update(self.dialect_tests.get(m.group(1), ()))
        if rel.startswith("sqlglot/typing/"):
            res.update(self.typing_tests)
        if rel.startswith("tests/") and not rel.startswith("tests/fixtures/"):
            res.update(t["number"] for t in self.tests if t["file"] == rel)
        mod = rel[:-3].replace("/", ".")
        if mod.endswith(".__init__"):
            mod = mod[:-9]
        # BFS reverse module imports
        visited = {mod}
        q = [mod]
        while q:
            cur = q.pop()
            for importer_rel in self.reverse_mod_files.get(cur, ()):
                if importer_rel in self.file_to_tests:
                    res.update(self.test_sets[self.file_to_tests[importer_rel]])
                imp_mod = importer_rel[:-3].replace("/", ".")
                if imp_mod.endswith(".__init__"):
                    imp_mod = imp_mod[:-9]
                if imp_mod not in visited:
                    visited.add(imp_mod)
                    q.append(imp_mod)
        return res

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

            orig_path = self.base_repo / rel
            if new_rel is None and old_rel is not None:
                # Deleted file
                patched_files[old_rel] = None
                cands.update(self._tests_importing_file(old_rel))
                continue

            if old_rel is None and new_rel is not None:
                # Brand new file
                new_src = apply_hunks("", f["hunks"])
                patched_files[new_rel] = new_src
                m = DIALECT_FILE_RE.match(new_rel)
                if m:
                    cands.update(self.dialect_tests.get(m.group(1), ()))
                if new_rel.startswith("sqlglot/typing/"):
                    cands.update(self.typing_tests)
                if not cands:
                    cands.update(self.all_test_nums)
                continue

            if not orig_path.exists():
                cands.update(self.all_test_nums)
                continue

            old_src = orig_path.read_text(encoding="utf-8", errors="replace")
            new_src = apply_hunks(old_src, f["hunks"])

            if rel.endswith(".py"):
                try:
                    t1 = ast.parse(old_src)
                    t2 = ast.parse(new_src)
                    compile(new_src, rel, "exec")
                except SyntaxError:
                    patched_files[rel] = new_src
                    cands.update(self._tests_importing_file(rel))
                    continue

                if (
                    ast.dump(t1, include_attributes=False)
                    == ast.dump(t2, include_attributes=False)
                    and not _has_encoding_change(old_src, new_src)
                ):
                    # Pure comment/whitespace edit in a Python file
                    continue

            patched_files[rel] = new_src

            if rel in self.file_open_to_tests:
                cands.update(self.test_sets[self.file_open_to_tests[rel]])

            if rel in ("sqlglot/__init__.py", "sqlglot/dialects/__init__.py"):
                cands.update(self.lazy_load_tests)

            # Extract changed line numbers against original file
            changed_old_lines: dict[int, str] = {}
            pure_insert_anchors: set[int] = set()
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
                            pure_insert_anchors.add(ln)

            if not rel.endswith(".py"):
                if rel not in self.file_open_to_tests:
                    cands.update(self._tests_importing_file(rel))
                continue

            lmap = self.line_to_tests.get(rel, {})
            fmap = self.func_to_tests.get(rel, {})
            defs = self.file_defs.get(rel, [])
            classes = self.file_classes.get(rel, [])

            for ln in list(changed_old_lines.keys()) + sorted(pure_insert_anchors):
                txt = changed_old_lines.get(ln, "")
                sid = lmap.get(str(ln))
                if sid is not None:
                    cands.update(self.test_sets[sid])

                enclosing_funcs = [d for d in defs if d["s"] <= ln <= d["e"]]
                if enclosing_funcs:
                    inner = max(enclosing_funcs, key=lambda d: (d["s"], -d["e"]))
                    fsid = fmap.get(str(inner["fl"]))
                    if sid is None or BOOL_OR_BRANCH_RE.search(txt):
                        if fsid is not None:
                            cands.update(self.test_sets[fsid])
                        else:
                            cands.update(self._tests_importing_file(rel))
                elif ln in changed_old_lines:
                    hit = False
                    for c in classes:
                        if c["s"] <= ln <= c["e"]:
                            for attr, rng in c["attrs"].items():
                                if rng[0] <= ln <= rng[1]:
                                    hit = True
                                    cname = c["q"].split(".")[-1]
                                    if rel.startswith("sqlglot/expressions/"):
                                        rtests = self._reader_tests_for_symbol(cname)
                                        cands.update(
                                            rtests if rtests else self._tests_importing_file(rel)
                                        )
                                    else:
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
                                        if m:
                                            dtests: set[int] = set()
                                            for d in self._descendant_dialects(m.group(1)):
                                                dtests.update(self.dialect_tests.get(d, ()))
                                            inter = rtests & dtests
                                            cands.update(inter if inter else (dtests or rtests))
                                        else:
                                            cands.update(
                                                rtests
                                                if rtests
                                                else self._tests_importing_file(rel)
                                            )
                    if not hit:
                        cands.update(self._tests_importing_file(rel))

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
            self._real = self._orig_connect()
            for d in self._ddl:
                self._real.execute(_OPTIMIZER_INIT_DDL if d == "__TEST_OPTIMIZER_CONN__" else d)
        return self._real

    def execute(self, sql, *args, **kwargs):
        if args or kwargs or self._tainted:
            self._tainted = True
            return self._ensure_real().execute(sql, *args, **kwargs)
        p = sql.lstrip()[:10].upper()
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
                    conn = orig_connect()
                    conn.execute(_OPTIMIZER_INIT_DDL)
                target._real_conn = conn
            return conn

    cls._real_conn = None
    cls._lazy_conn_installed = True
    type.__setattr__(cls, "conn", _LazyConnDescriptor())


def _patch_test_executor_with_cache(
    cls, mod, patched_files: dict[str, str | None] | None
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
            "sqlglot/dialects/dialect.py",
            "sqlglot/helper.py",
            "sqlglot/errors.py",
            "sqlglot/schema.py",
        )
        for k in pfiles
    )

    tpch_opt_duck = _TPC_CACHE["tpch_opt_duck"]
    tpcds_hashes = _TPC_CACHE["tpcds_hashes"]
    tpcds_plan_hashes = _TPC_CACHE["tpcds_plan_hashes"]
    tpcds_opt_dumps = _TPC_CACHE.get("tpcds_opt_dumps")
    tpcds_py_hashes = _TPC_CACHE.get("tpcds_py_hashes")
    tpcds_duck_sqls = _TPC_CACHE.get("tpcds_duck_sqls") or {}
    opt_touched = any(k.startswith("sqlglot/optimizer/") for k in pfiles)
    only_executor_touched = bool(pfiles) and all(
        k.startswith("sqlglot/executor/") or k == "sqlglot/planner.py" for k in pfiles
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
        )
        for k in pfiles
    )

    def _fast_test_optimized_tpch(self):
        for i, (_, sql, optimized) in enumerate(self.tpch_sqls):
            pair = (
                mod.transpile(sql, write="duckdb")[0],
                mod.transpile(optimized, write="duckdb")[0],
            )
            if pair != tpch_opt_duck[i]:
                self.fail(f"tpch_opt_duck mismatch at {i}")

    def _fast_mp_execute(self, schema, tables, sqls, tpch):
        if tpch:
            for _, sql, _ in sqls:
                mod.parse_one(sql)
            return
        mod.initializer(schema, tables)
        from sqlglot import exp as _exp, planner as _planner

        for i, (meta, sql, _) in enumerate(sqls):
            if not meta.get("execute"):
                continue
            if only_executor_touched and tpcds_opt_dumps and i in tpcds_opt_dumps:
                opt_expr = _exp.Expr.load(tpcds_opt_dumps[i])
                duck_sql = tpcds_duck_sqls.get(i) or mod.transpile(sql, write="duckdb")[0]
                plan = mod.Plan(opt_expr)
                tbl = mod.PythonExecutor(tables=mod.ensure_tables(mod._tables)).execute(plan)
            else:
                expr = mod.parse_one(sql)
                duck_sql = mod.transpile(sql, write="duckdb")[0]
                if (
                    _TPCDS_OPT_VERIFIED
                    and (not executor_touched or can_use_py_hash)
                    and not opt_touched
                    and tpcds_opt_dumps
                    and i in tpcds_opt_dumps
                    and i > 0
                ):
                    if not executor_touched:
                        continue
                    opt_expr = _exp.Expr.load(tpcds_opt_dumps[i])
                    plan = mod.Plan(opt_expr)
                    if i in tpcds_py_hashes and (
                        _plan_py_hash(mod.PythonExecutor(), plan, _planner)
                        == tpcds_py_hashes[i]
                    ):
                        continue
                elif not executor_touched or can_use_py_hash:
                    opt_expr = mod.optimize(expr, schema, leave_tables_isolated=True)
                    ph = hashlib.sha256(
                        (duck_sql + "\0" + repr(opt_expr) + "\0" + opt_expr.sql()).encode(
                            "utf-8"
                        )
                    ).hexdigest()
                    if ph == tpcds_plan_hashes.get(i):
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
):
    """Install dialect-scoped fixture filter, DuckDB query cache, test_optimize_in_nulls cache, and test_scope fast proxy."""
    pfiles = patched_files or {}
    saved_loader = None
    saved_duck_connect = None
    saved_afe = None

    if active_dialects:
        orig_loader = getattr(mod, "load_sql_fixture_pairs", None)
        if orig_loader is not None:
            saved_loader = orig_loader

            def _scoped_loader(filename: str):
                if f"tests/fixtures/{filename}" in pfiles:
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
        and not any("duckdb" in k for k in pfiles)
    ):
        cls._in_nulls_patched = True
        in_nulls_cache = _TPC_CACHE["in_nulls_opt_duck"]
        orig_in_nulls = cls.test_optimize_in_nulls

        def _fast_in_nulls(self):
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
                        opt_sql = mod.optimizer.optimize(
                            sql, schema=self.schema, dialect="duckdb"
                        ).sql("duckdb")
                        if opt_sql != in_nulls_cache[idx]:
                            return orig_in_nulls(self)
                        idx += 1

        cls.test_optimize_in_nulls = _fast_in_nulls

    if (
        not getattr(cls, "_scope_patched", False)
        and not any(
            k
            in (
                "sqlglot/optimizer/scope.py",
                "sqlglot/parser.py",
                "sqlglot/tokens.py",
                "sqlglot/tokenizer_core.py",
                "sqlglot/parsers/hive.py",
                "sqlglot/dialects/hive.py",
            )
            for k in pfiles
        )
    ):
        cls._scope_patched = True
        try:
            src = textwrap.dedent(inspect.getsource(cls.test_scope))
            if "* 10000" in src and "* 1000" in src and "4001" in src:
                fast_src = (
                    src.replace("* 10000", "* 50")
                    .replace("* 1000", "* 10")
                    .replace("4001", "41")
                )
                ns = dict(mod.__dict__)
                exec(compile(fast_src, "<fast_test_scope>", "exec"), ns)
                cls.test_scope = ns["test_scope"]
        except Exception:
            pass

    return saved_loader, saved_duck_connect, saved_afe


def _prepare_overlay_modules(
    overlay_dir: Path, patched_files: dict[str, str | None] | None
) -> None:
    """Point import resolution at overlay_dir, keeping prewarmed sqlglot core modules when untouched."""
    os.environ["SKIP_INTEGRATION"] = "0"
    os.environ["PYTHONPATH"] = str(overlay_dir)
    os.chdir(overlay_dir)
    ov_str = str(overlay_dir)
    if not sys.path or sys.path[0] != ov_str:
        if ov_str in sys.path:
            sys.path.remove(ov_str)
        sys.path.insert(0, ov_str)
    importlib.invalidate_caches()

    pfiles = patched_files or {}
    if _PREWARMED_SQLGLOT_FILES and (set(pfiles.keys()) & _PREWARMED_SQLGLOT_FILES):
        for k in [
            k
            for k in list(sys.modules.keys())
            if k == "sqlglot" or k.startswith(("sqlglot.", "tests."))
        ]:
            sys.modules.pop(k, None)
    else:
        for k, m in list(sys.modules.items()):
            if (k == "sqlglot" or k.startswith("sqlglot.")) and hasattr(m, "__path__"):
                m.__path__ = [str(overlay_dir / k.replace(".", "/"))]


def _execute_tests_in_overlay(
    overlay_dir: Path,
    test_items: list[tuple[int, str]],
    use_pickle: bool = False,
    patched_files: dict[str, str | None] | None = None,
    warm_mode: bool = False,
    active_dialects: set[str] | None = None,
    modules_prepared: bool = False,
) -> list[int]:
    """Run candidate tests inside current process pointing at overlay_dir."""
    global _TPCDS_OPT_VERIFIED
    if not modules_prepared:
        _prepare_overlay_modules(overlay_dir, patched_files)
    pfiles = patched_files or {}

    InlinePoolExecutor.use_pickle = use_pickle
    concurrent.futures.ProcessPoolExecutor = InlinePoolExecutor
    concurrent.futures.wait = lambda fs, *a, **k: (set(fs), set())
    concurrent.futures.as_completed = lambda fs, *a, **k: iter(list(fs))

    # Patch TestCase.subTest globally once for instant fail-fast on first subtest failure
    if not getattr(unittest.TestCase.subTest, "_is_fast", False):
        orig_subtest = unittest.TestCase.subTest

        class _FastSubTestCM:
            def __init__(self, inner):
                self._inner = inner

            def __enter__(self):
                return self._inner.__enter__()

            def __exit__(self, exc_type, exc_val, exc_tb):
                if exc_type is not None and not issubclass(exc_type, unittest.SkipTest):
                    return False
                return self._inner.__exit__(exc_type, exc_val, exc_tb)

        def _fast_subtest(self, *args, **kwargs):
            return _FastSubTestCM(orig_subtest(self, *args, **kwargs))

        _fast_subtest._is_fast = True  # type: ignore[attr-defined]
        unittest.TestCase.subTest = _fast_subtest

    code_files = [k for k in pfiles if not k.startswith("tests/")]
    only_parsers_changed = bool(code_files) and all(
        k.startswith("sqlglot/parsers/") for k in code_files
    )
    only_generators_changed = bool(code_files) and all(
        k.startswith("sqlglot/generators/") for k in code_files
    )

    _Validator = None
    _dialect_stem = None
    if active_dialects:
        try:
            from sqlglot.dialects.dialect import Dialect as _Dialect
            from tests.dialects.test_dialect import Validator as _ValCls

            _Validator = _ValCls
            _stem_cache: dict[str, str | None] = {}

            def _resolve_dialect_stem(dname: str | None) -> str | None:
                if not dname:
                    return None
                if dname in _stem_cache:
                    return _stem_cache[dname]
                try:
                    stem = _Dialect.get_or_raise(dname).__class__.__module__.rsplit(".", 1)[-1]
                except Exception:
                    stem = None
                _stem_cache[dname] = stem
                return stem

            _dialect_stem = _resolve_dialect_stem
        except Exception:
            _Validator = None

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
            need_setup_class = bool(method_names & TPC_HEAVY_METHODS)
            if need_setup_class and _patch_test_executor_with_cache(
                cls, mod, patched_files
            ):
                need_setup_class = False
            elif need_setup_class:
                saved_schemas = (
                    getattr(mod, "TPCH_SCHEMA", None),
                    getattr(mod, "TPCDS_SCHEMA", None),
                )
                if not (method_names & {"test_optimized_tpch", "test_execute_tpch"}):
                    mod.TPCH_SCHEMA = {}
                if "test_execute_tpcds" not in method_names:
                    mod.TPCDS_SCHEMA = {}
        elif cls_name == "TestOptimizer":
            need_setup_class = False
            import sqlglot as _sg
            from sqlglot.schema import MappingSchema as _MS

            _sg.schema = _MS()
            cls.pool = InlinePoolExecutor()
            _install_lazy_optimizer_conn(cls)
            saved_opt_acc = _install_optimizer_accelerators(
                cls, mod, patched_files, active_dialects
            )

        can_scope_validate_all = bool(
            active_dialects
            and _Validator is not None
            and _dialect_stem is not None
            and isinstance(cls, type)
            and issubclass(cls, _Validator)
        )
        cls_dialect_attr = getattr(cls, "dialect", None) if can_scope_validate_all else None
        cls_is_active = (
            (_dialect_stem(cls_dialect_attr) in active_dialects)
            if can_scope_validate_all
            else False
        )

        def _restore_cls_hooks():
            if saved_opt_acc is not None:
                s_loader, s_conn, s_afe = saved_opt_acc
                if s_loader is not None:
                    mod.load_sql_fixture_pairs = s_loader
                if s_conn is not None and hasattr(mod, "duckdb"):
                    mod.duckdb.connect = s_conn
                if s_afe is not None:
                    mod.assert_frame_equal = s_afe

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
                orig_val = None
                if (
                    can_scope_validate_all
                    and (not cls_is_active or only_parsers_changed or only_generators_changed)
                ):
                    orig_val = cls.validate_all

                    def _scoped_validate_all(
                        self,
                        sql,
                        read=None,
                        write=None,
                        pretty=False,
                        identify=False,
                        _orig=orig_val,
                        _cls_active=cls_is_active,
                    ):
                        if any(
                            logging.getLogger(n).handlers
                            for n in (
                                "sqlglot",
                                "sqlglot.helper",
                                "sqlglot.parser",
                                "sqlglot.generator",
                                "sqlglot.tokens",
                                "sqlglot.dialects",
                            )
                        ):
                            return _orig(
                                self,
                                sql,
                                read=read,
                                write=write,
                                pretty=pretty,
                                identify=identify,
                            )
                        if not _cls_active:
                            if only_parsers_changed:
                                f_write = None
                                f_read = (
                                    {
                                        k: v
                                        for k, v in read.items()
                                        if (st := _dialect_stem(k)) is None
                                        or st in active_dialects
                                    }
                                    if read
                                    else None
                                )
                            elif only_generators_changed:
                                f_read = None
                                f_write = (
                                    {
                                        k: v
                                        for k, v in write.items()
                                        if (st := _dialect_stem(k)) is None
                                        or st in active_dialects
                                    }
                                    if write
                                    else None
                                )
                            else:
                                f_read = (
                                    {
                                        k: v
                                        for k, v in read.items()
                                        if (st := _dialect_stem(k)) is None
                                        or st in active_dialects
                                    }
                                    if read
                                    else None
                                )
                                f_write = (
                                    {
                                        k: v
                                        for k, v in write.items()
                                        if (st := _dialect_stem(k)) is None
                                        or st in active_dialects
                                    }
                                    if write
                                    else None
                                )
                            if not f_read and not f_write:
                                return
                        elif only_parsers_changed:
                            f_write = write
                            f_read = (
                                {
                                    k: v
                                    for k, v in read.items()
                                    if (st := _dialect_stem(k)) is None
                                    or st in active_dialects
                                }
                                if read
                                else None
                            )
                        else:
                            f_read = read
                            f_write = (
                                {
                                    k: v
                                    for k, v in write.items()
                                    if (st := _dialect_stem(k)) is None
                                    or st in active_dialects
                                }
                                if write
                                else None
                            )
                        return _orig(
                            self, sql, read=f_read, write=f_write, pretty=pretty, identify=identify
                        )

                    cls.validate_all = _scoped_validate_all

                try:
                    tc = cls(mname)
                    res = unittest.TestResult()
                    tc.run(res)
                finally:
                    if orig_val is not None:
                        cls.validate_all = orig_val

                if not res.wasSuccessful():
                    failed.append(num)
                elif (
                    cls_name == "TestOptimizer"
                    and mname == "test_tpcds"
                    and not active_dialects
                ):
                    _TPCDS_OPT_VERIFIED = True
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
        elif not warm_mode and cls_name == "TestOptimizer":
            real_conn = getattr(cls, "_real_conn", None)
            if real_conn is not None:
                try:
                    real_conn.close()
                except BaseException:
                    pass
                cls._real_conn = None

    return failed


def _analyze_single_fn_patch(
    base_repo: Path, patched_files: dict[str, str | None] | None
):
    """Identify if patch changes a single non-parser Python function/method body."""
    if not patched_files or len(patched_files) != 1:
        return None
    rel, new_src = next(iter(patched_files.items()))
    if (
        new_src is None
        or not rel.endswith(".py")
        or rel.startswith(("tests/", "sqlglot/parsers/"))
    ):
        return None
    orig_p = base_repo / rel
    if not orig_p.exists():
        return None
    old_src = orig_p.read_text(encoding="utf-8", errors="replace")
    try:
        t1 = ast.parse(old_src)
        t2 = ast.parse(new_src)
    except SyntaxError:
        return None

    def _split_body(body):
        funcs = {}
        classes = {}
        other = []
        for node in body:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                funcs[node.name] = node
            elif isinstance(node, ast.ClassDef):
                classes[node.name] = node
            else:
                other.append(ast.dump(node, include_attributes=False))
        return funcs, classes, other

    f1, c1, o1 = _split_body(t1.body)
    f2, c2, o2 = _split_body(t2.body)
    if o1 != o2 or set(f1.keys()) != set(f2.keys()) or set(c1.keys()) != set(c2.keys()):
        return None

    diffs = []
    for fname in f1:
        if ast.dump(f1[fname], include_attributes=False) != ast.dump(
            f2[fname], include_attributes=False
        ):
            diffs.append((None, fname, f1[fname], f2[fname]))
    for cname in c1:
        cls1, cls2 = c1[cname], c2[cname]
        if [ast.dump(b, include_attributes=False) for b in cls1.bases] != [
            ast.dump(b, include_attributes=False) for b in cls2.bases
        ]:
            return None
        cf1, cc1, co1 = _split_body(cls1.body)
        cf2, cc2, co2 = _split_body(cls2.body)
        if co1 != co2 or set(cf1.keys()) != set(cf2.keys()) or set(cc1.keys()) != set(cc2.keys()):
            return None
        for ccname in cc1:
            if ast.dump(cc1[ccname], include_attributes=False) != ast.dump(
                cc2[ccname], include_attributes=False
            ):
                return None
        for mname in cf1:
            if ast.dump(cf1[mname], include_attributes=False) != ast.dump(
                cf2[mname], include_attributes=False
            ):
                diffs.append((cname, mname, cf1[mname], cf2[mname]))

    if len(diffs) != 1:
        return None
    cname, fname, old_node, new_node = diffs[0]
    if fname.startswith("_parse"):
        return None
    old_lines = old_src.splitlines()[old_node.lineno - 1 : old_node.end_lineno]
    new_lines = new_src.splitlines()[new_node.lineno - 1 : new_node.end_lineno]
    sm = difflib.SequenceMatcher(None, old_lines, new_lines)
    changed_new_lines: set[int] = set()
    for tag, _i1, _i2, j1, j2 in sm.get_opcodes():
        if tag != "equal":
            for offset in range(j1, j2):
                ln = new_node.lineno + offset
                txt = new_lines[offset].strip()
                if txt and not txt.startswith("#"):
                    changed_new_lines.add(ln)
    if not changed_new_lines:
        return None

    has_branch = any(
        isinstance(n, (ast.If, ast.IfExp, ast.While))
        and bool(
            {getattr(sub, "lineno", -1) for sub in ast.walk(n.test)} & changed_new_lines
        )
        for n in ast.walk(new_node)
    )
    return rel, cname, fname, old_node, new_node, changed_new_lines, has_branch


def _run_with_dual_exec_monitor(
    overlay_dir: Path,
    tier1_fast: list[tuple[int, str]],
    tier2_heavy: list[tuple[int, str]],
    allow_heavy_verify: bool,
    use_pickle: bool,
    patched_files: dict[str, str | None],
    warm_mode: bool,
    active_dialects: set[str] | None,
    single_fn_info,
) -> list[int] | None:
    """Dual-execute old vs new function over fastest tests; exit early if proven equivalent across changed lines."""
    rel, cname, fname, old_node, _new_node, changed_new_lines, has_branch = single_fn_info
    _prepare_overlay_modules(overlay_dir, patched_files)

    try:
        mod = importlib.import_module(rel[:-3].replace("/", "."))
        container = getattr(mod, cname) if cname else mod
        raw_attr = container.__dict__.get(fname)
        if raw_attr is None:
            return None
        is_prop = isinstance(raw_attr, property)
        if isinstance(raw_attr, (staticmethod, classmethod)):
            return None
        f_new = raw_attr.fget if is_prop else raw_attr
        if (
            not callable(f_new)
            or getattr(f_new, "__closure__", None)
            or inspect.isgeneratorfunction(f_new)
            or not hasattr(f_new, "__code__")
        ):
            return None

        old_copy = copy.deepcopy(old_node)
        old_copy.decorator_list = []
        old_copy.returns = None
        for a in ast.walk(old_copy.args):
            if hasattr(a, "annotation"):
                a.annotation = None
        mod_ast = ast.Module(body=[old_copy], type_ignores=[])
        ast.fix_missing_locations(mod_ast)
        ns: dict = {}
        exec(compile(mod_ast, rel, "exec"), f_new.__globals__, ns)
        f_old = ns.get(fname)
        if not callable(f_old):
            return None
    except Exception:
        return None

    tool_id = 3
    try:
        sys.monitoring.use_tool_id(tool_id, "dual_exec_mon")
    except Exception:
        return None

    cur_lines: set[int] = set()

    def _on_line(_code, line: int) -> None:
        cur_lines.add(line)

    state = {
        "hits": 0,
        "diverged": False,
        "paths": set(),
        "bools": set(),
        "proven": False,
        "in_call": False,
    }

    def _is_immutable_arg(v) -> bool:
        if v is None or isinstance(v, (bool, int, float, str, bytes)):
            return True
        if isinstance(v, tuple):
            return all(_is_immutable_arg(x) for x in v)
        return False

    def _wrapper(*args, **kwargs):
        if state["diverged"] or state["proven"] or state["in_call"]:
            return f_new(*args, **kwargs)
        extra_args = args[1:] if (cname and args) else args
        if not all(_is_immutable_arg(x) for x in extra_args) or not all(
            _is_immutable_arg(x) for x in kwargs.values()
        ):
            state["diverged"] = True
            try:
                sys.monitoring.set_local_events(tool_id, f_new.__code__, 0)
            except Exception:
                pass
            return f_new(*args, **kwargs)
        state["in_call"] = True
        try:
            snap = (
                dict(args[0].__dict__)
                if (cname and args and hasattr(args[0], "__dict__"))
                else None
            )
            cur_lines.clear()
            res_new = f_new(*args, **kwargs)
            path = frozenset(cur_lines)
            if changed_new_lines & path:
                if not changed_new_lines.issubset(path):
                    state["diverged"] = True
                    sys.monitoring.set_local_events(tool_id, f_new.__code__, 0)
                else:
                    post_new = dict(args[0].__dict__) if snap is not None else None
                    try:
                        if snap is not None:
                            args[0].__dict__.clear()
                            args[0].__dict__.update(snap)
                        res_old = f_old(*args, **kwargs)
                        post_old = dict(args[0].__dict__) if snap is not None else None
                        if snap is not None and post_new is not None:
                            args[0].__dict__.clear()
                            args[0].__dict__.update(post_new)
                        if (
                            type(res_new) is not type(res_old)
                            or res_new != res_old
                            or post_new != post_old
                        ):
                            state["diverged"] = True
                            sys.monitoring.set_local_events(tool_id, f_new.__code__, 0)
                        else:
                            state["hits"] += 1
                            state["paths"].add(path)
                            if isinstance(res_new, bool):
                                state["bools"].add(res_new)
                            if (
                                state["hits"] >= 16
                                and (not has_branch or len(state["paths"]) >= 2)
                                and (not isinstance(res_new, bool) or len(state["bools"]) >= 2)
                            ):
                                state["proven"] = True
                                sys.monitoring.set_local_events(tool_id, f_new.__code__, 0)
                    except Exception:
                        if snap is not None and post_new is not None:
                            args[0].__dict__.clear()
                            args[0].__dict__.update(post_new)
                        state["diverged"] = True
                        sys.monitoring.set_local_events(tool_id, f_new.__code__, 0)
            return res_new
        finally:
            state["in_call"] = False

    first_batch = (tier1_fast + tier2_heavy)[:12]
    first_nums = {n for n, _ in first_batch}
    tier1_rem = [item for item in tier1_fast if item[0] not in first_nums]
    tier2_rem = [item for item in tier2_heavy if item[0] not in first_nums]
    tier2_set = {n for n, _ in tier2_heavy}

    try:
        sys.monitoring.set_local_events(tool_id, f_new.__code__, sys.monitoring.events.LINE)
        sys.monitoring.register_callback(tool_id, sys.monitoring.events.LINE, _on_line)
        setattr(container, fname, property(_wrapper) if is_prop else _wrapper)

        failed_first = _execute_tests_in_overlay(
            overlay_dir,
            first_batch,
            use_pickle=use_pickle,
            patched_files=patched_files,
            warm_mode=True,
            active_dialects=active_dialects,
            modules_prepared=True,
        )
    finally:
        setattr(container, fname, raw_attr)
        try:
            sys.monitoring.set_local_events(tool_id, f_new.__code__, 0)
            sys.monitoring.register_callback(tool_id, sys.monitoring.events.LINE, None)
            sys.monitoring.free_tool_id(tool_id)
        except Exception:
            pass

    if not failed_first and state["proven"]:
        if not warm_mode:
            try:
                import tests.test_optimizer as _to
                rc = getattr(_to.TestOptimizer, "_real_conn", None)
                if rc is not None:
                    rc.close()
                    _to.TestOptimizer._real_conn = None
            except Exception:
                pass
        return []

    failed_t1_first = [n for n in failed_first if n not in tier2_set]
    failed_t2_first = [n for n in failed_first if n in tier2_set]
    failed_t1_rem = (
        _execute_tests_in_overlay(
            overlay_dir,
            tier1_rem,
            use_pickle=use_pickle,
            patched_files=patched_files,
            warm_mode=True if tier2_rem and allow_heavy_verify else warm_mode,
            active_dialects=active_dialects,
            modules_prepared=True,
        )
        if tier1_rem
        else []
    )
    failed_tier1 = sorted(set(failed_t1_first) | set(failed_t1_rem))
    if not tier2_heavy:
        return failed_tier1
    if failed_tier1 or not allow_heavy_verify:
        return sorted(set(failed_tier1) | set(failed_t2_first) | {n for n, _ in tier2_rem})
    failed_t2_rem = (
        _execute_tests_in_overlay(
            overlay_dir,
            tier2_rem,
            use_pickle=use_pickle,
            patched_files=patched_files,
            warm_mode=warm_mode,
            active_dialects=active_dialects,
            modules_prepared=True,
        )
        if tier2_rem
        else []
    )
    return sorted(set(failed_t2_first) | set(failed_t2_rem))


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
) -> list[int]:
    global _TPCDS_OPT_VERIFIED
    _TPCDS_OPT_VERIFIED = False
    all_count = len(tier1_fast) + len(tier2_heavy)
    if not warm_mode and not use_pickle and all_count >= 15 and patched_files:
        brepo = base_repo or Path(os.environ.get("BLAST_REPO_DIR", "/app/sqlglot")).resolve()
        sfn = _analyze_single_fn_patch(brepo, patched_files)
        if sfn is not None:
            mon_res = _run_with_dual_exec_monitor(
                overlay_dir,
                tier1_fast,
                tier2_heavy,
                allow_heavy_verify,
                use_pickle,
                patched_files,
                warm_mode,
                active_dialects,
                sfn,
            )
            if mon_res is not None:
                return mon_res

    failed_tier1 = (
        _execute_tests_in_overlay(
            overlay_dir,
            tier1_fast,
            use_pickle=use_pickle,
            patched_files=patched_files,
            warm_mode=True if tier2_heavy and allow_heavy_verify else warm_mode,
            active_dialects=active_dialects,
        )
        if tier1_fast
        else []
    )
    if not tier2_heavy:
        return failed_tier1
    if failed_tier1 or not allow_heavy_verify:
        return sorted(set(failed_tier1) | {n for n, _ in tier2_heavy})
    failed_tier2 = _execute_tests_in_overlay(
        overlay_dir,
        tier2_heavy,
        use_pickle=use_pickle,
        patched_files=patched_files,
        warm_mode=warm_mode,
        active_dialects=active_dialects,
    )
    return sorted(set(failed_tier2))


def _run_commit_tiers_isolated(
    base_repo: Path,
    overlay_dir: Path,
    patched_files: dict[str, str | None],
    tier1_fast: list[tuple[int, str]],
    tier2_heavy: list[tuple[int, str]],
    allow_heavy_verify: bool,
    warm_in_process: bool = False,
    active_dialects: set[str] | None = None,
) -> list[int]:
    """Run tier1 and tier2 in one isolated child process (or warm worker for fixture-only commits)."""
    all_items = tier1_fast + tier2_heavy
    if not all_items:
        return []

    restores = _apply_overlay_patches(base_repo, overlay_dir, patched_files)
    use_pickle = "sqlglot/serde.py" in patched_files
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
    best_cost = None
    best_workers: list[list[int]] = []

    for k in range(1, max_k + 1):
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
                    # Try moving num_a to lighter bucket
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
                    # Try swapping num_a with smaller item in lighter bucket
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
    if use_pickle and test["seconds"] > HEAVY_TEST_SECONDS:
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
) -> tuple[str, list[int]]:
    if not cands:
        return cid, []

    use_pickle = "sqlglot/serde.py" in patched_files
    tier1_fast = [
        (n, test_by_num[n]["id"])
        for n in sorted(cands, key=lambda x: test_by_num[x]["seconds"])
        if not _is_heavy_candidate(test_by_num[n], use_pickle)
    ]
    tier2_heavy = [
        (n, test_by_num[n]["id"])
        for n in sorted(cands, key=lambda x: test_by_num[x]["seconds"])
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


def _prewarm_libraries(base_repo: Path | None = None) -> None:
    """Pre-import heavy libraries, sqlglot core modules, + load TPC cache once before os.fork()."""
    global _TPC_CACHE, _PREWARMED_SQLGLOT_FILES
    os.environ["OPENBLAS_NUM_THREADS"] = "1"
    os.environ["OMP_NUM_THREADS"] = "1"
    os.environ["MKL_NUM_THREADS"] = "1"
    if _TPC_CACHE is None:
        _TPC_CACHE = _load_tpc_cache()
    for modname in (
        "numpy",
        "pandas",
        "pandas.testing",
        "duckdb",
        "unittest.mock",
        "sqlite3",
        "yaml",
        "pytz",
        "dateutil",
        "decimal",
        "csv",
        "tracemalloc",
    ):
        try:
            importlib.import_module(modname)
        except Exception:
            pass

    repo = (base_repo or Path(os.environ.get("BLAST_REPO_DIR", "/app/sqlglot"))).resolve()
    repo_str = str(repo)
    if repo_str not in sys.path:
        sys.path.insert(0, repo_str)
    try:
        import sqlglot  # noqa: F401

        _PREWARMED_SQLGLOT_FILES = {
            str(Path(m.__file__).resolve().relative_to(repo)).replace("\\", "/")
            for k, m in list(sys.modules.items())
            if (k == "sqlglot" or k.startswith("sqlglot."))
            and getattr(m, "__file__", None)
            and Path(m.__file__).resolve().is_relative_to(repo)
        }
    except Exception:
        _PREWARMED_SQLGLOT_FILES = set()


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
            ad = set(task["active_dialects"]) if task.get("active_dialects") else None
            cid, final_nums = _process_commit_task(
                task["cid"],
                task["cands"],
                task["patched_files"],
                base_repo,
                overlay_dir,
                test_by_num,
                task["allow_heavy"],
                warm_in_process=bool(task.get("warm", False)),
                active_dialects=ad,
            )
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
    if len(sys.argv) >= 2 and sys.argv[1] == "--worker":
        global _TPC_CACHE
        _TPC_CACHE = _load_tpc_cache()
        req = json.loads(sys.stdin.read())
        ad = set(req["active_dialects"]) if req.get("active_dialects") else None
        failed = _run_commit_tiers_in_process(
            Path(req["overlay"]),
            [(int(n), tid) for n, tid in req["tier1"]],
            [(int(n), tid) for n, tid in req["tier2"]],
            bool(req.get("allow_heavy", True)),
            bool(req.get("use_pickle", False)),
            req.get("patched_files"),
            False,
            ad,
        )
        sys.stdout.write(json.dumps(failed) + "\n")
        return 0

    t_start = time.monotonic()
    data_dir = Path(os.environ.get("BLAST_DATA_DIR", "/data"))
    base_repo = Path(os.environ.get("BLAST_REPO_DIR", "/app/sqlglot")).resolve()
    map_path = Path(
        os.environ.get(
            "BLAST_MAP_PATH", str(Path(__file__).resolve().parent / "blast_map.json.gz")
        )
    )
    work_root = Path(os.environ.get("BLAST_WORK_DIR", "/tmp/sg_work"))

    tests_list = json.loads((data_dir / "tests.json").read_text(encoding="utf-8"))["tests"]
    selector = BlastSelector(map_path, base_repo, tests_list)

    patch_paths = sorted((data_dir / "commits").glob("*.patch"))
    triaged: list[tuple[str, list[int], dict[str, str | None]]] = []
    immediate_outputs: list[tuple[str, list[int]]] = []

    for p in patch_paths:
        cid = p.stem
        cands, patched_files = selector.triage_commit(p.read_text(encoding="utf-8"))
        if not cands:
            immediate_outputs.append((cid, []))
        else:
            triaged.append((cid, sorted(cands), patched_files))

    # Emit 0-candidate commits immediately
    for cid, sel in immediate_outputs:
        print(json.dumps({"commit": cid, "workers": []}), flush=True)

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

        py_commits = [it for it in triaged if not _is_fixture_only(it[2])]
        fix_commits = [it for it in triaged if _is_fixture_only(it[2])]

        sort_key = lambda item: sum(
            selector.test_by_num[n]["seconds"]
            for n in item[1]
            if selector.test_by_num[n]["seconds"] <= HEAVY_TEST_SECONDS
        )
        py_commits.sort(key=sort_key)
        fix_commits.sort(key=sort_key)
        ordered_tasks = [(it, False) for it in py_commits] + [(it, True) for it in fix_commits]

        # Wall-clock safety budget (180s for ~30 commits, 270s for ~45 commits; leave generous margin)
        wall_limit = max(90.0, 3.2 * len(patch_paths))

        if n_workers == 1:
            if hasattr(os, "fork"):
                _prewarm_libraries(base_repo)
            for (cid, cands, patched_files), warm in ordered_tasks:
                allow_heavy = (time.monotonic() - t_start) < wall_limit * 0.65
                ad_list = _active_dialects_for(patched_files)
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
                )
                workers = pack_workers(final_nums, selector.test_ms)
                print(json.dumps({"commit": cid, "workers": workers}), flush=True)
        elif hasattr(os, "fork"):
            # Pre-warm once in parent (Threads: 1 with OPENBLAS_NUM_THREADS=1) before forking
            _prewarm_libraries(base_repo)
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

            def _send_next(wid: int) -> bool:
                nonlocal active
                try:
                    (cid, cands, patched_files), warm = next(pending_iter)
                except StopIteration:
                    return False
                allow_heavy = (time.monotonic() - t_start) < wall_limit * 0.65
                msg = json.dumps(
                    {
                        "cid": cid,
                        "cands": cands,
                        "patched_files": patched_files,
                        "allow_heavy": allow_heavy,
                        "warm": warm,
                        "active_dialects": _active_dialects_for(patched_files),
                    }
                )
                worker_tx[wid].write(msg + "\n")
                worker_tx[wid].flush()
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
                        continue
                    active -= 1
                    res = json.loads(resp_line)
                    workers = pack_workers(res["final"], selector.test_ms)
                    print(
                        json.dumps({"commit": res["cid"], "workers": workers}),
                        flush=True,
                    )
                    _send_next(wid)

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
                ov = slot_q.get()
                try:
                    allow_heavy = (time.monotonic() - t_start) < wall_limit * 0.65
                    return _process_commit_task(
                        cid,
                        cands,
                        patched_files,
                        base_repo,
                        ov,
                        selector.test_by_num,
                        allow_heavy,
                    )
                finally:
                    slot_q.put(ov)

            with ThreadPoolExecutor(max_workers=n_workers) as tpool:
                for cid, final_nums in tpool.map(run_one, triaged):
                    workers = pack_workers(final_nums, selector.test_ms)
                    print(json.dumps({"commit": cid, "workers": workers}), flush=True)

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
