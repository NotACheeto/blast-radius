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
import gzip
import importlib
import json
import math
import os
from pathlib import Path
import pickle
import re
import shutil
import subprocess
import sys
import time
import unittest

WORKER_COST_MS = 2_000
MAX_WORKERS = 8
HEAVY_TEST_SECONDS = 2.5

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

    def _reader_tests_for_symbol(self, sym: str) -> set[int]:
        res: set[int] = set()
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
                                        rtests = self._reader_tests_for_symbol(attr)
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
            if entry.name == "__pycache__":
                continue
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


def _execute_tests_in_overlay(
    overlay_dir: Path, test_items: list[tuple[int, str]], use_pickle: bool = False
) -> list[int]:
    """Run candidate tests inside current process pointing at overlay_dir."""
    os.environ["SKIP_INTEGRATION"] = "0"
    os.environ["PYTHONPATH"] = str(overlay_dir)
    os.chdir(overlay_dir)
    if str(overlay_dir) not in sys.path:
        sys.path.insert(0, str(overlay_dir))

    InlinePoolExecutor.use_pickle = use_pickle
    concurrent.futures.ProcessPoolExecutor = InlinePoolExecutor
    concurrent.futures.wait = lambda fs, *a, **k: (set(fs), set())
    concurrent.futures.as_completed = lambda fs, *a, **k: iter(list(fs))

    # Patch TestCase.subTest globally for instant fail-fast on first subtest failure
    orig_subtest = unittest.TestCase.subTest

    class _FastSubTestCM:
        def __init__(self, inner):
            self._inner = inner

        def __enter__(self):
            return self._inner.__enter__()

        def __exit__(self, exc_type, exc_val, exc_tb):
            if exc_type is not None and not issubclass(exc_type, unittest.SkipTest):
                # Do not suppress the exception — stop remaining subtests immediately
                return False
            return self._inner.__exit__(exc_type, exc_val, exc_tb)

    def _fast_subtest(self, *args, **kwargs):
        return _FastSubTestCM(orig_subtest(self, *args, **kwargs))

    unittest.TestCase.subTest = _fast_subtest

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

        # Skip heavy TPC-H / TPC-DS CSV loading in TestExecutor unless needed
        need_setup_class = True
        saved_schemas = None
        if cls_name == "TestExecutor":
            method_names = {m for _, m in methods}
            need_setup_class = bool(method_names & TPC_HEAVY_METHODS)
            if need_setup_class:
                saved_schemas = (
                    getattr(mod, "TPCH_SCHEMA", None),
                    getattr(mod, "TPCDS_SCHEMA", None),
                )
                if not (method_names & {"test_optimized_tpch", "test_execute_tpch"}):
                    mod.TPCH_SCHEMA = {}
                if "test_execute_tpcds" not in method_names:
                    mod.TPCDS_SCHEMA = {}

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
            continue

        for num, mname in methods:
            tc = cls(mname)
            res = unittest.TestResult()
            tc.run(res)
            if not res.wasSuccessful():
                failed.append(num)

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

    return failed


def _run_commit_tests_isolated(
    base_repo: Path,
    overlay_dir: Path,
    patched_files: dict[str, str | None],
    test_items: list[tuple[int, str]],
) -> list[int]:
    """Run candidate tests in a clean child process isolated from parent sqlglot imports."""
    if not test_items:
        return []

    restores = _apply_overlay_patches(base_repo, overlay_dir, patched_files)
    use_pickle = "sqlglot/serde.py" in patched_files
    try:
        if hasattr(os, "fork"):
            r_fd, w_fd = os.pipe()
            pid = os.fork()
            if pid == 0:
                os.close(r_fd)
                try:
                    failed = _execute_tests_in_overlay(
                        overlay_dir, test_items, use_pickle=use_pickle
                    )
                    payload = json.dumps(failed).encode("utf-8")
                except BaseException:
                    payload = json.dumps([n for n, _ in test_items]).encode("utf-8")
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
                    return [n for n, _ in test_items]
                return json.loads(b"".join(chunks).decode("utf-8"))
        else:
            # Windows fallback: invoke a clean python subprocess executing _worker_entry
            req = json.dumps(
                {
                    "overlay": str(overlay_dir),
                    "items": test_items,
                    "use_pickle": use_pickle,
                }
            )
            proc = subprocess.run(
                [sys.executable, __file__, "--worker"],
                input=req,
                text=True,
                capture_output=True,
            )
            if proc.returncode != 0 or not proc.stdout.strip():
                return [n for n, _ in test_items]
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


def _is_heavy_candidate(test: dict) -> bool:
    method_name = test["id"].split("::")[2]
    return test["seconds"] > HEAVY_TEST_SECONDS or method_name in TPC_HEAVY_METHODS


def _process_commit_task(
    cid: str,
    cands: list[int],
    patched_files: dict[str, str | None],
    base_repo: Path,
    overlay_dir: Path,
    test_by_num: dict[int, dict],
    allow_heavy_verify: bool,
) -> tuple[str, list[int]]:
    if not cands:
        return cid, []

    tier1_fast = [
        (n, test_by_num[n]["id"])
        for n in sorted(cands, key=lambda x: test_by_num[x]["seconds"])
        if not _is_heavy_candidate(test_by_num[n])
    ]
    tier2_heavy = [
        (n, test_by_num[n]["id"])
        for n in sorted(cands, key=lambda x: test_by_num[x]["seconds"])
        if _is_heavy_candidate(test_by_num[n])
    ]

    failed_tier1 = _run_commit_tests_isolated(
        base_repo, overlay_dir, patched_files, tier1_fast
    )

    if not tier2_heavy:
        return cid, failed_tier1

    # If any fast sibling failed or budget is tight, keep tier2_heavy directly without running it
    if failed_tier1 or not allow_heavy_verify:
        return cid, sorted(set(failed_tier1) | {n for n, _ in tier2_heavy})

    failed_tier2 = _run_commit_tests_isolated(
        base_repo, overlay_dir, patched_files, tier2_heavy
    )
    return cid, sorted(set(failed_tier1) | set(failed_tier2))


def _prewarm_libraries() -> None:
    """Pre-import heavy third-party packages once in parent before os.fork()."""
    for modname in (
        "duckdb",
        "numpy",
        "pandas",
        "pandas.testing",
        "pytz",
        "dateutil",
        "yaml",
        "sqlite3",
    ):
        try:
            importlib.import_module(modname)
        except Exception:
            pass


def main() -> int:
    if len(sys.argv) >= 2 and sys.argv[1] == "--worker":
        req = json.loads(sys.stdin.read())
        failed = _execute_tests_in_overlay(
            Path(req["overlay"]),
            [(int(n), tid) for n, tid in req["items"]],
            use_pickle=bool(req.get("use_pickle", False)),
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
        # Pre-import heavy libs once on Linux before os.fork()
        if hasattr(os, "fork"):
            _prewarm_libraries()

        # Build up to 2 overlay directories (matching 2 container CPUs)
        n_workers = min(2, len(triaged))
        overlays = [work_root / f"w{i}" for i in range(n_workers)]
        for ov in overlays:
            _build_overlay(base_repo, ov)

        # Sort commits so fastest-to-verify run first; heavy-only/large commits run with remaining budget
        triaged.sort(
            key=lambda item: sum(
                selector.test_by_num[n]["seconds"]
                for n in item[1]
                if selector.test_by_num[n]["seconds"] <= HEAVY_TEST_SECONDS
            )
        )

        # Wall-clock safety budget (180s for ~30 commits, 270s for ~45 commits; leave generous margin)
        wall_limit = max(90.0, 3.2 * len(patch_paths))

        if n_workers == 1:
            for cid, cands, patched_files in triaged:
                allow_heavy = (time.monotonic() - t_start) < wall_limit * 0.65
                _, final_nums = _process_commit_task(
                    cid,
                    cands,
                    patched_files,
                    base_repo,
                    overlays[0],
                    selector.test_by_num,
                    allow_heavy,
                )
                workers = pack_workers(final_nums, selector.test_ms)
                print(json.dumps({"commit": cid, "workers": workers}), flush=True)
        else:
            # 2-slot concurrent execution using threads dispatching isolated child processes
            # (On Linux each slot runs in its own overlay and os.fork()s; on Windows subprocess runs in its own overlay)
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

    print(
        f"processed {len(patch_paths)} commits in {time.monotonic() - t_start:.2f}s wall",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
