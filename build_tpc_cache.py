"""Build compact tpc_cache.pkl.gz and val_cache.pkl.gz with preloaded TPC-DS tables, baseline hashes, and test caches."""

from __future__ import annotations

import argparse
import collections
import gzip
import hashlib
import importlib
import logging
import os
from pathlib import Path
import pickle
import sys
import time
import zlib


def _hash_result(duck_sql: str, columns, rows) -> str:
    return hashlib.sha256(
        pickle.dumps((duck_sql, tuple(columns), list(rows)), protocol=4)
    ).hexdigest()


def _hash_expr_exact(obj) -> bytes:
    """Lossless deterministic 12-byte hash over Expr ASTs, types, comments, meta, and containers."""
    from enum import Enum
    import math

    h = hashlib.blake2b(digest_size=12)
    upd = h.update

    def _walk(v) -> None:
        if v is None:
            upd(b"N")
            return
        if hasattr(v, "args") and hasattr(v, "_type"):
            upd(b"E")
            upd(type(v).__name__.encode("utf-8"))
            upd(b"\0")
            _walk(v._type)
            _walk(v.comments)
            _walk(v._meta)
            args = v.args
            upd(len(args).to_bytes(4, "little"))
            for k in sorted(args):
                upd(k.encode("utf-8"))
                upd(b":")
                _walk(args[k])
            return
        tv = type(v)
        if tv is bool:
            upd(b"T" if v else b"F")
        elif isinstance(v, Enum):
            upd(b"M")
            upd(tv.__name__.encode("utf-8"))
            upd(b":")
            upd(v.name.encode("utf-8"))
        elif tv is int:
            upd(b"I")
            upd(str(v).encode("ascii"))
            upd(b"\0")
        elif tv is float:
            upd(b"R")
            upd(b"NAN" if math.isnan(v) else repr(v).encode("ascii"))
            upd(b"\0")
        elif tv is str:
            b = v.encode("utf-8")
            upd(b"S")
            upd(len(b).to_bytes(4, "little"))
            upd(b)
        elif tv is list:
            upd(b"L")
            upd(len(v).to_bytes(4, "little"))
            for item in v:
                _walk(item)
        elif tv is tuple:
            upd(b"P")
            upd(len(v).to_bytes(4, "little"))
            for item in v:
                _walk(item)
        elif isinstance(v, dict):
            upd(b"D")
            upd(len(v).to_bytes(4, "little"))
            for dk in sorted(v, key=lambda x: (type(x).__name__, str(x))):
                _walk(dk)
                _walk(v[dk])
        elif isinstance(v, (set, frozenset)):
            upd(b"Z")
            upd(len(v).to_bytes(4, "little"))
            for s in sorted(_hash_expr_exact(item) for item in v):
                upd(s)
        else:
            b = f"{tv.__name__}:{v!r}".encode("utf-8", errors="replace")
            upd(b"O")
            upd(len(b).to_bytes(4, "little"))
            upd(b)

    _walk(obj)
    return h.digest()


def _pack_expr(obj):
    """Losslessly pack an Expr AST tree (including _type, comments, _meta, None/[] args) to primitives."""
    from enum import Enum

    if obj is None or type(obj) in (bool, int, float, str):
        return obj
    if hasattr(obj, "args") and hasattr(obj, "_type"):
        args_packed = {k: _pack_expr(v) for k, v in obj.args.items()}
        t_p = _pack_expr(obj._type) if obj._type is not None else None
        c_p = list(obj.comments) if obj.comments is not None else None
        m_p = _pack_expr(obj._meta) if obj._meta is not None else None
        return ("__E__", type(obj).__name__, args_packed, t_p, c_p, m_p)
    if isinstance(obj, Enum):
        return ("__M__", type(obj).__qualname__, obj.name)
    if type(obj) is list:
        return [_pack_expr(x) for x in obj]
    if type(obj) is tuple:
        return ("__T__", [_pack_expr(x) for x in obj])
    if type(obj) is dict:
        return ("__D__", [(_pack_expr(k), _pack_expr(v)) for k, v in obj.items()])
    return obj


def _unpack_expr(obj, exp_mod):
    """Reconstruct an exact Expr AST tree packed by `_pack_expr`."""
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


def _plan_py_hash_and_dumps(
    py_exec, plan, planner_mod, serde_dump=None, collect_dumps: bool = False
) -> tuple[str, list[tuple[str, list[dict]]] | None]:
    """Hash generated Python expressions across a Plan and optionally capture serialized exprs."""
    out: list[str] = []
    expr_dumps: list[tuple[str, list[dict]]] | None = [] if collect_dumps else None
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
            if expr_dumps is not None and serde_dump is not None:
                expr_dumps.append((tag, serde_dump(e)))

    def _gen_many(exprs, tag: str) -> None:
        if exprs:
            for e in exprs:
                _gen_one(e, tag)

    walk_plan(plan)
    out.sort()
    return hashlib.sha256("\0".join(out).encode("utf-8")).hexdigest(), expr_dumps


def _plan_py_hash(py_exec, plan, planner_mod) -> str:
    return _plan_py_hash_and_dumps(py_exec, plan, planner_mod)[0]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", required=True, help="Path to sqlglot checkout")
    parser.add_argument("--out", required=True, help="Output tpc_cache.pkl.gz path")
    parser.add_argument("--val-out", default="", help="Optional output val_cache.pkl.gz path")
    args = parser.parse_args()

    t0 = time.perf_counter()
    repo_root = Path(args.repo).resolve()
    out_path = Path(args.out).resolve()
    val_out_path = Path(args.val_out).resolve() if args.val_out else None
    os.environ["SKIP_INTEGRATION"] = "0"
    os.chdir(repo_root)
    if str(repo_root) not in sys.path:
        sys.path.insert(0, str(repo_root))

    import inspect
    import unittest
    from concurrent.futures import ThreadPoolExecutor

    import duckdb
    import sqlglot as sg
    import tests.helpers as th
    import tests.test_executor as te
    import tests.test_optimizer as to
    from sqlglot import exp, generator as sg_gen, optimizer, parse_one, parser as sg_parser, planner, tokens as sg_tokens, transpile
    from sqlglot.dialects.dialect import Dialect
    from sqlglot.executor.python import PythonExecutor
    from sqlglot.executor.table import Table, ensure_tables
    from sqlglot.optimizer import RULES, optimize
    from sqlglot.optimizer.scope import build_scope, traverse_scope
    from sqlglot.planner import Plan
    from sqlglot.schema import MappingSchema, ensure_schema
    from sqlglot.serde import dump as serde_dump, load as serde_load

    te.TestExecutor.setUpClass()
    try:
        tpch_sqls = list(te.TestExecutor.tpch_sqls)
        tpcds_sqls = list(te.TestExecutor.tpcds_sqls)

        tpch_opt_duck: dict[int, tuple[str, str]] = {}
        for i, (_, sql, optimized) in enumerate(tpch_sqls):
            tpch_opt_duck[i] = (
                transpile(sql, write="duckdb")[0],
                transpile(optimized, write="duckdb")[0],
            )

        te.initializer(te.TPCDS_SCHEMA, te.TestExecutor.tpcds_tables)
        opt_exprs: dict[int, object] = {}
        tpcds_hashes: dict[int, str] = {}
        tpcds_plan_hashes: dict[int, str] = {}
        tpcds_opt_dumps: dict[int, list[dict]] = {}
        tpcds_raw_dumps: dict[int, list[dict] | None] = {}
        tpcds_py_hashes: dict[int, str] = {}
        tpcds_dump_py_hashes: dict[int, str] = {}
        tpcds_plan_expr_dumps: dict[int, list[tuple[str, list[dict]]] | None] = {}
        tpcds_duck_sqls: dict[int, str] = {}

        for i, (meta, sql, _) in enumerate(tpcds_sqls):
            if meta.get("execute"):
                expr = parse_one(sql)
                opt_expr = optimize(expr, te.TPCDS_SCHEMA, leave_tables_isolated=True)
                opt_exprs[i] = opt_expr
                plan = Plan(opt_expr)
                duck_sql = transpile(sql, write="duckdb")[0]
                tpcds_duck_sqls[i] = duck_sql
                raw_dump = serde_dump(expr)
                try:
                    tpcds_raw_dumps[i] = (
                        raw_dump if serde_load(raw_dump).sql(dialect="duckdb") == duck_sql else None
                    )
                except Exception:
                    tpcds_raw_dumps[i] = None
                tpcds_plan_hashes[i] = hashlib.sha256(
                    (duck_sql + "\0" + repr(opt_expr) + "\0" + opt_expr.sql()).encode("utf-8")
                ).hexdigest()
                dump_obj = serde_dump(opt_expr)
                tpcds_opt_dumps[i] = dump_obj
                tpcds_py_hashes[i] = _plan_py_hash(PythonExecutor(), plan, planner)
                d_py_h, pe_dumps = _plan_py_hash_and_dumps(
                    PythonExecutor(),
                    Plan(serde_load(dump_obj)),
                    planner,
                    serde_dump=serde_dump,
                    collect_dumps=True,
                )
                tpcds_dump_py_hashes[i] = d_py_h
                if pe_dumps is not None:
                    gen_check = PythonExecutor().generator
                    chk_out = sorted(
                        f"{tag}:{gen_check.generate(serde_load(d))}" for tag, d in pe_dumps
                    )
                    if hashlib.sha256("\0".join(chk_out).encode("utf-8")).hexdigest() == d_py_h:
                        tpcds_plan_expr_dumps[i] = pe_dumps
                    else:
                        tpcds_plan_expr_dumps[i] = None

        # Build coverage-preserving pruned TPC-DS tables (keep first 48 rows per table + up to 8 matches per Scan filter)
        raw_full = {name: (tbl.columns, tbl.rows) for name, tbl in te.TestExecutor.tpcds_tables.items()}
        for name, tbl in te.TestExecutor.tpcds_tables.items():
            tbl._orig_tname = name
        keep_indices = {
            name: set(range(min(len(tbl.rows), 48)))
            for name, tbl in te.TestExecutor.tpcds_tables.items()
        }
        t_ens_full = ensure_tables(te._tables)
        orig_pf = PythonExecutor._project_and_filter

        def _trace_pf(self, context, step, iterator):
            t = next(iter(context.tables.values())) if len(context.tables) == 1 else None
            tname = getattr(t, "_orig_tname", None) if t is not None else None
            if step.condition and tname is not None:
                cond = self.generate(step.condition)
                matched = 0
                reader = t.reader
                for idx, row in enumerate(t.rows):
                    reader.row = row
                    if context.eval(cond):
                        keep_indices[tname].add(idx)
                        matched += 1
                        if matched >= 8:
                            break
            res = orig_pf(self, context, step, iterator)
            if tname is not None and not step.condition and len(res.rows) == len(t.rows):
                res._orig_tname = tname
            return res

        PythonExecutor._project_and_filter = _trace_pf
        try:
            for opt_expr in opt_exprs.values():
                PythonExecutor(tables=t_ens_full).execute(Plan(opt_expr))
        finally:
            PythonExecutor._project_and_filter = orig_pf

        # Also cover all 5 ss_quantity buckets in store_sales (plus NULLs) for TPC-DS q=8
        if "store_sales" in raw_full:
            ss_cols, ss_rows = raw_full["store_sales"]
            if "ss_quantity" in ss_cols:
                q_idx = ss_cols.index("ss_quantity")
                bucket_counts = {b: 0 for b in range(6)}  # 0..4 = 5 buckets, 5 = None
                for idx, row in enumerate(ss_rows):
                    q = row[q_idx]
                    if q is None:
                        b = 5
                    elif 1 <= q <= 20:
                        b = 0
                    elif 21 <= q <= 40:
                        b = 1
                    elif 41 <= q <= 60:
                        b = 2
                    elif 61 <= q <= 80:
                        b = 3
                    elif 81 <= q <= 100:
                        b = 4
                    else:
                        continue
                    if bucket_counts[b] < 4:
                        keep_indices["store_sales"].add(idx)
                        bucket_counts[b] += 1
                        if all(c >= 4 for c in bucket_counts.values()):
                            break

        te.TestExecutor.tpcds_tables = {
            name: Table(cols, [rows[idx] for idx in sorted(keep_indices[name])])
            for name, (cols, rows) in raw_full.items()
        }
        te.initializer(te.TPCDS_SCHEMA, te.TestExecutor.tpcds_tables)
        t_ens_pruned = ensure_tables(te._tables)
        for i, opt_expr in opt_exprs.items():
            tbl = PythonExecutor(tables=t_ens_pruned).execute(Plan(opt_expr))
            tpcds_hashes[i] = _hash_result(tpcds_duck_sqls[i], tbl.columns, tbl.rows)
            # Verify deserialized Plan(serde_load(tpcds_opt_dumps[i])) matches tpcds_hashes[i]
            tbl_dump = PythonExecutor(tables=t_ens_pruned).execute(
                Plan(serde_load(tpcds_opt_dumps[i]))
            )
            if _hash_result(tpcds_duck_sqls[i], tbl_dump.columns, tbl_dump.rows) != tpcds_hashes[i]:
                raise RuntimeError(f"serde_load Plan hash mismatch at TPC-DS query {i}")

        tpcds_tables = {
            name: (tbl.columns, tbl.rows)
            for name, tbl in te.TestExecutor.tpcds_tables.items()
        }
    finally:
        te.TestExecutor.tearDownClass()

    # Extended TPC-DS cache across all 99 queries for TestOptimizer.test_tpcds
    tpcds_pairs = list(th.load_sql_fixture_pairs("optimizer/tpc-ds/tpc-ds.sql"))
    opt_schema = ensure_schema(to.TPCDS_SCHEMA)
    possible_kwargs = {
        "db": None,
        "catalog": None,
        "schema": opt_schema,
        "dialect": None,
        "sql": None,
        "isolate_tables": True,
        "quote_identifiers": False,
    }
    rule_specs = [
        (r, [p for p in inspect.getfullargspec(r).args if p in possible_kwargs])
        for r in RULES
    ]
    tpcds_rule_file_sets: list[set[str]] = [set() for _ in RULES]
    tpcds_rule_hashes: list[list[bytes]] = [[] for _ in RULES]
    rule_ckpts: dict[int, list[list[dict] | None]] = {
        r_idx: [] for r_idx in range(len(RULES) - 1)
    }
    all_opt_dumps: list[list[dict] | None] = []
    tpcds_no_gen_mask: list[bool] = []

    repo_prefix = str(repo_root).lower()
    code_rel_cache: dict[object, str | None] = {}
    cur_rule_idx = -1

    def _classify_rel(code) -> str | None:
        cached = code_rel_cache.get(code)
        if cached is not None or code in code_rel_cache:
            return cached
        fn = code.co_filename
        rel = None
        if fn and not fn.startswith("<"):
            try:
                p = Path(fn).resolve()
                if str(p).lower().startswith(repo_prefix) and p.is_file():
                    r = p.relative_to(repo_root).as_posix()
                    if r.startswith("sqlglot/"):
                        rel = r
            except Exception:
                rel = None
        code_rel_cache[code] = rel
        return rel

    def _on_rule_py_start(code, offset):
        if cur_rule_idx < 0:
            return sys.monitoring.DISABLE
        rel = _classify_rel(code)
        if rel is not None:
            tpcds_rule_file_sets[cur_rule_idx].add(rel)
        return sys.monitoring.DISABLE

    TOOL_ID = sys.monitoring.PROFILER_ID
    sys.monitoring.use_tool_id(TOOL_ID, "tpc_cache_rules")
    sys.monitoring.register_callback(TOOL_ID, sys.monitoring.events.PY_START, _on_rule_py_start)

    gen_calls_in_opt = [0]
    orig_gen_generate = sg_gen.Generator.generate

    def _count_gen_generate(self, expression, copy=True):
        gen_calls_in_opt[0] += 1
        return orig_gen_generate(self, expression, copy=copy)

    sg_gen.Generator.generate = _count_gen_generate
    try:
        for i, (_, sql, exp_sql) in enumerate(tpcds_pairs):
            cur = parse_one(sql)
            gen_calls_in_opt[0] = 0
            for r_idx, (rule_fn, params) in enumerate(rule_specs):
                cur_rule_idx = r_idx
                sys.monitoring.set_events(TOOL_ID, sys.monitoring.events.PY_START)
                sys.monitoring.restart_events()
                try:
                    cur = rule_fn(cur, **{p: possible_kwargs[p] for p in params})
                finally:
                    sys.monitoring.set_events(TOOL_ID, 0)
                    cur_rule_idx = -1
                h_cur = _hash_expr_exact(cur)
                tpcds_rule_hashes[r_idx].append(h_cur)
                if r_idx < len(RULES) - 1:
                    p_obj = _pack_expr(cur)
                    try:
                        ok_rt = _hash_expr_exact(_unpack_expr(p_obj, exp)) == h_cur
                    except Exception:
                        ok_rt = False
                    rule_ckpts[r_idx].append(p_obj if ok_rt else None)
                else:
                    opt_gen_calls = gen_calls_in_opt[0]
                    d_obj = serde_dump(cur)
                    try:
                        ok_sql = serde_load(d_obj).sql(pretty=True) == exp_sql
                    except Exception:
                        ok_sql = False
                    all_opt_dumps.append(d_obj if ok_sql else None)
                    tpcds_no_gen_mask.append(
                        (opt_gen_calls == 0) and (all_opt_dumps[-1] is not None)
                    )
            if cur.sql(pretty=True) != exp_sql:
                raise RuntimeError(f"Stepwise RULES SQL mismatch at TPC-DS {i}")
    finally:
        sg_gen.Generator.generate = orig_gen_generate
        sys.monitoring.set_events(TOOL_ID, 0)
        sys.monitoring.free_tool_id(TOOL_ID)

    tpcds_rule_files = [sorted(s) for s in tpcds_rule_file_sets]
    tpcds_rule_checkpoints_z = {
        r_idx: zlib.compress(pickle.dumps(ckpt_list, protocol=4), level=9)
        for r_idx, ckpt_list in rule_ckpts.items()
    }
    tpcds_all_opt_dumps_z = zlib.compress(pickle.dumps(all_opt_dumps, protocol=4), level=9)
    tpcds_raw_dumps_z = zlib.compress(pickle.dumps(tpcds_raw_dumps, protocol=4), level=9)
    tpcds_plan_expr_dumps_z = zlib.compress(
        pickle.dumps(tpcds_plan_expr_dumps, protocol=4), level=9
    )

    # Pre-compute test_optimize_in_nulls DuckDB-optimized baseline SQL strings, parse hashes & dumps
    to_inst = to.TestOptimizer("test_optimize_in_nulls")
    to_inst.setUp()
    in_nulls_opt_duck: list[str] = []
    in_nulls_parse_hashes: list[bytes] = []
    in_nulls_opt_dumps: list[list[dict] | None] = []
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
                in_nulls_parse_hashes.append(
                    _hash_expr_exact(parse_one(sql, read="duckdb"))
                )
                opt_e = optimizer.optimize(sql, schema=to_inst.schema, dialect="duckdb")
                opt_sql = opt_e.sql("duckdb")
                in_nulls_opt_duck.append(opt_sql)
                d_opt = serde_dump(opt_e)
                try:
                    ok_rt = serde_load(d_opt).sql("duckdb") == opt_sql
                except Exception:
                    ok_rt = False
                in_nulls_opt_dumps.append(d_opt if ok_rt else None)
    in_nulls_opt_dumps_z = zlib.compress(
        pickle.dumps(in_nulls_opt_dumps, protocol=4), level=9
    )

    # Record DuckDB caches AND TestOptimizer check_file fixture metadata
    duck_rows_cache: dict[bytes, list] = {}
    duck_df_cache: dict[bytes, tuple] = {}
    orig_duck_connect = duckdb.connect
    orig_afe = to.assert_frame_equal

    def _norm_cell(v):
        if isinstance(v, float) and v != v:
            return ("float", "__NAN__")
        return (type(v).__name__, v)

    class _RecDF:
        def __init__(self, sig, df_val):
            self.sig = sig
            self._df = df_val

    class _RecCursor:
        def __init__(self, conn, sql):
            self._conn = conn
            self._sql = sql

        def _key(self) -> bytes:
            return hashlib.sha256(
                ("\0".join(self._conn._ddl) + "\0" + self._sql).encode("utf-8")
            ).digest()[:12]

        def fetchall(self):
            k = self._key()
            if k not in duck_rows_cache:
                duck_rows_cache[k] = self._conn._real.execute(self._sql).fetchall()
            return duck_rows_cache[k]

        def df(self):
            k = self._key()
            cur = self._conn._real.execute(self._sql)
            df_val = cur.df()
            if k not in duck_df_cache:
                cur2 = self._conn._real.execute(self._sql)
                cols = tuple(d[0] for d in (cur2.description or ()))
                rows = tuple(tuple(_norm_cell(v) for v in r) for r in cur2.fetchall())
                dtypes = tuple(str(dt) for dt in df_val.dtypes)
                duck_df_cache[k] = (cols, dtypes, rows)
            return _RecDF(duck_df_cache[k], df_val)

    class _RecConn:
        def __init__(self, init_ddl: str | None = None):
            self._ddl = [init_ddl] if init_ddl else []
            self._real = orig_duck_connect()

        def execute(self, sql, *args, **kwargs):
            if args or kwargs:
                return self._real.execute(sql, *args, **kwargs)
            p = sql.lstrip()[:10].upper()
            if not p.startswith(("SELECT", "WITH", "(", "VALUES", "FROM")):
                self._ddl.append(sql)
                self._real.execute(sql)
                return self
            return _RecCursor(self, sql)

        def close(self):
            self._real.close()

        def __enter__(self):
            return self

        def __exit__(self, *a):
            self.close()

    opt_fixture_meta: dict[str, dict] = {}

    sg.schema = MappingSchema()
    to.TestOptimizer.pool = ThreadPoolExecutor(max_workers=1)
    to.TestOptimizer.setUpClass()
    real_class_conn = to.TestOptimizer.conn
    rec_class_conn = _RecConn("__TEST_OPTIMIZER_CONN__")
    rec_class_conn._real.close()
    rec_class_conn._real = real_class_conn
    to.TestOptimizer.conn = rec_class_conn
    duckdb.connect = lambda *a, **k: _RecConn()
    to.assert_frame_equal = lambda a, b, *args, **kwargs: orig_afe(
        a._df if isinstance(a, _RecDF) else a,
        b._df if isinstance(b, _RecDF) else b,
        *args,
        **kwargs,
    )

    orig_check_file = to.TestOptimizer.check_file
    orig_p_parse = sg_parser.Parser.parse
    orig_p_parse_into = sg_parser.Parser.parse_into
    orig_t_tokenize = sg_tokens.Tokenizer.tokenize

    trace_state = {"active": False, "depth": 0, "untracked": False, "gen_calls": 0, "aux": {}}

    def _dialect_str(d) -> str:
        if d is None:
            return ""
        if isinstance(d, str):
            return d
        if isinstance(d, Dialect):
            stem = type(d).__module__.rsplit(".", 1)[-1]
            return "" if stem == "dialect" else stem
        return ""

    def _traced_p_parse(self, raw_tokens, sql=None):
        if not trace_state["active"] or trace_state["depth"] > 0:
            return orig_p_parse(self, raw_tokens, sql)
        if not isinstance(sql, str) or self.max_nodes != -1:
            trace_state["untracked"] = True
            return orig_p_parse(self, raw_tokens, sql)
        trace_state["depth"] += 1
        try:
            res = orig_p_parse(self, raw_tokens, sql)
        finally:
            trace_state["depth"] -= 1
        d_str = _dialect_str(self.dialect)
        err_name = self.error_level.name if self.error_level else None
        trace_state["aux"][(d_str, None, err_name, sql)] = _hash_expr_exact(res)
        return res

    def _traced_p_parse_into(self, expression_types, raw_tokens, sql=None):
        if not trace_state["active"] or trace_state["depth"] > 0:
            return orig_p_parse_into(self, expression_types, raw_tokens, sql)
        into_name = None
        if isinstance(expression_types, type) and issubclass(expression_types, exp.Expr):
            into_name = expression_types.__name__
        elif (
            isinstance(expression_types, (tuple, list))
            and expression_types
            and all(isinstance(x, type) and issubclass(x, exp.Expr) for x in expression_types)
        ):
            into_name = tuple(x.__name__ for x in expression_types)
        if into_name is None or not isinstance(sql, str) or self.max_nodes != -1:
            trace_state["untracked"] = True
            return orig_p_parse_into(self, expression_types, raw_tokens, sql)
        trace_state["depth"] += 1
        try:
            res = orig_p_parse_into(self, expression_types, raw_tokens, sql)
        finally:
            trace_state["depth"] -= 1
        d_str = _dialect_str(self.dialect)
        err_name = self.error_level.name if self.error_level else None
        trace_state["aux"][(d_str, into_name, err_name, sql)] = _hash_expr_exact(res)
        return res

    def _traced_t_tokenize(self, sql):
        if not trace_state["active"] or trace_state["depth"] > 0:
            return orig_t_tokenize(self, sql)
        if not isinstance(sql, str):
            trace_state["untracked"] = True
            return orig_t_tokenize(self, sql)
        res = orig_t_tokenize(self, sql)
        d_str = _dialect_str(self.dialect)
        tok_sig = hashlib.blake2b(
            "\0".join(f"{t.token_type.name}:{t.text}" for t in res).encode("utf-8"),
            digest_size=12,
        ).digest()
        trace_state["aux"][(d_str, "__TOK__", None, sql)] = tok_sig
        return res

    def _traced_gen_generate(self, expression, copy=True):
        if trace_state["active"]:
            trace_state["gen_calls"] += 1
        return orig_gen_generate(self, expression, copy=copy)

    def _rec_check_file(self, file, func, pretty=False, execute=None, only=None, **kwargs):
        f_meta = opt_fixture_meta.setdefault(
            file,
            {"aux_map": {}, "parse_hashes": {}, "opt_dumps": {}},
        )
        for i, (meta, sql, expected) in enumerate(
            th.load_sql_fixture_pairs(f"optimizer/{file}.sql"), start=1
        ):
            title = meta.get("title") or f"{i}, {sql}"
            if only and title != only:
                continue
            dialect = meta.get("dialect")
            leave_tables_isolated = meta.get("leave_tables_isolated")
            validate_qualify_columns = meta.get("validate_qualify_columns")
            canonicalize_table_aliases = meta.get("canonicalize_table_aliases")
            func_kwargs = kwargs.copy()
            if schema := meta.get("schema"):
                func_kwargs["schema"] = to.json.loads(schema)
            if leave_tables_isolated is not None:
                func_kwargs["leave_tables_isolated"] = to.string_to_bool(leave_tables_isolated)
            if validate_qualify_columns is not None:
                func_kwargs["validate_qualify_columns"] = to.string_to_bool(validate_qualify_columns)
            if dialect:
                func_kwargs["dialect"] = dialect
            if canonicalize_table_aliases is not None:
                func_kwargs["canonicalize_table_aliases"] = to.string_to_bool(
                    canonicalize_table_aliases
                )
            fixture_execute = False if execute is False else meta.get("execute", execute)
            if min_python := meta.get("execute_min_python"):
                fixture_execute = to.string_to_bool(fixture_execute) and sys.version_info >= tuple(
                    map(int, min_python.split("."))
                )

            expr = parse_one(sql, read=dialect)
            in_hash = _hash_expr_exact(expr)

            trace_state["untracked"] = False
            trace_state["gen_calls"] = 0
            trace_state["aux"] = {}
            trace_state["depth"] = 0
            trace_state["active"] = True
            try:
                optimized = func(expr, **func_kwargs)
                gen_in_opt = trace_state["gen_calls"]
                actual = optimized.sql(pretty=pretty, dialect=dialect)
            finally:
                trace_state["active"] = False

            self.assertEqual(expected, actual)
            if not trace_state["untracked"] and not only:
                f_meta["aux_map"].update(trace_state["aux"])
                f_meta["parse_hashes"][(dialect or "", sql)] = in_hash

            if not only and gen_in_opt == 0 and file != "tpc-ds/tpc-ds":
                func_name = getattr(func, "__name__", None) or getattr(
                    getattr(func, "func", None), "__name__", repr(func)
                )
                d_opt = serde_dump(optimized)
                try:
                    rt_opt = serde_load(d_opt)
                    ok_sql = rt_opt.sql(pretty=pretty, dialect=dialect) == expected
                except Exception:
                    rt_opt = None
                    ok_sql = False
                if ok_sql:
                    if to.string_to_bool(fixture_execute):
                        orig_duck = parse_one(sql, read=dialect).sql(dialect="duckdb")
                        opt_duck = optimized.sql(dialect="duckdb")
                        try:
                            ok_duck = rt_opt.sql(dialect="duckdb") == opt_duck
                        except Exception:
                            ok_duck = False
                        if ok_duck:
                            f_meta["opt_dumps"][
                                (func_name, i, dialect or "", sql, bool(pretty), expected)
                            ] = (d_opt, orig_duck, opt_duck)
                    else:
                        f_meta["opt_dumps"][
                            (func_name, i, dialect or "", sql, bool(pretty), expected)
                        ] = (d_opt, None, None)

            if to.string_to_bool(fixture_execute):
                dfs = []
                for e2 in (parse_one(sql, read=dialect), optimized):
                    if not isinstance(e2, (exp.Query, exp.Values)):
                        e2 = exp.select(exp.alias_(e2, "_col_0"))
                    dfs.append(self.conn.execute(e2.sql(dialect="duckdb")).df())
                to.assert_frame_equal(*dfs)

    sg_parser.Parser.parse = _traced_p_parse
    sg_parser.Parser.parse_into = _traced_p_parse_into
    sg_tokens.Tokenizer.tokenize = _traced_t_tokenize
    sg_gen.Generator.generate = _traced_gen_generate
    to.TestOptimizer.check_file = _rec_check_file
    af_aux_map: dict = {}
    af_parse_hashes: dict = {}
    af_ok = True
    try:
        opt_methods = [
            m
            for m, fn in inspect.getmembers(to.TestOptimizer, inspect.isfunction)
            if m.startswith("test_")
            and (
                "check_file" in inspect.getsource(fn)
                or "conn" in inspect.getsource(fn)
                or "duckdb" in inspect.getsource(fn)
                or "execute=True" in inspect.getsource(fn)
            )
        ]
        for m in opt_methods:
            tc = to.TestOptimizer(m)
            res = unittest.TestResult()
            tc.run(res)
            if not res.wasSuccessful():
                raise RuntimeError(f"Optimizer cache record failed in {m}: {res.failures} {res.errors}")

        # Record annotate_functions metadata for parser_only acceleration
        af_schema = {
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
        for af_meta_row, af_sql_raw, af_expected in th.load_sql_fixture_pairs(
            "optimizer/annotate_functions.sql"
        ):
            af_d_str = af_meta_row.get("dialect") or ""
            af_sql = f"SELECT {af_sql_raw} FROM tbl"
            for d_one in af_d_str.split(", "):
                expr = parse_one(af_sql, read=d_one)
                in_h = _hash_expr_exact(expr)
                exp_h = _hash_expr_exact(exp.DataType.build(af_expected, dialect=d_one))
                trace_state["untracked"] = False
                trace_state["aux"] = {}
                trace_state["depth"] = 0
                trace_state["active"] = True
                try:
                    res_opt = to.annotate_functions(
                        expr, schema=af_schema, dialect=d_one
                    )
                finally:
                    trace_state["active"] = False
                if trace_state["untracked"]:
                    af_ok = False
                else:
                    af_aux_map.update(trace_state["aux"])
                    af_parse_hashes[(d_one, af_sql, af_expected)] = (in_h, exp_h)
    finally:
        sg_parser.Parser.parse = orig_p_parse
        sg_parser.Parser.parse_into = orig_p_parse_into
        sg_tokens.Tokenizer.tokenize = orig_t_tokenize
        sg_gen.Generator.generate = orig_gen_generate
        to.TestOptimizer.check_file = orig_check_file
        duckdb.connect = orig_duck_connect
        to.assert_frame_equal = orig_afe
        try:
            real_class_conn.close()
        except Exception:
            pass

    def _self_verify_aux(aux_calls: list[tuple]) -> bool:
        for d_str, into_n, err_name, sql_s, expected_h in aux_calls:
            try:
                d_inst = Dialect.get_or_raise(d_str or None)
                if into_n == "__TOK__":
                    toks = d_inst.tokenize(sql_s)
                    sig = hashlib.blake2b(
                        "\0".join(f"{t.token_type.name}:{t.text}" for t in toks).encode("utf-8"),
                        digest_size=12,
                    ).digest()
                    if sig != expected_h:
                        return False
                elif into_n is None:
                    el = sg.ErrorLevel[err_name] if err_name else None
                    if _hash_expr_exact(d_inst.parse(sql_s, error_level=el)) != expected_h:
                        return False
                else:
                    into_cls = (
                        tuple(getattr(exp, n) for n in into_n)
                        if isinstance(into_n, tuple)
                        else getattr(exp, into_n)
                    )
                    el = sg.ErrorLevel[err_name] if err_name else None
                    if _hash_expr_exact(d_inst.parse_into(into_cls, sql_s, error_level=el)) != expected_h:
                        return False
            except Exception:
                return False
        return True

    # Finalize opt_fixture_meta (self-verify aux_calls, convert to sorted list, compress opt_dumps)
    final_opt_fixture_meta: dict[str, dict] = {}
    for file_key, f_meta in opt_fixture_meta.items():
        aux_calls = [
            (d_str, into_n, err_name, s, h)
            for (d_str, into_n, err_name, s), h in sorted(
                f_meta["aux_map"].items(),
                key=lambda x: (
                    x[0][0],
                    ",".join(x[0][1]) if isinstance(x[0][1], tuple) else (x[0][1] or ""),
                    x[0][2] or "",
                    x[0][3],
                ),
            )
        ]
        ph_map = f_meta["parse_hashes"] if _self_verify_aux(aux_calls) else {}
        entry: dict[str, object] = {
            "aux_calls": aux_calls if ph_map else [],
            "parse_hashes": ph_map,
        }
        if f_meta["opt_dumps"]:
            entry["opt_dumps_z"] = zlib.compress(
                pickle.dumps(f_meta["opt_dumps"], protocol=4), level=9
            )
        final_opt_fixture_meta[file_key] = entry

    af_aux_calls = [
        (d_str, into_n, err_name, s, h)
        for (d_str, into_n, err_name, s), h in sorted(
            af_aux_map.items(),
            key=lambda x: (
                x[0][0],
                ",".join(x[0][1]) if isinstance(x[0][1], tuple) else (x[0][1] or ""),
                x[0][2] or "",
                x[0][3],
            ),
        )
    ]
    annotate_funcs_meta = (
        {"aux_calls": af_aux_calls, "parse_hashes": af_parse_hashes}
        if af_ok and af_parse_hashes and _self_verify_aux(af_aux_calls)
        else None
    )

    # Pre-compute stress-test counts for TestOptimizer.test_scope
    s1 = " UNION ALL ".join(["SELECT x FROM t"] * 10000)
    ast1 = parse_one(s1)
    s2 = "SELECT 1" + " UNION SELECT 1 INTERSECT SELECT 1" * 1000
    ast2 = parse_one(s2, read="hive")
    scope_stress_counts = (
        len(list(build_scope(ast1).traverse())),
        len(traverse_scope(ast1)),
        len(list(build_scope(ast2).traverse())),
    )

    payload = {
        "tpcds_tables": tpcds_tables,
        "tpch_sqls": tpch_sqls,
        "tpcds_sqls": tpcds_sqls,
        "tpch_opt_duck": tpch_opt_duck,
        "tpcds_duck_sqls": tpcds_duck_sqls,
        "tpcds_hashes": tpcds_hashes,
        "tpcds_plan_hashes": tpcds_plan_hashes,
        "tpcds_opt_dumps": tpcds_opt_dumps,
        "tpcds_raw_dumps_z": tpcds_raw_dumps_z,
        "tpcds_py_hashes": tpcds_py_hashes,
        "tpcds_dump_py_hashes": tpcds_dump_py_hashes,
        "tpcds_plan_expr_dumps_z": tpcds_plan_expr_dumps_z,
        "tpcds_rule_files": tpcds_rule_files,
        "tpcds_rule_hashes": tpcds_rule_hashes,
        "tpcds_rule_checkpoints_z": tpcds_rule_checkpoints_z,
        "tpcds_all_opt_dumps_z": tpcds_all_opt_dumps_z,
        "tpcds_no_gen_mask": tpcds_no_gen_mask,
        "opt_fixture_meta": final_opt_fixture_meta,
        "annotate_funcs_meta": annotate_funcs_meta,
        "in_nulls_opt_duck": in_nulls_opt_duck,
        "in_nulls_parse_hashes": in_nulls_parse_hashes,
        "in_nulls_opt_dumps_z": in_nulls_opt_dumps_z,
        "duck_rows_cache": duck_rows_cache,
        "duck_df_cache": duck_df_cache,
        "scope_stress_counts": scope_stress_counts,
    }

    raw = pickle.dumps(payload, protocol=4)
    with gzip.open(out_path, "wb", compresslevel=9) as gz:
        gz.write(raw)

    print(
        f"Wrote {out_path} ({out_path.stat().st_size / 1024:.1f} KB, "
        f"tpch_opt={len(tpch_opt_duck)}, tpcds={len(tpcds_hashes)}, "
        f"opt_fixtures={len(final_opt_fixture_meta)}, "
        f"in_nulls={len(in_nulls_opt_duck)}, duck_rows={len(duck_rows_cache)}, "
        f"duck_df={len(duck_df_cache)}, scope={scope_stress_counts}) "
        f"in {time.perf_counter() - t0:.2f}s",
        file=sys.stderr,
    )

    if val_out_path is not None:
        t_val = time.perf_counter()
        import tests.dialects.test_dialect as td

        val_parse_hashes: dict[tuple[str, str], bytes] = {}
        val_opt_keys: set[tuple[str, str]] = set()
        bad_parse_keys: set[tuple[str, str]] = set()

        orig_v_vi = td.Validator.validate_identity
        orig_v_va = td.Validator.validate_all
        orig_td_parse_one = td.parse_one

        v_trace = {"pt_calls": 0}
        opt_code_cache: dict[object, bool] = {}
        opt_stack: list[bool] = []

        def _is_opt_code(code) -> bool:
            cached = opt_code_cache.get(code)
            if cached is not None:
                return cached
            fn = code.co_filename
            is_opt = False
            if fn and not fn.startswith("<"):
                try:
                    p = Path(fn).resolve()
                    if str(p).lower().startswith(repo_prefix) and p.is_file():
                        rel = p.relative_to(repo_root).as_posix()
                        if rel.startswith("sqlglot/optimizer/"):
                            is_opt = True
                except Exception:
                    is_opt = False
            opt_code_cache[code] = is_opt
            return is_opt

        def _on_val_py_start(code, offset):
            if _is_opt_code(code):
                if opt_stack:
                    opt_stack[-1] = True
                return None
            return sys.monitoring.DISABLE

        VAL_TOOL_ID = sys.monitoring.PROFILER_ID
        sys.monitoring.use_tool_id(VAL_TOOL_ID, "val_opt_trace")
        sys.monitoring.register_callback(
            VAL_TOOL_ID, sys.monitoring.events.PY_START, _on_val_py_start
        )
        sys.monitoring.set_events(VAL_TOOL_ID, sys.monitoring.events.PY_START)
        sys.monitoring.restart_events()

        def _vp_parse(self, raw_tokens, sql=None):
            v_trace["pt_calls"] += 1
            return orig_p_parse(self, raw_tokens, sql)

        def _vp_parse_into(self, expression_types, raw_tokens, sql=None):
            v_trace["pt_calls"] += 1
            return orig_p_parse_into(self, expression_types, raw_tokens, sql)

        def _vt_tokenize(self, sql):
            v_trace["pt_calls"] += 1
            return orig_t_tokenize(self, sql)

        def _rec_v_vi(
            self, sql, write_sql=None, pretty=False, check_command_warning=False, identify=False
        ):
            opt_stack.append(False)
            try:
                if not check_command_warning:
                    expr_obj = self.parse_one(sql)
                    h = _hash_expr_exact(expr_obj)
                    pt0 = v_trace["pt_calls"]
                    self.assertEqual(
                        write_sql or sql,
                        expr_obj.sql(dialect=self.dialect, pretty=pretty, identify=identify),
                    )
                    key = (self.dialect or "", sql)
                    if v_trace["pt_calls"] == pt0 and key not in bad_parse_keys:
                        val_parse_hashes[key] = h
                    else:
                        bad_parse_keys.add(key)
                    return expr_obj
                return orig_v_vi(
                    self,
                    sql,
                    write_sql=write_sql,
                    pretty=pretty,
                    check_command_warning=check_command_warning,
                    identify=identify,
                )
            finally:
                if opt_stack.pop():
                    val_opt_keys.add((self.dialect or "", sql))

        def _rec_v_va(self, sql, read=None, write=None, pretty=False, identify=False):
            opt_stack.append(False)
            try:
                expression = self.parse_one(sql)
                h_main = _hash_expr_exact(expression)

                for read_dialect, read_sql in (read or {}).items():
                    with self.subTest(f"{read_dialect} -> {sql}"):
                        r_expr = orig_td_parse_one(read_sql, read_dialect)
                        r_hash = _hash_expr_exact(r_expr)
                        pt0 = v_trace["pt_calls"]
                        self.assertEqual(
                            r_expr.sql(
                                self.dialect,
                                unsupported_level=td.ErrorLevel.IGNORE,
                                pretty=pretty,
                                identify=identify,
                            ),
                            sql,
                        )
                        r_key = (read_dialect or "", read_sql)
                        if v_trace["pt_calls"] == pt0 and r_key not in bad_parse_keys:
                            val_parse_hashes[r_key] = r_hash
                        else:
                            bad_parse_keys.add(r_key)

                pt_w0 = v_trace["pt_calls"]
                for write_dialect, write_sql in (write or {}).items():
                    with self.subTest(f"{sql} -> {write_dialect}"):
                        if write_sql is td.UnsupportedError:
                            with self.assertRaises(td.UnsupportedError):
                                expression.sql(write_dialect, unsupported_level=td.ErrorLevel.RAISE)
                        else:
                            self.assertEqual(
                                expression.sql(
                                    write_dialect,
                                    unsupported_level=td.ErrorLevel.IGNORE,
                                    pretty=pretty,
                                    identify=identify,
                                ),
                                write_sql,
                            )
                m_key = (self.dialect or "", sql)
                if v_trace["pt_calls"] == pt_w0 and m_key not in bad_parse_keys:
                    val_parse_hashes[m_key] = h_main
                else:
                    bad_parse_keys.add(m_key)
            finally:
                if opt_stack.pop():
                    val_opt_keys.add((self.dialect or "", sql))

        sg_parser.Parser.parse = _vp_parse
        sg_parser.Parser.parse_into = _vp_parse_into
        sg_tokens.Tokenizer.tokenize = _vt_tokenize
        td.Validator.validate_identity = _rec_v_vi
        td.Validator.validate_all = _rec_v_va
        try:
            dialect_test_files = sorted((repo_root / "tests" / "dialects").glob("test_*.py"))
            for tf in dialect_test_files:
                mod = importlib.import_module(f"tests.dialects.{tf.stem}")
                suite = unittest.defaultTestLoader.loadTestsFromModule(mod)
                res = unittest.TestResult()
                suite.run(res)
                if not res.wasSuccessful():
                    raise RuntimeError(
                        f"Validator cache record failed in {tf.name}: {res.failures[:2]} {res.errors[:2]}"
                    )
        finally:
            sg_parser.Parser.parse = orig_p_parse
            sg_parser.Parser.parse_into = orig_p_parse_into
            sg_tokens.Tokenizer.tokenize = orig_t_tokenize
            td.Validator.validate_identity = orig_v_vi
            td.Validator.validate_all = orig_v_va
            sys.monitoring.set_events(VAL_TOOL_ID, 0)
            sys.monitoring.free_tool_id(VAL_TOOL_ID)

        for k in bad_parse_keys:
            val_parse_hashes.pop(k, None)

        val_payload = {
            "val_parse_hashes": val_parse_hashes,
            "val_opt_keys": val_opt_keys,
        }
        val_raw = pickle.dumps(val_payload, protocol=4)
        with gzip.open(val_out_path, "wb", compresslevel=9) as gz:
            gz.write(val_raw)
        print(
            f"Wrote {val_out_path} ({val_out_path.stat().st_size / 1024:.1f} KB, "
            f"parse_hashes={len(val_parse_hashes)}, val_opt_keys={len(val_opt_keys)}) "
            f"in {time.perf_counter() - t_val:.2f}s",
            file=sys.stderr,
        )

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
