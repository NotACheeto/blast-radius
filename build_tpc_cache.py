"""Build compact tpc_cache.pkl.gz with preloaded TPC-DS tables, baseline hashes, and test caches."""

from __future__ import annotations

import argparse
import gzip
import hashlib
import os
from pathlib import Path
import pickle
import sys
import time


def _hash_result(duck_sql: str, columns, rows) -> str:
    return hashlib.sha256(
        pickle.dumps((duck_sql, tuple(columns), list(rows)), protocol=4)
    ).hexdigest()


def _plan_py_hash(py_exec, plan, planner_mod) -> str:
    """Hash all generated Python expressions across a Plan (and nested subqueries) without running row loops."""
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


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", required=True, help="Path to sqlglot checkout")
    parser.add_argument("--out", required=True, help="Output tpc_cache.pkl.gz path")
    args = parser.parse_args()

    t0 = time.perf_counter()
    repo_root = Path(args.repo).resolve()
    out_path = Path(args.out).resolve()
    os.environ["SKIP_INTEGRATION"] = "0"
    os.chdir(repo_root)
    if str(repo_root) not in sys.path:
        sys.path.insert(0, str(repo_root))

    import inspect
    import unittest
    from concurrent.futures import ThreadPoolExecutor

    import duckdb
    import sqlglot as sg
    import tests.test_executor as te
    import tests.test_optimizer as to
    from sqlglot import optimizer, parse_one, planner, transpile
    from sqlglot.executor.python import PythonExecutor
    from sqlglot.executor.table import Table, ensure_tables
    from sqlglot.optimizer import optimize
    from sqlglot.optimizer.scope import build_scope, traverse_scope
    from sqlglot.planner import Plan
    from sqlglot.schema import MappingSchema
    from sqlglot.serde import dump as serde_dump

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
        tpcds_py_hashes: dict[int, str] = {}
        tpcds_duck_sqls: dict[int, str] = {}

        for i, (meta, sql, _) in enumerate(tpcds_sqls):
            if meta.get("execute"):
                expr = parse_one(sql)
                opt_expr = optimize(expr, te.TPCDS_SCHEMA, leave_tables_isolated=True)
                opt_exprs[i] = opt_expr
                plan = Plan(opt_expr)
                duck_sql = transpile(sql, write="duckdb")[0]
                tpcds_duck_sqls[i] = duck_sql
                tpcds_plan_hashes[i] = hashlib.sha256(
                    (duck_sql + "\0" + repr(opt_expr) + "\0" + opt_expr.sql()).encode("utf-8")
                ).hexdigest()
                tpcds_opt_dumps[i] = serde_dump(opt_expr)
                tpcds_py_hashes[i] = _plan_py_hash(PythonExecutor(), plan, planner)

        # Build coverage-preserving pruned TPC-DS tables (keep first 48 rows per table + up to 4 matches per Scan filter)
        raw_full = {name: (tbl.columns, tbl.rows) for name, tbl in te.TestExecutor.tpcds_tables.items()}
        rows_id_to_name = {id(tbl.rows): name for name, tbl in te.TestExecutor.tpcds_tables.items()}
        keep_indices = {
            name: set(range(min(len(tbl.rows), 48)))
            for name, tbl in te.TestExecutor.tpcds_tables.items()
        }
        t_ens_full = ensure_tables(te._tables)
        orig_pf = PythonExecutor._project_and_filter

        def _trace_pf(self, context, step, iterator):
            if step.condition and len(context.tables) == 1:
                t = next(iter(context.tables.values()))
                tname = rows_id_to_name.get(id(t.rows))
                if tname is not None:
                    cond = self.generate(step.condition)
                    matched = 0
                    reader = t.reader
                    for idx, row in enumerate(t.rows):
                        reader.row = row
                        if context.eval(cond):
                            keep_indices[tname].add(idx)
                            matched += 1
                            if matched >= 4:
                                break
            return orig_pf(self, context, step, iterator)

        PythonExecutor._project_and_filter = _trace_pf
        try:
            for opt_expr in opt_exprs.values():
                PythonExecutor(tables=t_ens_full).execute(Plan(opt_expr))
        finally:
            PythonExecutor._project_and_filter = orig_pf

        te.TestExecutor.tpcds_tables = {
            name: Table(cols, [rows[idx] for idx in sorted(keep_indices[name])])
            for name, (cols, rows) in raw_full.items()
        }
        te.initializer(te.TPCDS_SCHEMA, te.TestExecutor.tpcds_tables)
        t_ens_pruned = ensure_tables(te._tables)
        for i, opt_expr in opt_exprs.items():
            tbl = PythonExecutor(tables=t_ens_pruned).execute(Plan(opt_expr))
            tpcds_hashes[i] = _hash_result(tpcds_duck_sqls[i], tbl.columns, tbl.rows)

        tpcds_tables = {
            name: (tbl.columns, tbl.rows)
            for name, tbl in te.TestExecutor.tpcds_tables.items()
        }
    finally:
        te.TestExecutor.tearDownClass()

    # Pre-compute test_optimize_in_nulls DuckDB-optimized baseline SQL strings
    to_inst = to.TestOptimizer("test_optimize_in_nulls")
    to_inst.setUp()
    in_nulls_opt_duck: list[str] = []
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
                in_nulls_opt_duck.append(
                    optimizer.optimize(
                        sql, schema=to_inst.schema, dialect="duckdb"
                    ).sql("duckdb")
                )

    # Record DuckDB fetchall() and .df() baselines across all DuckDB-backed TestOptimizer methods
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
    try:
        duck_methods = [
            m
            for m, fn in inspect.getmembers(to.TestOptimizer, inspect.isfunction)
            if m.startswith("test_")
            and (
                "conn" in inspect.getsource(fn)
                or "duckdb" in inspect.getsource(fn)
                or "execute=True" in inspect.getsource(fn)
            )
        ]
        for m in duck_methods:
            tc = to.TestOptimizer(m)
            res = unittest.TestResult()
            tc.run(res)
            if not res.wasSuccessful():
                raise RuntimeError(f"DuckDB cache record failed in {m}: {res.failures} {res.errors}")
    finally:
        duckdb.connect = orig_duck_connect
        to.assert_frame_equal = orig_afe
        try:
            real_class_conn.close()
        except Exception:
            pass

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
        "tpcds_py_hashes": tpcds_py_hashes,
        "in_nulls_opt_duck": in_nulls_opt_duck,
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
        f"in_nulls={len(in_nulls_opt_duck)}, duck_rows={len(duck_rows_cache)}, "
        f"duck_df={len(duck_df_cache)}, scope={scope_stress_counts}) "
        f"in {time.perf_counter() - t0:.2f}s",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
