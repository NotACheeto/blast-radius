"""Build compact tpc_cache.pkl.gz with preloaded TPC-DS tables and baseline execution/plan hashes."""

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

    import tests.test_executor as te
    from sqlglot import parse_one, transpile
    from sqlglot.optimizer import optimize
    from sqlglot.planner import Plan

    te.TestExecutor.setUpClass()
    try:
        tpcds_tables = {
            name: (tbl.columns, tbl.rows)
            for name, tbl in te.TestExecutor.tpcds_tables.items()
        }
        tpch_sqls = list(te.TestExecutor.tpch_sqls)
        tpcds_sqls = list(te.TestExecutor.tpcds_sqls)

        tpch_opt_duck: dict[int, tuple[str, str]] = {}
        for i, (_, sql, optimized) in enumerate(tpch_sqls):
            tpch_opt_duck[i] = (
                transpile(sql, write="duckdb")[0],
                transpile(optimized, write="duckdb")[0],
            )

        te.initializer(te.TPCDS_SCHEMA, te.TestExecutor.tpcds_tables)
        tpcds_hashes: dict[int, str] = {}
        tpcds_plan_hashes: dict[int, str] = {}
        for i, (meta, sql, _) in enumerate(tpcds_sqls):
            if meta.get("execute"):
                expr = parse_one(sql)
                opt_expr = optimize(expr, te.TPCDS_SCHEMA, leave_tables_isolated=True)
                plan_str = repr(Plan(opt_expr))
                tbl = te.mp_execute(expr, meta)
                duck_sql = transpile(sql, write="duckdb")[0]
                tpcds_hashes[i] = _hash_result(duck_sql, tbl.columns, tbl.rows)
                tpcds_plan_hashes[i] = hashlib.sha256(
                    (duck_sql + "\0" + repr(opt_expr) + "\0" + plan_str).encode("utf-8")
                ).hexdigest()
    finally:
        te.TestExecutor.tearDownClass()

    payload = {
        "tpcds_tables": tpcds_tables,
        "tpch_sqls": tpch_sqls,
        "tpcds_sqls": tpcds_sqls,
        "tpch_opt_duck": tpch_opt_duck,
        "tpcds_hashes": tpcds_hashes,
        "tpcds_plan_hashes": tpcds_plan_hashes,
    }

    raw = pickle.dumps(payload, protocol=4)
    with gzip.open(out_path, "wb", compresslevel=9) as gz:
        gz.write(raw)

    print(
        f"Wrote {out_path} ({out_path.stat().st_size / 1024:.1f} KB, "
        f"tpch_opt={len(tpch_opt_duck)}, tpcds={len(tpcds_hashes)}) in {time.perf_counter() - t0:.2f}s",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
