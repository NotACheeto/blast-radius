# Blast Radius AI Handoff & Architecture Guide

This document describes the repository layout, problem constraints, three-stage architecture, implemented optimizations, verification harness, and benchmark results for the **Blast Radius** (`sqlglot`) test selector.

- **Repository:** `https://github.com/NotACheeto/blast-radius`
- **Target Branch / Latest Pushed Commit:** `main` @ `95c227dc14b882e6c7e8aa9a91a9d06aa75d91cf`
- **Pinned `sqlglot` Commit:** `eb11aec4be8cb2122afe713a4816662c3f0fb2fa`
- **Base Docker Image:** `python:3.13-slim@sha256:e48f59cdba69a3cbd9ed2cf0f348d90d45a8d350d98134cf1070bc106ee9ed90`

---

## 1. Problem, Sandbox Limits, and Scoring Rules

Source of truth: [RULES.md](file:///c:/Users/bjmar/Downloads/hackathonOSU/RULES.md), [SCORING.md](file:///c:/Users/bjmar/Downloads/hackathonOSU/SCORING.md), [score.py](file:///c:/Users/bjmar/Downloads/hackathonOSU/score.py).

- **Inputs inside container:**
  - `/data/tests.json`: `1,620` numbered active tests (`0..1619`, with recorded `seconds`) and `1` skipped test.
  - `/data/commits/<id>.patch`: Standalone unified diffs against `sqlglot @ eb11aec4be8cb2122afe713a4816662c3f0fb2fa`.
  - `/app/sqlglot`: Pre-installed, bytecode-compiled (`python -m compileall -q /app/sqlglot`) read-only checkout built in [Dockerfile](file:///c:/Users/bjmar/Downloads/hackathonOSU/Dockerfile).
- **Output format (`stdout`):**
  - Strictly one valid UTF-8 JSON line per commit (no logs on stdout, no BOM, `<= 2 MB`):
    `{"commit": "<id>", "workers": [[12, 845], [3]]}` (`"workers": []` skips running any tests).
  - Up to `MAX_WORKERS = 8` non-empty workers per commit, no duplicate or out-of-range test numbers.
- **Exact Scoring Formula:**
  - Per-test duration: `round(seconds * 1000)` ms (`math.floor(seconds * 1000 + 0.5)`).
  - Worker boot penalty: `WORKER_COST_MS = 2000` ms (`2.0 s`) per non-empty worker.
  - Commit simulated cost: `0` if `workers == []`, else `max(worker_load_ms) + 2000 * len(workers)`.
  - Miss penalty: `+300.0 s` added to `simulated` for every commit where `workers` omits at least one truly failing test.
  - Total run score: `simulated + CPU_time` (user + system CPU across all container processes; median of 3 runs rounded to `0.1 s`).
- **Hard Execution Constraints:**
  - `--network none --cpus 2 --memory 4096m --memory-swap 4096m --pids-limit 256 --read-only --tmpfs /tmp:rw,size=64m,mode=1777 --user 65534:65534`.
  - Repo size must remain `<= 20 MB` (`6.58 MiB` packed before latest cache update; map + caches total `5.74 MiB`).
  - Wall-clock budget: 3 minutes (~180 s practice), ~4.5 minutes (final batch).

---

## 2. File Inventory

| File | Size | Purpose |
| --- | --- | --- |
| [Dockerfile](file:///c:/Users/bjmar/Downloads/hackathonOSU/Dockerfile) | 1,230 B (16 lines) | Installs [requirements.lock](file:///c:/Users/bjmar/Downloads/hackathonOSU/requirements.lock), fetches/compiles pinned `sqlglot`, copies prebuilt binary caches + `selector.py`, sets `PYTHONHASHSEED=0` & single-thread BLAS env vars. |
| [build_map.py](file:///c:/Users/bjmar/Downloads/hackathonOSU/build_map.py) | 46,026 B (1,134 lines) | Offline builder for `blast_map.pkl.gz` using `sys.monitoring` (`LINE` + `PY_START`), `setUpClass` tracing, file-open hooks, runtime tracers (`Expr`, `Dialect`, `_TrackedDict` keys/iters, SQL tokens, time format substrings), and Python `ast` extraction. |
| [blast_map.pkl.gz](file:///c:/Users/bjmar/Downloads/hackathonOSU/blast_map.pkl.gz) | 1,783,198 B | Compressed binary runtime/AST/import/dict-key/token dependency map of baseline `sqlglot` (`1,741.4 KB`). |
| [build_tpc_cache.py](file:///c:/Users/bjmar/Downloads/hackathonOSU/build_tpc_cache.py) | 51,179 B (1,238 lines) | Offline builder for `tpc_cache.pkl.gz` & `val_cache.pkl.gz` (pruned TPC-DS tables, baseline hashes, lossless per-rule TPC-DS checkpoints, optimizer fixture/annotation hashes & dumps, DuckDB caches, validator parse hashes & `val_opt_keys`). |
| [tpc_cache.pkl.gz](file:///c:/Users/bjmar/Downloads/hackathonOSU/tpc_cache.pkl.gz) | 3,886,973 B | Compressed precomputed optimizer/TPC-DS/executor/DuckDB baseline caches (`3,795.9 KB`, `PYTHONHASHSEED=0`). |
| [val_cache.pkl.gz](file:///c:/Users/bjmar/Downloads/hackathonOSU/val_cache.pkl.gz) | 349,557 B | Compressed dialect validator exact AST parse hashes (`12,270`) and optimizer-touching key set (`4,187`) (`341.4 KB`). |
| [selector.py](file:///c:/Users/bjmar/Downloads/hackathonOSU/selector.py) | 213,224 B (4,918 lines) | Main entrypoint (`CMD ["python", "/app/selector.py"]`): Stage 1 static triage & dict/block AST narrowing, Stage 2 isolated in-process verification & stage-isolated accelerators, Stage 3 bounded-BnB worker bin packing. |
| [Makefile](file:///c:/Users/bjmar/Downloads/hackathonOSU/Makefile), [score.py](file:///c:/Users/bjmar/Downloads/hackathonOSU/score.py), `sample/` | — | Local sample commits (`30` commits + `answers.json`), Docker run flags, and exact scorer. |

---

## 3. Architecture Overview

`selector.py` uses a **3-Stage Hybrid Architecture**: fast static triage to shortlist candidate tests with zero misses, followed by low-overhead isolated execution to prune false positives down to exact failing tests (`workers: []` for no-op/passing commits), and finally optimal worker bin-packing.

```
  patch file ──► [Stage 1: BlastSelector.triage_commit] ──(0 cands)──► {"workers": []} (0 ms)
                        │
                  (cands > 0)
                        ▼
             [Stage 2: 2x os.fork() Workers + /tmp Symlink Overlay]
              ├─ tier1_fast  ──► subTest fail-fast + accelerators
              └─ tier2_heavy ──► test_tpcds <-> test_execute_tpcds coordination + tpc_cache
                        │
                 (exact failed tests)
                        ▼
             [Stage 3: pack_workers (k=1..8 LPT + swap search)] ──► stdout JSON line
```

### Offline Maps (`build_map.py` -> `blast_map.pkl.gz`)
Pre-imports all `sqlglot.*` modules before enabling `sys.monitoring` (`LINE` and `PY_START`) so `__pycache__` reads never pollute coverage, wraps `concurrent.futures.ProcessPoolExecutor` with an in-process pickling `InlinePoolExecutor` (so `Expr.__reduce__` / serde paths are traced), traces `cls.setUpClass()` into `setup_lines`/`setup_funcs`/`setup_modules`, hooks `builtins.open`/`pathlib.Path.open`/`os.path` file reads, runs lightweight runtime tracers (`expr_to_tests`, `dialect_used_tests`, `_TrackedDict` key/iter maps `dict_key_to_tests` & `dict_iter_tests`, `token_to_tests`, `time_substr_to_tests`), and precomputes `dialect_tests`, `cross_dialect_tests`, `subclasses`, and `reverse_mod_files`.

### Offline Test Caches (`build_tpc_cache.py` -> `tpc_cache.pkl.gz` & `val_cache.pkl.gz`)
Built inside Linux `python:3.13-slim` with `PYTHONHASHSEED=0` containing:
- `tpcds_tables`, `tpch_sqls`, `tpcds_sqls`, `tpch_opt_duck`, `tpcds_duck_sqls`, `tpcds_hashes`, `tpcds_plan_hashes`, `tpcds_opt_dumps`, `tpcds_raw_dumps_z`, `tpcds_dump_py_hashes`, `tpcds_plan_expr_dumps_z`.
- `tpcds_rule_files`, `tpcds_rule_hashes`, `tpcds_rule_checkpoints_z` (per-rule lossless `_pack_expr` checkpoints for all `0..12` TPC-DS `RULES`), `tpcds_all_opt_dumps_z`, `tpcds_no_gen_mask` (`94/99`).
- `opt_fixture_meta` (all 23 optimizer fixtures with lossless `_hash_expr_exact` parse hashes, self-verified `aux_calls`, and verified `opt_dumps_z`), `annotate_funcs_meta` (`2,435` parse hashes), `in_nulls_opt_duck`, `in_nulls_parse_hashes`, `in_nulls_opt_dumps_z`.
- `duck_rows_cache`, `duck_df_cache`, `scope_stress_counts`.
- `val_cache.pkl.gz`: `12,270` lossless `_hash_expr_exact` validator parse hashes and `4,187` `val_opt_keys` (tracked with `sys.monitoring` for queries exercising `sqlglot/optimizer/*`).

### Stage 1: Static Diff Analysis & Candidate Triage (`BlastSelector.triage_commit`)
1. **In-memory patching (`parse_patch`, `apply_hunks`)**: Handles modified, new, deleted, and renamed files.
2. **Fast AST equivalence (`_asts_structurally_equal`, `_CanonicalizeAST`)**: Compares statements overlapping changed hunk lines first (short-circuiting on edits in `<2 ms`), canonicalizes `==`/`!=` <-> `is`/`is not` on `None`, pure non-str/non-int enums (`_PURE_SQLGLOT_ENUMS`), and `self.normalization_strategy` vs `NormalizationStrategy.<X>` inside `sqlglot/dialects/dialect.py`.
3. **Granular candidate lookup:**
   - **Functions & AST block narrowing (`_func_tests`, `_ast_narrow_func_tests`):** Narrows unchanged function signatures down to changed compound/statement AST spans (`If`/`For`/`While`/`With`/`Try`).
   - **Dict-key AST narrowing (`_ast_diff_dict_attr`, `_resolve_spread_str_map`):** Narrows `TRANSFORMS`, `TYPE_MAPPING`, `PROPERTIES_LOCATION`, `FUNCTIONS`, `STATEMENT_PARSERS`, `KEYWORDS`, `SINGLE_TOKENS`, `TIME_MAPPING`/`FORMAT_MAPPING` (including inherited `**Parent.ATTR` spreads and `STRICT_TIME_FORMATS`) down to only tests touching the edited key(s) + runtime iterators.
   - **Dialect Inheritance, Runtime Readers, & Transitive Package Imports (`_descendant_dialects`, `_tests_importing_file`):** Uses runtime `dialect_used_tests`, propagates `transitive=True` BFS across `__init__.py` package imports (catching `tests/test_dialect_imports.py` on `sqlglot/diff.py` syntax errors), and excludes false `TokenType` snake-case lookups outside `sqlglot/expressions/datatypes.py`.

### Stage 2: Parallel Overlay Execution & Test Accelerators
1. **Master-Worker Architecture (`main` / `_linux_worker_loop`):**
   - Calls `_prewarm_libraries()` once before `os.fork()` (loads `_TPC_CACHE`, `numpy`, `pandas`, `duckdb`, `sqlite3`, `yaml`, `pytz`, etc. with `OPENBLAS_NUM_THREADS=1`).
   - Creates `2` zero-copy symlink/hardlink mirrors in `/tmp/sg_work/w{0,1}` (`_build_overlay`).
   - Schedules `.py` commits LPT-first (forking a short-lived child per commit to keep parent clean) and fixture-only commits warm in-process (`warm_in_process=True`).
   - `_apply_overlay_patches` swaps modified files and unlinks corresponding `__pycache__/*.pyc` symlinks so Python compiles patched files in `/tmp`; `_restore_overlay` restores symlinks after each commit.
2. **Two-Tier Verification (`_process_commit_task`, `_run_commit_tiers_in_process`):**
   - Splits candidates into `tier1_fast` and `tier2_heavy` (`TPC_HEAVY_METHODS` + `test_tpcds`), sorted by ascending baseline duration so quick tests fail fast.
   - Runs both `tier1_fast` and `tier2_heavy` (within `wall_limit * 0.85`, where `wall_limit = max(90.0, 3.2 * len(patch_paths))`) so passing `tier2` tests (like `#1106 test_execute_tpcds`, `21.454 s`) are still pruned even when `tier1_fast` has failures.
3. **Runtime Test Accelerators (`_execute_tests_in_overlay`, `_install_optimizer_accelerators`, `_patch_test_executor_with_cache`):**
   - **Subtest Fail-Fast (`_FastSubTestCM`):** Propagates first subtest failure immediately out of parameterized loop tests (`validate_all`, `check_file`).
   - **In-Process Bounded-Pickle Pool (`InlinePoolExecutor`):** Replaces `ProcessPoolExecutor` in-process; when `_needs_pickle(patched_files)` is true (`serde.py`, `executor/table.py`, `expressions/*`), limits full pickle/unpickle round-trips to `pickle_budget = 2` futures per test method and `pickled_once` in `_fast_mp_execute`.
   - **Dialect `Validator` Filtering (`_fast_va`, `_fast_vi`, `_fast_parser_va` + `_TrackedAssertLogsCM`):** On dialect-scoped commits (`active_dialects`), classes whose `cls.dialect not in active_dialects` filter `validate_all(read, write)` entries by comma-split dialect key (`k.split(",")[0].strip().lower() in _ad`) and short-circuit `validate_identity` via `self.parse_one(sql)`. Whenever `with self.assertLogs(...):` is active (`_ASSERT_LOGS_DEPTH > 0`), `_TrackedAssertLogsCM` delegates transparently to the unpatched `Validator` methods so log assertions never false-fail.
   - **TPC-DS & Executor Acceleration (`_patch_test_executor_with_cache`, `_fast_mp_execute`):**
     - Uses pre-pruned `tpcds_tables` + three-tier verification: direct `Expr.load(tpcds_opt_dumps[i])` when only `executor/*` or `planner.py` changed; `tpcds_plan_hashes` (`optimize` only) when neither executor nor Python generator changed; and `_plan_py_hash` verification when generator/dialect/eliminate_joins changed without row-engine changes.
     - Coordinates `TestOptimizer::test_tpcds` (`#1440`) and `TestExecutor::test_execute_tpcds` (`#1106`): if `#1440` fails at query `i`, `_COMMIT_TPCDS_FAILED_IDX = i - 1` runs first in `_fast_mp_execute` (~0.11 s); if `#1440` passes and optimizer entrypoints didn't change, query `0` verifies `leave_tables_isolated=True` and skips re-optimizing the remaining queries (`return` when `not executor_touched`, or load `tpcds_opt_dumps[i]` when `can_use_py_hash`).
   - **Optimizer & DuckDB Caches:** Lazy DuckDB initialization (`_install_lazy_optimizer_conn`, `_CachedDuckConn`, `_FastDF`), modified-first fixture ordering (`_scoped_loader`), `qualify_columns_ddl` before `qualify_columns` (`_reordered_check_file`), full 180-query `opt_sql == in_nulls_opt_duck[idx]` fast check (`_fast_in_nulls`), and bounded stress-test loop counts with `except AssertionError: _orig(self)` fallback (`test_scope`, `test_deep_ast_type_annotation`, `test_max_nodes` at `5000`/`2500`, `test_is_precedence`, `test_generator_memory`, `test_recursion`, `test_values`).

### Stage 3: Worker Scheduler (`pack_workers`)
Tries every worker count $k \in \{1 \dots \min(8, |S|)\}$, sorts failed tests descending by `test_ms`, performs greedy Longest Processing Time (LPT) assignment, applies iterative single-item move and pairwise swap local search off the busiest bucket, and picks the $k$ minimizing $\max(\text{loads}) + 2000 \times k$.

---

## 4. Iteration History & Verified Metrics

| Git SHA | Description | Sample Simulated | Sample Misses | Sample CPU (Middle of 3) | Practice Score / Stress Test |
| --- | --- | --- | --- | --- | --- |
| `545c0ca2` (`BB-54958303`) | Earlier baseline | — | — | — | Practice: `499.9 s` (`439.477 s` sim [`139.477 s` base + `300 s` miss penalty], `60.41 s` CPU, `1` miss) |
| `929351f5` (`BB-BE1EA532`) | Rebuilt maps + full tier2 + `_ATTR_DERIVED_SYMBOLS` + pickle | `94.351 s` | `0` | `21.99 s` | Practice: `190.0 s` (`94.455 s` sim, `0` misses, `95.55 s` CPU); Stress: `20/20` |
| `1e2a98ea` | `pickle_budget=2`, 1-hop imports, dead-method pruning, `_CanonicalizeAST`, TPC-DS coordination, `test_max_nodes` fix | `94.351 s` | `0` | `9.866 s` (`5.37 s` wall) | Stress: `20/20` caught (`116.411 s` CPU, `59.14 s` wall) |
| `95c227dc` (Base `HEAD`) | `Validator` `active_dialects` hooks + `_ASSERT_LOGS_DEPTH`, expr/typing pruning, `eliminate_joins` py-hash, recursion scaling | `94.351 s` | `0` | `8.940 s` (`4.86 s` wall) | Practice: `157.9 s` (`94.455 s` sim, `63.48 s` CPU, `0` misses); 33-commit Stress: `293.643 s` CPU |
| Working tree (unpushed) | Binary maps + runtime dict/token/expr tracers, dict-key & AST block narrowing, lossless exact hashing, `parser_only`/`gen_only`/`opt_only` checkpoints & `val_opt_keys`, selective `sqlglot` core reuse, BnB packer | `94.351 s` | `0` | **`6.319 s`** (`3.73 s` wall) | 33-commit Stress: **`33/33` exact (`0` missed, `0` extra)**, `143.529 s` CPU (`73.74 s` wall) |

*Working-tree `sample/` runs verified inside Docker `--platform linux/amd64 --network none --cpus 2 --memory 4096m --read-only`: Run 1 = `6.319 s`, Run 2 = `6.277 s`, Run 3 = `6.499 s` container CPU (`Simulated: 94.351 s`, `Misses: 0`, zero `nanobind` warnings).*

---

## 5. Critical Edge Cases & Pitfalls Discovered

1. **Never prune subtests inside `_fast_in_nulls` (`test_optimize_in_nulls`):** Correlated subqueries (`w_idx >= 4`) combined with `AND`/`OR` outer predicates (`s_idx in (9, 10)`) exercise `LIST_FILTER` code paths (`m03_factory_rename_func`) that are NOT triggered on `w_idx == 0`. Keep all 180 queries enabled (`~0.3–0.46 s`).
2. **Never patch `Validator.validate_identity` to return `None`:** Over 150 calls in `tests/dialects/test_*.py` chain `.selects[0]`, `.assert_is(...)`, or pass it to `annotate_types(...)`. Always return `self.parse_one(sql)` and delegate to `_orig` whenever `_ASSERT_LOGS_DEPTH > 0` or `check_command_warning=True`.
3. **Never add an unconstrained top-level reader fallback inside `_reader_tests_for_symbol`:** Class/module-level dicts like `TRANSFORMS = {..., exp.TriggerProperties: ...}` in `sqlglot/generator.py:826` have `rsid is None` and `not enclosing_defs`; pulling `_tests_importing_file(rf)` there blows up leaf expression commits like `ktz3` from `4` tests (`0.20 s`) to `1,369` tests (`21.94 s`).
4. **Never pass raw `sqlglot/parser.py` node count thresholds without verifying against `_node_count`:** `width=60, depth=100` yields ~`6,060` `_node_count`, so `max_nodes=10_000` never raises `ParseError`. Keep `max_nodes=5_000` / `2_500` with `except AssertionError: _orig(self)`.
5. **Rebuilding maps must happen in the Linux container (`PYTHONHASHSEED=0`):** Never regenerate `blast_map.json.gz` or `tpc_cache.pkl.gz` on Windows; Python/SQLite/path differences and hash seeds must match `python:3.13-slim`.
6. **PowerShell stdout redirection Warning:** PowerShell `>` writes UTF-16LE with BOM, which fails `score.py` (`not_utf8`). Always capture raw bytes via Python (`Path("output.jsonl").write_bytes(proc.stdout)`).

---

## 6. Commands for Local Verification

**1. Build Docker Image:**
```powershell
docker build --platform linux/amd64 --tag blast-radius-entry .
```

**2. Run Sample Scorer (PowerShell-safe UTF-8 capture):**
```powershell
python -c "
import subprocess, pathlib
root = pathlib.Path('.')
p = subprocess.run([
    'docker', 'run', '--rm', '--platform', 'linux/amd64', '--network', 'none',
    '--cpus', '2', '--memory', '4096m', '--memory-swap', '4096m', '--pids-limit', '256',
    '--read-only', '--tmpfs', '/tmp:rw,size=64m,mode=1777', '--cap-drop', 'ALL',
    '--security-opt', 'no-new-privileges', '--user', '65534:65534', '--env', 'HOME=/tmp',
    '--volume', str((root / 'sample' / 'commits').resolve()) + ':/data/commits:ro',
    '--volume', str((root / 'sample' / 'tests.json').resolve()) + ':/data/tests.json:ro',
    'blast-radius-entry',
], capture_output=True)
pathlib.Path('output.jsonl').write_bytes(p.stdout)
print(p.stderr.decode('utf-8', errors='replace'))
"
python score.py sample sample/answers.json output.jsonl
```

**3. Rebuild Maps Inside Container (only needed if `build_map.py` or `build_tpc_cache.py` changes):**
```powershell
docker run --rm --platform linux/amd64 --network none --env PYTHONHASHSEED=0 --volume ${PWD}:/work --entrypoint python3 blast-radius-entry /work/build_map.py --repo /app/sqlglot --tests /work/sample/tests.json --out /work/blast_map.pkl.gz
docker run --rm --platform linux/amd64 --network none --env PYTHONHASHSEED=0 --volume ${PWD}:/work --entrypoint python3 blast-radius-entry /work/build_tpc_cache.py --repo /app/sqlglot --out /work/tpc_cache.pkl.gz --val-out /work/val_cache.pkl.gz
```
