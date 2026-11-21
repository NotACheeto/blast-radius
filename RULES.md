# Blast Radius Track — Rules & Scoring Reference

---

## Rule File 1: How a run is scored

These are the exact rules. `score.py` in this kit and the scorer on the server each follow them, and the two are compared on thousands of outputs before the event. For the same output, the simulated seconds you compute locally are the simulated seconds the server computes. The board's number also holds the CPU time your container used on the server, which `make sample` does not measure, and it is the middle of 3 runs.

### Inputs

`/data/tests.json` is `{"tests": [...]}`. Each entry is `{"number": 12, "id": "tests/test_parser.py::TestParser::test_union", "file": "tests/test_parser.py", "seconds": 0.031}`. Numbers run from 0 with no gaps, in the order listed. `seconds` has three decimals. A second key, `skipped`, names tests that our environment skips. They cannot fail and have no number.

`/data/commits/<id>.patch` is one unified diff against the pinned sqlglot commit. The commit's id is the file name without `.patch`.

The answers, which only the sample set ships, are `{"commits": {"<id>": {"failing": [12, 845], "kind": "code"}}}`. `failing` lists the numbers of the tests that fail on that commit.

### Reading your output

Your program's stdout is decoded as UTF-8 and split on `\n`. When stdout ends with a newline, the empty piece after it is ignored. Empty stdout has no lines. Every other piece is a line, numbered from 1. A byte order mark is not removed, so a line that starts with one is not JSON.

Each line is checked in this order, and the first rule a line breaks rejects the run. The message names the rule and the line number, never the line's content.

| Order | Rule | Code |
| --- | --- | --- |
| 1 | The line is standard JSON. `NaN` and `Infinity` are not. | `not_json` |
| 2 | It is an object with exactly two keys, `commit` and `workers`. `commit` is a string and `workers` is a list. | `wrong_shape` |
| 3 | `commit` is the id of a commit in `/data/commits`. | `unknown_commit` |
| 4 | No earlier line has the same `commit`. | `repeated_commit` |
| 5 | Every item of `workers` is a list, and every item of those lists is a whole number. `3.0` counts as 3. `true`, `"3"` and `3.5` do not. | `wrong_shape` |
| 6 | Every number is a test number in `tests.json`. | `unknown_test` |
| 7 | No number appears twice in the line, in one worker or across workers. | `repeated_test` |
| 8 | After empty workers are dropped, at most 8 workers remain. | `too_many_workers` |

After the last line: every commit in `/data/commits` has a line (`missing_commit`, reported without a line number). Stdout that is not UTF-8 is `not_utf8`.

Lines may come in any order. Tests may come in any order inside a worker. Empty workers are dropped before anything is counted, so `[[1, 2], []]` is one worker.

### Cost of one commit

Arithmetic is in whole milliseconds, so no rounding error can separate two teams. A test's duration is `round(seconds * 1000)` milliseconds.

- A worker's load is the sum of its tests' durations.
- With no workers the cost is 0.
- Otherwise the cost is the largest load, plus the worker cost for every worker.

The worker cost is 2 seconds.

### Misses

A commit is a miss when at least one of its failing tests is in none of its workers. Each miss adds 300 seconds. The commit's own cost still counts.

### A run's total

```
simulated = sum of commit costs + 300 s x misses
total     = simulated + CPU time
```

CPU time is what every process in your container used, user and system together, from start to exit, in microseconds. The build is not charged.

### A submission's score

Your image runs 3 times. All 3 must be valid. The score is the middle of the 3 totals, rounded to a tenth of a second with halves rounded up: `floor((microseconds + 50000) / 100000) / 10`.

Lower is better. Equal scores rank the earlier submission first.

---

## Rule File 2: Problem Statement, Track Rules, Build & Run Limits, and Submission Requirements

### The problem

Every fast CI system has to decide which tests a commit needs. Run them all and you wait; skip the wrong one and a bug ships.

You get a batch of code changes to sqlglot, a Python SQL parser. For each change, say which of its tests to run and how to split them across up to 8 workers.

Most changes break at least one test. Some break nothing at all, and the right answer for those is to run nothing.

### Get started

Download `blast-radius-sample.tar.gz` below and unpack it into an empty folder (it has no top-level folder). You need Docker, make, and Python 3.9 or newer.

Run `make sample` to build the starter image, run it under the limits below on the 30 sample commits, and score what it printed.

### What to hand in

- Submit a public GitHub repository with a `Dockerfile` at its top, and the commit to score. Any language, any libraries, and any amount of AI are allowed.
- Every change your program receives is a patch against sqlglot at commit `eb11aec4be8cb2122afe713a4816662c3f0fb2fa`. Each one stands alone.
- `/data/commits/<id>.patch` holds one unified diff per commit.
- `/data/tests.json` lists every test, numbered, with its file path and recorded runtime in seconds.
- Print one JSON line per commit to stdout: `{"commit": "k7q2", "workers": [[12, 845, 901], [3, 77]]}`. Each inner list is one worker's test numbers, and `"workers": []` runs nothing.
- Send logs to stderr. Any other output on stdout, or more than 2 MB on stdout, rejects the run.

### How it is scored

- A commit costs the recorded test seconds of its busiest worker plus 2 seconds for every worker, up to 8 workers, and running nothing costs 0.
- A commit whose selection leaves out any test that fails on it adds 300 seconds.
- Your program's CPU seconds are added to the total, and running sqlglot's tests while you decide is allowed and charged here.
- Your image runs 3 times, and the middle total counts, rounded to 0.1 s.

### What fails means

A test fails on a commit when pytest reports a failure, an error, or a timeout for it, or when its file cannot be imported. A test with subtests is one test, and one failing subtest fails it.

A change that only adds a comment is not promised to be harmless.

### Limits

- Your repository may hold at most 20 MB. Git submodules and Git LFS files are not fetched, so clone sqlglot in your Dockerfile and commit maps as plain files.
- Builds have network access, 4 cores, 8 GB of memory, and 10 minutes. You may install sqlglot and run its tests during the build to make coverage or import maps.
- Every submission is built from nothing, so a build that runs sqlglot's tests takes minutes each time you submit. A map you make once and commit builds in seconds.
- Runs have no network access, 2 cores, 4 GB of memory, and 3 minutes for the whole batch (4.5 minutes in the final, which has about 1.5x as many commits).
- Your program runs as user `nobody` with `HOME=/tmp`, a read-only disk, an empty 64 MB `/tmp`, and at most 256 processes.

### Docs and starter files

- `SCORING.md`: Exact scoring rules: input files, stdout format, worker costs, miss penalties, and CPU time (also inside `blast-radius-sample.tar.gz`).
- `blast-radius-sample.tar.gz`: Starter kit: a working selector, 30 sample commits with the tests each one breaks, and the local scorer.

### Scoring Summary

- **Metric:** Simulated CI seconds, lower is better
- **Baseline to beat:** 1614.1 s (Starter: run every test, split across 3 workers)
- **Formula:** busiest worker test seconds + 2 s per worker + 300 s per missed commit + CPU seconds; middle of 3 runs
- **Ties:** Equal scores rank the earlier submission first. In the final, scores at most 1 second behind the best tie and rank earliest first, and the remaining entries group the same way from the next best. First place wins.
- **Scorer version:** `blast-radius-1`

For each commit, you pay the busiest worker's recorded test seconds plus 2 seconds per worker, and 300 seconds if you leave out any failing test; your program's CPU seconds are added across the batch. With your score you are told each run's simulated seconds, CPU seconds, and how many commits missed, never which.

### Rules

- Print one JSON line per commit, with at most 8 workers, no duplicate test in a commit, and only test numbers from `tests.json`.
- A broken rule, crash, timeout, memory limit overrun, or failed build rejects the submission with the reason and never changes your best score.
- You never see what your program printed on practice or final runs. Debug locally on the sample set with `make sample`.
- Your team may submit once an hour to start. We raise the limit if the queue stays short.
- One team a person, and your own team's repository. No sharing code between teams: top entries are compared, and you may be asked to explain yours. A submission with the same repository, commit or archive as another team's is disqualified, the later one.
- Your build may download only from public package registries (PyPI, npm, Docker Hub), GitHub releases at a fixed tag, and sqlglot at commit `eb11aec`. Nothing from an address your team controls, because the final rebuilds every image after the cutoff.
- No answers worked out ahead of time and looked up by patch: no table from a patch, or from a kind of edit, to the tests it breaks. Maps built from the pinned commit (coverage, imports, fixtures) are allowed. Top entries are read.
- Keep your repository public, with every commit you submitted still in it, until results are published. An entry we cannot fetch or restore for the final scores nothing.
- Only the final counts. The practice board carries no prize.
- If we find a mislabeled commit before results are published, we correct it for every team.

### The final

At the cutoff, your chosen commit (your best, unless you pick another) is scored on unseen commits, including kinds of change not in practice. At least the top 5 entries are then scored again on those same commits, 5 runs each instead of 3, one at a time on one idle machine; that middle total replaces their first score.

The cutoff is Sun 10:00 AM CST.
