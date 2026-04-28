#!/usr/bin/env bash
# Extract top-N slowest F* per-function totals + per-query maxima from a
# build log produced with --query_stats.  Designed for the
# `verification_result.txt` style output that `./hax.sh prove` produces.
#
# Usage:
#   ./extract-fstar-perf.sh [N] [LOG]
#     N    — how many top entries to print (default 20)
#     LOG  — path to build log (default: ../verification_result.txt)
#
# Output: two markdown sections to stdout.  Pipe into a snapshot file.
set -euo pipefail

N="${1:-20}"
LOG="${2:-${PWD%/*}/../verification_result.txt}"

if [ ! -f "$LOG" ]; then
  echo "error: log not found: $LOG" >&2
  exit 1
fi

# Parse Query-stats lines.  Format example:
#   (Module.Path.fst(LINE,COL-LINE,COL))\tQuery-stats (Module.Path.fn_name, N)\t<succeeded|failed> [(with hint)] in TIME milliseconds with fuel F and ifuel I and rlimit R (used rlimit U)
#
# Aggregate per (module, fn_name): total_ms, max_query_ms, count, fail_flag,
# saturation_flag (used > 0.8 * rlimit on at least one query).
python3 - "$LOG" "$N" <<'PY'
import sys, re, collections

log_path = sys.argv[1]
top_n    = int(sys.argv[2])

# Match: (Module.fst(...))<TAB>Query-stats (Module.fn, N)<TAB>(succeeded|failed) [(with hint)] in MS milliseconds ... rlimit RL (used rlimit USED)
qs_re = re.compile(
    r"\(([A-Za-z0-9_.]+\.fsti?)\([^)]*\)\)\s+"
    r"Query-stats \(([A-Za-z0-9_.]+),\s+(\d+)\)\s+"
    r"(succeeded|failed)[^i]*in\s+(\d+)\s+milliseconds[^r]*"
    r"rlimit\s+(\d+)\s+\(used rlimit\s+([0-9.]+)\)"
)

per_fn = collections.defaultdict(lambda: {
    "total_ms": 0, "max_ms": 0, "count": 0,
    "failed": False, "saturated": False, "module": "",
})

with open(log_path, errors="replace") as f:
    for line in f:
        m = qs_re.search(line)
        if not m:
            continue
        mod, fn, qid, status, ms, rlimit, used = m.groups()
        ms = int(ms); rlimit = int(rlimit); used = float(used)
        key = (mod, fn)
        d = per_fn[key]
        d["module"] = mod
        d["total_ms"] += ms
        if ms > d["max_ms"]: d["max_ms"] = ms
        d["count"] += 1
        if status == "failed": d["failed"] = True
        if rlimit > 0 and used > 0.8 * rlimit: d["saturated"] = True

ranked = sorted(per_fn.items(), key=lambda kv: -kv[1]["total_ms"])

# Module totals: sum of all per-fn totals scoped to one module.
mod_totals = collections.defaultdict(int)
for (mod, fn), d in per_fn.items():
    mod_totals[mod] += d["total_ms"]
mod_ranked = sorted(mod_totals.items(), key=lambda kv: -kv[1])

print(f"## Top-{top_n} per-function totals\n")
print(f"| # | Function | Module | total (s) | max query (ms) | queries | flags |")
print(f"|---|---|---|---:|---:|---:|---|")
for i, ((mod, fn), d) in enumerate(ranked[:top_n], 1):
    flags = []
    if d["failed"]: flags.append("FAILED")
    if d["saturated"]: flags.append("rlimit-sat")
    flag_str = ", ".join(flags) if flags else "—"
    short_mod = mod.replace("Libcrux_ml_dsa.", "L_md.").replace("Hacspec_ml_dsa.", "H_md.").replace(".fst", "")
    short_fn = fn.replace(mod.replace(".fst", "") + ".", "")
    print(f"| {i} | `{short_fn}` | `{short_mod}` | {d['total_ms']/1000:.2f} | {d['max_ms']} | {d['count']} | {flag_str} |")

print(f"\n## Top-{top_n} module totals (sum of all queries)\n")
print(f"| # | Module | total (s) | functions tracked |")
print(f"|---|---|---:|---:|")
for i, (mod, total) in enumerate(mod_ranked[:top_n], 1):
    fns = sum(1 for (m, _), _ in per_fn.items() if m == mod)
    short_mod = mod.replace("Libcrux_ml_dsa.", "L_md.").replace("Hacspec_ml_dsa.", "H_md.").replace(".fst", "")
    print(f"| {i} | `{short_mod}` | {total/1000:.2f} | {fns} |")

# Total queries seen
total_queries = sum(d["count"] for d in per_fn.values())
total_ms = sum(d["total_ms"] for d in per_fn.values())
print(f"\n_Sample size: {total_queries} Query-stats lines, {total_ms/1000:.0f}s total Z3 time, across {len(per_fn)} functions in {len(mod_totals)} modules._")
PY
