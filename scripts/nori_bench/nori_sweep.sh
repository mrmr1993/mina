#!/usr/bin/env bash
# Parameter sweep over the nori benchmark harness.
#
# Reproduces the manual search recorded in nori-run-stats.txt: for each
# (count, threads, circuits) configuration it restarts the worker pool from
# cold, runs the benchmark, and records the steady-state timing. The proving
# keys are reloaded per config (that's the cost being traded against
# parallelism), but kept hot across the timed runs within a config.
#
# Edit the CONFIGS array below to taste. Each entry is:
#   "<count> <threads> <circuits-spec>"
#
# Usage:
#   scripts/nori_bench/nori_sweep.sh <proof.json> [more_proofs...]
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BENCH="$HERE/nori_bench.sh"

# (count, threads, circuits) — sampled from the configs in nori-run-stats.txt.
CONFIGS=(
  "3 7 all"
  "4 6 8-24,layer1,node"
  "5 6 10-24,layer1,node"
  "6 4 12-24,layer1,node"
  "7 4 19-23,layer1,node"
)

PROOFS=("$@")
if [ "${#PROOFS[@]}" -eq 0 ]; then
  echo "usage: $0 <proof.json> [more_proofs...]" >&2
  exit 2
fi

OUT=/tmp/nori_sweep_results.txt
: >"$OUT"
echo "config sweep over ${#CONFIGS[@]} configs, $(date)" | tee -a "$OUT"

for cfg in "${CONFIGS[@]}"; do
  read -r count threads circuits <<<"$cfg"
  echo "" | tee -a "$OUT"
  echo "#### count=$count threads=$threads circuits=$circuits ####" | tee -a "$OUT"

  # --skip-verify mirrors the later (faster) runs in the stats file; drop it to
  # measure with verification on.
  "$BENCH" \
    --count "$count" --threads "$threads" --circuits "$circuits" \
    --runs 3 --warmup 1 --skip-verify \
    "${PROOFS[@]}" | tee -a "$OUT"
done

echo "" | tee -a "$OUT"
echo "Sweep complete. Results in $OUT" | tee -a "$OUT"
