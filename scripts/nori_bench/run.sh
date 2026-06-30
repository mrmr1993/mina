#!/bin/bash
# Run a nori proof conversion fully specified by a resource-aware scheduler
# config. The config is the complete spec: workers (derived from each base job's
# "worker"), per-job cores/cost/priority, and the budget. Every test is just:
#
#   scripts/nori_bench/run.sh PATH/TO/config.json
#
# Prints the makespan/vk line and a Gantt of the run.
set -euo pipefail

CONFIG="${1:?usage: run.sh CONFIG.json}"
REPO="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$REPO"
CONFIG="$(realpath "$CONFIG")"
NAME="$(basename "$CONFIG" .json)"
LOG="/tmp/nori_run_${NAME}.dag.log"
LIVE=/tmp/nori_run.log

# Mirror all output to a fixed live file so a single `tail -F /tmp/nori_run.log`
# in another shell follows every run, regardless of the per-config name.
exec > >(tee "$LIVE") 2>&1
echo "=== run $NAME @ $(date +%H:%M:%S) ==="

eval "$(opam env)" 2>/dev/null || true
ulimit -s 65532 2>/dev/null || true
ulimit -n 10240 2>/dev/null || true
export SCHEDULER_CONFIG="$CONFIG"
export MALLOC_ARENA_MAX=2

# Derive one --pool per worker (its base-circuit shard + all compression layers)
# from the config's per-base-job "worker" assignments. The pool rayon (:2:) is
# the worker's global pool; per-job rayon comes from the config via --rayon.
mapfile -t POOLS < <(python3 - "$CONFIG" <<'PY'
import json, sys
cfg = json.load(open(sys.argv[1]))
workers = {}
for k, v in cfg["jobs"].items():
    if k.isdigit() and isinstance(v, dict) and "worker" in v:
        workers.setdefault(v["worker"], []).append(int(k))
for wid in sorted(workers):
    circs = ",".join(str(c) for c in sorted(workers[wid]))
    print(f"{circs},compress:2:1")
PY
)
SLOTS=${#POOLS[@]}
if [ "$SLOTS" -eq 0 ]; then
  echo "no workers derived from $CONFIG (base jobs need a \"worker\" field)" >&2
  exit 1
fi

pkill -9 nori_proof_conv 2>/dev/null || true
rm -f /tmp/nori-socket/worker.*.sock* /tmp/nori-socket/prove_slot.* 2>/dev/null || true
rm -rf /tmp/nori-socket/wrap_waiting 2>/dev/null || true
sleep 5

P=()
for pool in "${POOLS[@]}"; do P+=(--pool "$pool"); done

echo "## $NAME : $SLOTS workers, budget $(python3 -c "import json,sys;print(json.load(open('$CONFIG'))['budget'])")"
timeout 1800 scripts/nori_bench/bench.sh --name "$NAME" --slots "$SLOTS" \
  --env "SCHEDULER_CONFIG=$CONFIG MALLOC_ARENA_MAX=2" \
  --warmup 0 --hot 1 --no-record "${P[@]}" 2>&1 | grep -E "makespan=" || true
cp /tmp/nori_bench_out.log "$LOG" 2>/dev/null || true

echo "## Gantt ($LOG):"
python3 scripts/nori_bench/gantt.py "$LOG" --config "$CONFIG" --width 100 || true
