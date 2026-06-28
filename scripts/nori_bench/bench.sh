#!/usr/bin/env bash
# Single consolidated benchmark runner for the nori proof-conversion pipeline.
#
# This REPLACES the ad-hoc /tmp/nori_*.sh scripts. Every invocation:
#   * spins up the requested worker pools (keys stay hot),
#   * runs warmup + N timed "hot" conversions,
#   * captures makespan, cores-busy, peak RAM, min MemAvailable, vk match, OOM,
#   * tags the run with the main + proof-systems-submodule commit SHAs and a
#     dirty flag,
#   * appends one JSON record to scripts/nori_bench/results.jsonl,
#   * regenerates scripts/nori_bench/RESULTS.md (sorted by makespan).
#
# The point: ONE place for the runner, ONE accumulating record, so we stop
# relitigating stale numbers measured on forgotten binaries/configs.
#
# Usage:
#   scripts/nori_bench/bench.sh --name LABEL [--pool SPEC]... [options]
#
# Pool SPEC: CIRCUITS:RAYON:COUNT  (worker --start-index auto-assigned in order)
#   e.g.  0-7,layer1,node,tip:5:4   -> 4 workers, RAYON=5, those circuits
# With no --pool given, defaults to the baseline: 4-4-4, R5, node+tip coverage.
#
# Options (defaults in parens):
#   --name LABEL     required short config name
#   --pool SPEC      repeatable pool spec (see above)
#   --slots K        PICKLES_PROVE_SLOTS admission gate, 0=off            (8)
#   --hot N          timed hot conversions after warmup                  (2)
#   --warmup N       untimed warmup conversions                          (1)
#   --env "K=V ..."  extra env exported to workers + driver              ()
#   --note "..."     freeform note stored with the row                   ()
#   --proof PATH     input proof.json                  (/tmp/nori-proofs/proof.json)
#   --no-record      run + print, but do not append to results.jsonl     (off)
set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
cd "$REPO"
eval "$(opam env)" 2>/dev/null || true

EXE=_build/default/src/app/proof_conversion/nori_proof_converter.exe
SOCK=/tmp/nori-socket; CACHE=/tmp/nori-cache-dir
PROOF=/tmp/nori-proofs/proof.json
REF=../nori-proof-conversion/example-proofs/v5.sp1ToPlonk.json
NCPU=$(nproc)

NAME=""; SLOTS=8; HOT=2; WARMUP=1; EXTRA_ENV=""; NOTE=""; RECORD=1
POOLS=()
while [ $# -gt 0 ]; do
  case "$1" in
    --name)      NAME="$2"; shift 2 ;;
    --pool)      POOLS+=("$2"); shift 2 ;;
    --slots)     SLOTS="$2"; shift 2 ;;
    --hot)       HOT="$2"; shift 2 ;;
    --warmup)    WARMUP="$2"; shift 2 ;;
    --env)       EXTRA_ENV="$2"; shift 2 ;;
    --note)      NOTE="$2"; shift 2 ;;
    --proof)     PROOF="$2"; shift 2 ;;
    --no-record) RECORD=0; shift ;;
    -h|--help)   sed -n '2,40p' "$0"; exit 0 ;;
    *) echo "unknown option: $1" >&2; exit 2 ;;
  esac
done
[ -n "$NAME" ] || { echo "error: --name required" >&2; exit 2; }
[ -x "$EXE" ] || { echo "error: build $EXE first" >&2; exit 2; }
if [ "${#POOLS[@]}" -eq 0 ]; then
  POOLS=("0-7,layer1,node,tip:5:4" "8-15,layer1,node,tip:5:4" "16-23,layer1,node,tip:5:4")
fi

ulimit -s 65532 2>/dev/null || true; ulimit -n 10240 2>/dev/null || true
export MINA_USE_MMAP_CACHE=1 OCAMLRUNPARAM='O=20' KIMCHI_FUSED_EVAL=1
export PICKLES_PROVE_SLOTS="$SLOTS"
# shellcheck disable=SC2086
[ -n "$EXTRA_ENV" ] && export $EXTRA_ENV

RAMF=$(mktemp); echo 0 >"$RAMF"; OOMF=$(mktemp); rm -f "$OOMF"
rm -f "$SOCK"/worker.*.sock* "$SOCK"/prove_slot.* 2>/dev/null || true
rm -rf "$SOCK"/wrap_waiting 2>/dev/null || true
mkdir -p "$SOCK" "$CACHE"

PIDS=(); SAMP=""; WD=""
cleanup(){
  "$EXE" stop-workers --socket-dir "$SOCK" >/dev/null 2>&1 || true
  [ -n "$SAMP" ] && kill "$SAMP" 2>/dev/null || true
  [ -n "$WD" ] && kill "$WD" 2>/dev/null || true
  for p in "${PIDS[@]:-}"; do kill "$p" 2>/dev/null || true; done
  pkill -9 -f nori_proof_converter.exe 2>/dev/null || true
}
trap cleanup EXIT

echo "==> [$NAME] starting pools: ${POOLS[*]}  (slots=$SLOTS env='$EXTRA_ENV')"
IDX=0; TOTAL=0
for spec in "${POOLS[@]}"; do
  CIRC="${spec%%:*}"; rest="${spec#*:}"; RAYON="${rest%%:*}"; CNT="${rest##*:}"
  RAYON_NUM_THREADS="$RAYON" "$EXE" start-workers --system plonk --count "$CNT" \
    --socket-dir "$SOCK" --cache-dir "$CACHE" --circuits "$CIRC" \
    --skip-verify --start-index "$IDX" >/tmp/nori_bench_pool_$IDX.log 2>&1 &
  PIDS+=($!); IDX=$((IDX+CNT)); TOTAL=$((TOTAL+CNT))
done

while [ "$(ls "$SOCK"/worker.*.sock.ready 2>/dev/null | wc -l)" -lt "$TOTAL" ]; do
  al=0; for p in "${PIDS[@]}"; do kill -0 "$p" 2>/dev/null && al=1; done
  [ "$al" -eq 0 ] && { echo "ABORT: a pool died before becoming ready"; exit 1; }
  m=$(awk '/MemAvailable/{print int($2/1024)}' /proc/meminfo)
  [ "$m" -lt 900 ] && { echo "ABORT: low mem during startup (${m}MB)"; exit 1; }
  sleep 3
done
echo "==> [$NAME] $TOTAL workers ready"

# peak-RAM sampler (sum of worker RssAnon) + OOM watchdog
( max=0; while :; do
    s=$(for p in $(pgrep -f nori_proof_converter.exe 2>/dev/null); do
          awk '/^RssAnon/{print $2}' /proc/$p/status 2>/dev/null; done | awk '{t+=$1}END{print t+0}')
    [ "${s:-0}" -gt "$max" ] && { max=$s; echo "$max" >"$RAMF"; }; sleep 0.5
  done ) & SAMP=$!
( while :; do m=$(awk '/MemAvailable/{print int($2/1024)}' /proc/meminfo)
    [ "$m" -lt 700 ] && { echo "$m" >"$OOMF"; pkill -9 -f nori_proof_converter.exe 2>/dev/null; break; }
    sleep 0.5; done ) & WD=$!

read_stat(){ awk '/^cpu /{idle=$5+$6;tot=0;for(i=2;i<=NF;i++)tot+=$i;print idle,tot}' /proc/stat; }
MIN_AVAIL=999999
hot(){
  local t0=$SECONDS i0 a0 i1 a1
  read i0 a0 < <(read_stat)
  "$EXE" sp1ToPlonkDaemonised "$PROOF" --workers "$SOCK" >/tmp/nori_bench_out.log 2>&1
  local rc=$?
  read i1 a1 < <(read_stat)
  local m; m=$(awk '/MemAvailable/{print int($2/1024)}' /proc/meminfo); [ "$m" -lt "$MIN_AVAIL" ] && MIN_AVAIL=$m
  local b; b=$(awk -v i0=$i0 -v i1=$i1 -v a0=$a0 -v a1=$a1 -v n=$NCPU 'BEGIN{printf "%.1f",n*(1-(i1-i0)/(a1-a0))}')
  echo "$((SECONDS-t0)) $rc $b"
}

echo "==> [$NAME] warmup x$WARMUP"
for ((w=0; w<WARMUP; w++)); do "$EXE" sp1ToPlonkDaemonised "$PROOF" --workers "$SOCK" >/dev/null 2>&1 || true; done
[ -f "$OOMF" ] && { echo "==> [$NAME] OOM during warmup"; }

TIMES=(); CORES=(); RCS=()
if [ ! -f "$OOMF" ]; then
  echo "==> [$NAME] hot x$HOT"
  for ((r=0; r<HOT; r++)); do
    [ -f "$OOMF" ] && break
    read t rc b < <(hot); echo "    hot $((r+1)): ${t}s rc=$rc cores=$b"
    TIMES+=("$t"); CORES+=("$b"); RCS+=("$rc")
  done
fi
kill "$SAMP" "$WD" 2>/dev/null || true; SAMP=""; WD=""

VK=$(python3 -c "import json;a=json.load(open('${PROOF%.json}.sp1ToPlonk.json'));b=json.load(open('$REF'));print(str(a.get('vkData',{}).get('hash')==b.get('vkData',{}).get('hash')).lower())" 2>/dev/null || echo "unknown")
PEAK=$(awk -v k="$(cat "$RAMF")" 'BEGIN{printf "%.2f", k/1048576}')
OOM=false; [ -f "$OOMF" ] && OOM=true
CMAIN=$(git rev-parse --short HEAD 2>/dev/null)
CSUB=$(cd src/lib/crypto/proof-systems && git rev-parse --short HEAD 2>/dev/null)
DIRTY=""; git diff --quiet 2>/dev/null || DIRTY="main"; (cd src/lib/crypto/proof-systems && git diff --quiet 2>/dev/null) || DIRTY="${DIRTY:+$DIRTY+}sub"
DATE=$(date -u +%Y-%m-%dT%H:%M)

echo "==> [$NAME] makespan=${TIMES[*]:-OOM}  cores=${CORES[*]:-}  peak=${PEAK}GB  minAvail=${MIN_AVAIL}MB  vk=$VK  oom=$OOM  ($CMAIN/$CSUB${DIRTY:+ dirty:$DIRTY})"

if [ "$RECORD" -eq 1 ]; then
  POOLS_JSON=$(printf '%s\n' "${POOLS[@]}" | python3 -c "import sys,json;print(json.dumps([l.strip() for l in sys.stdin if l.strip()]))")
  TIMES_JSON=$(printf '%s\n' "${TIMES[@]:-}" | python3 -c "import sys,json;print(json.dumps([int(l) for l in sys.stdin if l.strip()]))")
  CORES_JSON=$(printf '%s\n' "${CORES[@]:-}" | python3 -c "import sys,json;print(json.dumps([float(l) for l in sys.stdin if l.strip()]))")
  python3 - "$HERE" <<PY
import json,sys,os
here=sys.argv[1]
rec={"name":"$NAME","pools":$POOLS_JSON,"slots":int("$SLOTS"),"env":"$EXTRA_ENV",
     "makespan_s":$TIMES_JSON,"cores":$CORES_JSON,"peak_ram_gb":float("$PEAK"),
     "min_memavail_mb":int("$MIN_AVAIL") if "$MIN_AVAIL".isdigit() else None,
     "vk_match":"$VK","oom":$OOM,"rcs":[int(x) for x in "${RCS[*]:-}".split()],
     "commit_main":"$CMAIN","commit_sub":"$CSUB","dirty":"$DIRTY","date":"$DATE","note":"$NOTE"}
with open(os.path.join(here,"results.jsonl"),"a") as f: f.write(json.dumps(rec)+"\n")
PY
  python3 "$HERE/gen_results.py" "$HERE"
  echo "==> recorded to results.jsonl + regenerated RESULTS.md"
fi
