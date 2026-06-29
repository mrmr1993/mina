#!/usr/bin/env bash
# Benchmark harness for the nori proof-conversion pipeline.
#
# Reconstructs the local (non-Docker) test cycle used on
# feature/nori-proof-conversion-3: spin up N persistent worker daemons so the
# proving keys stay hot, then push several proofs through
# `sp1ToPlonkDaemonised` and time the steady state (discarding the first,
# cold-cache run).
#
# It drives the `nori_proof_converter.exe` subcommands directly:
#   start-workers --system <sys> --count <n> --socket-dir <dir> [--circuits ...]
#   sp1ToPlonkDaemonised <proof.json> --workers <socket-dir>
#   stop-workers --socket-dir <dir>
#
# Usage:
#   scripts/nori_bench/nori_bench.sh [options] <proof.json> [more_proofs.json...]
#
# Options (with defaults):
#   --count N            worker daemons to start            (3)
#   --threads N          RAYON_NUM_THREADS per worker       (7)
#   --circuits SPEC      circuit subset, e.g. 19-23,layer1,node, or `all`  (all)
#   --system SYS         plonk | groth16                    (plonk)
#   --socket-dir DIR     worker socket directory            (/tmp/nori-socket)
#   --cache-dir DIR      proving-key cache directory        (/tmp/nori-cache-dir)
#   --runs N             timed runs per proof after warmup  (3)
#   --warmup N           untimed warmup runs per proof      (1)
#   --skip-verify        pass --skip-verify to start-workers (off)
#   --exe PATH           path to nori_proof_converter.exe   (dune exec ...)
#   --keep-workers       leave workers running on exit (don't stop-workers)
#   --reuse-workers      assume workers already running; don't start/stop them
#
# Notes:
#   * The exe only exists on the proof-conversion branch. Build it first with:
#       dune build src/app/proof_conversion/nori_proof_converter.exe
#   * MINA_USE_MMAP_CACHE=1 is exported (matches the recorded runs); it lets the
#     cached keys be mmap'd rather than re-read, cutting startup RAM/time.
set -euo pipefail

# ---- defaults -------------------------------------------------------------
COUNT=3
THREADS=7
CIRCUITS=all
SYSTEM=plonk
SOCKET_DIR=/tmp/nori-socket
CACHE_DIR=/tmp/nori-cache-dir
RUNS=3
WARMUP=1
SKIP_VERIFY=0
EXE=""
KEEP_WORKERS=0
REUSE_WORKERS=0

PROOFS=()

while [ $# -gt 0 ]; do
  case "$1" in
    --count)        COUNT="$2"; shift 2 ;;
    --threads)      THREADS="$2"; shift 2 ;;
    --circuits)     CIRCUITS="$2"; shift 2 ;;
    --system)       SYSTEM="$2"; shift 2 ;;
    --socket-dir)   SOCKET_DIR="$2"; shift 2 ;;
    --cache-dir)    CACHE_DIR="$2"; shift 2 ;;
    --runs)         RUNS="$2"; shift 2 ;;
    --warmup)       WARMUP="$2"; shift 2 ;;
    --skip-verify)  SKIP_VERIFY=1; shift ;;
    --exe)          EXE="$2"; shift 2 ;;
    --keep-workers) KEEP_WORKERS=1; shift ;;
    --reuse-workers) REUSE_WORKERS=1; shift ;;
    -h|--help)      sed -n '2,40p' "$0"; exit 0 ;;
    --) shift; while [ $# -gt 0 ]; do PROOFS+=("$1"); shift; done ;;
    -*) echo "Unknown option: $1" >&2; exit 2 ;;
    *)  PROOFS+=("$1"); shift ;;
  esac
done

if [ "${#PROOFS[@]}" -eq 0 ]; then
  echo "error: no input proofs given" >&2
  exit 2
fi

export MINA_USE_MMAP_CACHE=1
export RAYON_NUM_THREADS="$THREADS"

# How to invoke the converter. Default to `dune exec` so it works from a fresh
# checkout; override with --exe to time a prebuilt binary without dune overhead.
run_converter() {
  if [ -n "$EXE" ]; then
    "$EXE" "$@"
  else
    dune exec src/app/proof_conversion/nori_proof_converter.exe -- "$@"
  fi
}

mkdir -p "$SOCKET_DIR" "$CACHE_DIR"

WORKERS_PID=""
stop_workers() {
  if [ "$REUSE_WORKERS" -eq 1 ] || [ "$KEEP_WORKERS" -eq 1 ]; then
    return
  fi
  echo "==> stopping workers" >&2
  run_converter stop-workers --socket-dir "$SOCKET_DIR" || true
  if [ -n "$WORKERS_PID" ]; then
    kill "$WORKERS_PID" 2>/dev/null || true
    wait "$WORKERS_PID" 2>/dev/null || true
  fi
}
trap stop_workers EXIT

# ---- start workers --------------------------------------------------------
if [ "$REUSE_WORKERS" -eq 0 ]; then
  # Clear stale readiness markers so the wait loop below is meaningful.
  rm -f "$SOCKET_DIR"/worker.*.sock.ready 2>/dev/null || true

  sv_flag=()
  [ "$SKIP_VERIFY" -eq 1 ] && sv_flag=(--skip-verify)

  echo "==> starting $COUNT workers (threads=$THREADS circuits=$CIRCUITS system=$SYSTEM)" >&2
  # Foreground start-workers, backgrounded as a shell job so it keeps holding
  # the daemons; we poll the .ready markers to know when keys are hot.
  run_converter start-workers \
    --system "$SYSTEM" --count "$COUNT" \
    --socket-dir "$SOCKET_DIR" --cache-dir "$CACHE_DIR" \
    --circuits "$CIRCUITS" "${sv_flag[@]}" &
  WORKERS_PID=$!

  echo "==> waiting for $COUNT workers to compile/load circuits..." >&2
  while :; do
    ready=$(ls "$SOCKET_DIR"/worker.*.sock.ready 2>/dev/null | wc -l)
    [ "$ready" -ge "$COUNT" ] && break
    if ! kill -0 "$WORKERS_PID" 2>/dev/null; then
      echo "error: start-workers exited before all workers became ready" >&2
      exit 1
    fi
    sleep 1
  done
  echo "==> all workers ready" >&2
fi

# ---- benchmark ------------------------------------------------------------
# Times one conversion in seconds (wall clock) using the shell's SECONDS.
time_one() {
  local proof="$1"
  local start=$SECONDS
  run_converter sp1ToPlonkDaemonised "$proof" --workers "$SOCKET_DIR" \
    >/dev/null 2>>/tmp/nori_bench_convert.log
  echo $(( SECONDS - start ))
}

printf '\n%-40s %8s %8s %8s\n' "proof" "min(s)" "med(s)" "max(s)"
printf '%s\n' "-------------------------------------------------------------------------"

for proof in "${PROOFS[@]}"; do
  # Warmup runs (untimed): make sure the workers' keys + this proof's shape are
  # fully resident before we start measuring.
  for ((w = 0; w < WARMUP; w++)); do
    echo "   warmup $((w + 1))/$WARMUP: $(basename "$proof")" >&2
    run_converter sp1ToPlonkDaemonised "$proof" --workers "$SOCKET_DIR" \
      >/dev/null 2>>/tmp/nori_bench_convert.log
  done

  times=()
  for ((r = 0; r < RUNS; r++)); do
    t=$(time_one "$proof")
    echo "   run $((r + 1))/$RUNS: ${t}s" >&2
    times+=("$t")
  done

  # min / median / max
  sorted=$(printf '%s\n' "${times[@]}" | sort -n)
  mn=$(echo "$sorted" | head -1)
  mx=$(echo "$sorted" | tail -1)
  cnt=${#times[@]}
  med=$(echo "$sorted" | sed -n "$(((cnt + 1) / 2))p")
  printf '%-40s %8s %8s %8s\n' "$(basename "$proof")" "$mn" "$med" "$mx"
done

echo "" >&2
echo "Conversion stderr logged to /tmp/nori_bench_convert.log" >&2
echo "Outputs written next to each proof as <name>.sp1ToPlonk.json" >&2
