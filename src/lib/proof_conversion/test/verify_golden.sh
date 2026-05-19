#!/usr/bin/env bash
# Canonical regression gate for proof_conversion refactors.
#
# Compiles every circuit (24 PLONK + 2 compressor + 16 Groth16) under the
# production [~name:] strings, captures each step-circuit's gate JSON dump,
# sha256s it (along with the Pickles name), and diffs the resulting sorted
# map against [test/golden/step_gate_digests.json].
#
# Returns 0 if the golden is unchanged, non-zero otherwise. Run this from
# any directory; the script chdir's to the workspace root.
#
# Wall-clock cost: ~20 minutes for the full sweep on a workstation.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
MINA_DIR="$(cd "$SCRIPT_DIR/../../../.." && pwd)"
GOLDEN="$SCRIPT_DIR/golden/step_gate_digests.json"

cd "$MINA_DIR"
eval "$(opam env)"
ulimit -s 65532 || true
ulimit -n 10240 || true

echo "Building test_step_gate_golden.exe..." >&2
dune build src/lib/proof_conversion/test/test_step_gate_golden.exe

DUMP_DIR="$(mktemp -d -t gate_dump.XXXXXX)"
ACTUAL="$(mktemp -t step_gate_actual.XXXXXX.json)"
trap 'rm -rf "$DUMP_DIR" "$ACTUAL"' EXIT

echo "Running full circuit sweep (this takes ~20 minutes)..." >&2
DUMP_PCS_GATES="$DUMP_DIR" \
  _build/default/src/lib/proof_conversion/test/test_step_gate_golden.exe \
  > "$ACTUAL"

echo "" >&2
echo "Diffing against $GOLDEN ..." >&2
if diff -u "$GOLDEN" "$ACTUAL"; then
  echo "" >&2
  echo "OK: step-circuit gate digests match golden." >&2
  exit 0
else
  echo "" >&2
  echo "FAIL: step-circuit gate digests differ from golden." >&2
  echo "If the change is intentional, run regen_golden.sh to update." >&2
  exit 1
fi
