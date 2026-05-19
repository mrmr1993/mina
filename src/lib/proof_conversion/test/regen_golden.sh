#!/usr/bin/env bash
# Regenerate src/lib/proof_conversion/test/golden/step_gate_digests.json from
# the current branch state. Run this once to establish a baseline; afterwards
# `dune build @src/lib/proof_conversion/test/check-proof-conversion` diffs
# against this file.
#
# Usage:
#   ./regen_golden.sh
#
# Wall-clock cost: ~20 minutes for the full 42-circuit sweep on a workstation.

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
trap 'rm -rf "$DUMP_DIR"' EXIT

echo "Running full circuit sweep (this takes ~20 minutes)..." >&2
DUMP_PCS_GATES="$DUMP_DIR" \
  _build/default/src/lib/proof_conversion/test/test_step_gate_golden.exe \
  > "$GOLDEN"

echo "" >&2
echo "Updated $GOLDEN" >&2
echo "Entries:" >&2
wc -l "$GOLDEN" >&2
