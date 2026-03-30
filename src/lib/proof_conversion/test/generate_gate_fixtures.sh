#!/usr/bin/env bash
# Generate reference gate JSON fixtures from nori-proof-conversion.
#
# Usage:
#   ./generate_gate_fixtures.sh [groth16|plonk]
#
# Requires: node (via nvm), nori-proof-conversion checkout at ../nori-proof-conversion
#
# Output: fixtures/gates/{groth16,plonk}/*.json

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
NORI_DIR="${SCRIPT_DIR}/../../../../nori-proof-conversion"
FIXTURE_DIR="${SCRIPT_DIR}/fixtures/gates"

if [ ! -d "$NORI_DIR" ]; then
  echo "Error: nori-proof-conversion not found at $NORI_DIR"
  exit 1
fi

proof_type="${1:-groth16}"

case "$proof_type" in
  groth16)
    dump_script="src/groth/recursion/dump_digests.ts"
    out_dir="${FIXTURE_DIR}/groth16"
    ;;
  plonk)
    dump_script="src/plonk/recursion/dump_digests.ts"
    out_dir="${FIXTURE_DIR}/plonk"
    ;;
  *)
    echo "Usage: $0 [groth16|plonk]"
    exit 1
    ;;
esac

mkdir -p "$out_dir"

echo "Generating ${proof_type} gate fixtures..."
echo "  nori dir: $NORI_DIR"
echo "  output:   $out_dir"

cd "$NORI_DIR"

# Dump all circuit gate JSONs
DUMP_PCS_GATES="$out_dir" npx tsx "$dump_script" 2>&1 | tee "${out_dir}/dump.log"

echo ""
echo "Generated fixtures:"
ls -la "$out_dir"/*.json 2>/dev/null || echo "  (no JSON files found)"
echo ""
echo "Done. Compare against OCaml output using:"
echo "  DUMP_PCS_GATES=/tmp/ocaml_gates dune exec src/lib/proof_conversion/test/test_gate_comparison.exe"
echo "  diff -r $out_dir /tmp/ocaml_gates"
