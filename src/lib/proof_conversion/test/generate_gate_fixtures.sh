#!/usr/bin/env bash
# Dump gate JSONs from nori-proof-conversion for a specific circuit.
#
# Usage:
#   ./generate_gate_fixtures.sh [groth16|plonk] <output_dir>
#
# Example:
#   ./generate_gate_fixtures.sh groth16 /tmp/nori_gates
#
# Then compare with OCaml gates:
#   DUMP_PCS_GATES=/tmp/ocaml_gates dune exec src/app/proof_conversion/main.exe -- \
#     --proof-type groth16 --input .../proof.json --output /tmp/out.json
#   diff <(jq -r '.gates[].typ' /tmp/ocaml_gates/cs_0_*.json) \
#        <(jq -r '.gates[]' /tmp/nori_gates/zkp0.json)
#
# For a single circuit with full detail:
#   DUMP_ZKP=zkp0 ./generate_gate_fixtures.sh groth16 /tmp/nori_gates
#
# Requires: node (via nvm), nori-proof-conversion checkout at ../nori-proof-conversion

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
NORI_DIR="${SCRIPT_DIR}/../../../../nori-proof-conversion"

if [ ! -d "$NORI_DIR" ]; then
  echo "Error: nori-proof-conversion not found at $NORI_DIR"
  exit 1
fi

proof_type="${1:-groth16}"
out_dir="${2:-/tmp/nori_gates}"

case "$proof_type" in
  groth16)
    dump_script="src/groth/recursion/dump_digests.ts"
    ;;
  plonk)
    dump_script="src/plonk/recursion/dump_digests.ts"
    ;;
  *)
    echo "Usage: $0 [groth16|plonk] <output_dir>"
    exit 1
    ;;
esac

mkdir -p "$out_dir"

echo "Dumping ${proof_type} gate sequences from nori..."
echo "  nori dir: $NORI_DIR"
echo "  output:   $out_dir"
echo ""

cd "$NORI_DIR"

# Use DUMP_PCS_GATES to get full gate JSONs (with wires + coefficients)
DUMP_PCS_GATES="$out_dir" \
  GROTH16_VK_PATH=./src/groth/example_jsons/vk.json \
  npx tsx "$dump_script" 2>&1

echo ""
echo "Gate files:"
ls -la "$out_dir"/cs_*.json 2>/dev/null || echo "  (no files found)"
echo ""
echo "Quick diff workflow:"
echo "  # Dump OCaml gates:"
echo "  DUMP_PCS_GATES=/tmp/ocaml_gates dune exec src/app/proof_conversion/main.exe -- \\"
echo "    --proof-type ${proof_type} --input .../proof.json --output /tmp/out.json"
echo ""
echo "  # Compare gate types for circuit N (step circuit = even-numbered cs files):"
echo "  diff <(jq -r '.gates[].typ' /tmp/ocaml_gates/cs_0_*.json) \\"
echo "       <(jq -r '.gates[].typ' ${out_dir}/cs_0_*.json)"
echo ""
echo "  # Or use the gate comparison tool:"
echo "  dune exec src/lib/proof_conversion/test/test_gate_comparison.exe -- \\"
echo "    --reference ${out_dir} --candidate /tmp/ocaml_gates"
