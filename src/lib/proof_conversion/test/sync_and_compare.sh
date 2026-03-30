#!/usr/bin/env bash
# Sync the o1js submodule with the current Mina branch, rebuild o1js,
# dump gate JSONs from both OCaml and o1js, and compare wrap circuits.
#
# Usage:
#   ./sync_and_compare.sh [--skip-rebuild]
#
# Output goes to /tmp/sync_and_compare.log — check there for details.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
MINA_DIR="$(cd "$SCRIPT_DIR/../../../.." && pwd)"
O1JS_DIR="${MINA_DIR}/../o1js"
SUBMOD_MINA="$O1JS_DIR/src/mina"

OCAML_GATES="/tmp/ocaml_compat_gates"
O1JS_GATES="/tmp/o1js_compat_gates"
LOG="/tmp/sync_and_compare.log"

BRANCH="$(cd "$MINA_DIR" && git rev-parse --abbrev-ref HEAD)"

SKIP_REBUILD=false
if [[ "${1:-}" == "--skip-rebuild" ]]; then
  SKIP_REBUILD=true
fi

echo "=== Mina → o1js sync & gate comparison ===" | tee "$LOG"
echo "  Mina:   $MINA_DIR" | tee -a "$LOG"
echo "  o1js:   $O1JS_DIR" | tee -a "$LOG"
echo "  Branch: $BRANCH" | tee -a "$LOG"
echo "  Log:    $LOG" | tee -a "$LOG"
echo "" | tee -a "$LOG"

# --- Step 1: Sync Mina branch into o1js submodule ---
echo "[1/5] Syncing Mina branch into o1js submodule..." | tee -a "$LOG"
cd "$SUBMOD_MINA"
git fetch local-mina "$BRANCH" --quiet
git reset --no-recurse-submodules --hard "local-mina/$BRANCH" >> "$LOG" 2>&1

cd "$MINA_DIR"
LOCAL_DIFF="$(git diff)"
if [ -n "$LOCAL_DIFF" ]; then
  echo "  Applying uncommitted local diff..." | tee -a "$LOG"
  cd "$SUBMOD_MINA"
  echo "$LOCAL_DIFF" | git apply --allow-empty >> "$LOG" 2>&1 || echo "  (some hunks failed)" | tee -a "$LOG"
fi
echo "  Submodule: $(cd "$SUBMOD_MINA" && git log --oneline -1)" | tee -a "$LOG"

# --- Step 2: Rebuild o1js ---
if [ "$SKIP_REBUILD" = true ]; then
  echo "[2/5] Skipping o1js rebuild (--skip-rebuild)" | tee -a "$LOG"
else
  echo "[2/5] Rebuilding o1js WASM + node..." | tee -a "$LOG"
  cd "$O1JS_DIR"
  npm run build:bindings-node >> "$LOG" 2>&1
  npm run build >> "$LOG" 2>&1
  echo "  done" | tee -a "$LOG"
fi

# --- Step 3: Build OCaml test ---
echo "[3/5] Building OCaml compat test..." | tee -a "$LOG"
cd "$MINA_DIR"
dune build src/lib/proof_conversion/test/test_pickles_compat.exe >> "$LOG" 2>&1
echo "  done" | tee -a "$LOG"

# --- Step 4: Dump gates from both sides ---
echo "[4/5] Dumping gate JSONs..." | tee -a "$LOG"
rm -rf "$OCAML_GATES" "$O1JS_GATES"
mkdir -p "$OCAML_GATES" "$O1JS_GATES"

# OCaml side (simple test only)
cd "$MINA_DIR"
echo "  OCaml..." | tee -a "$LOG"
SKIP_RECURSIVE=1 DUMP_PCS_GATES="$OCAML_GATES" \
  dune exec src/lib/proof_conversion/test/test_pickles_compat.exe >> "$LOG" 2>&1 || true

# o1js side
cd "$O1JS_DIR"
echo "  o1js..." | tee -a "$LOG"
DUMP_PCS_GATES="$O1JS_GATES" node -e "
const { Field, ZkProgram, Provable } = require('./dist/node/index.cjs');
async function main() {
  const Simple = ZkProgram({
    name: 'simple-compat-test',
    publicInput: Provable.Array(Field, 1),
    publicOutput: Provable.Array(Field, 0),
    methods: {
      compute: {
        privateInputs: [],
        async method(pub) {
          const x = Provable.witness(Field, () => Field(0));
          const xSq = x.mul(x);
          pub[0].assertEquals(xSq);
          return [];
        },
      },
    },
  });
  await Simple.compile();
}
main().catch(e => { console.error(e); process.exit(1); });
" >> "$LOG" 2>&1
echo "  done" | tee -a "$LOG"

# --- Step 5: Compare ---
echo "" | tee -a "$LOG"
echo "[5/5] Comparing wrap circuits..." | tee -a "$LOG"

cd "$MINA_DIR"

echo "  OCaml files:" | tee -a "$LOG"
ls -1 "$OCAML_GATES"/*.json 2>/dev/null | tee -a "$LOG"
echo "  o1js files:" | tee -a "$LOG"
ls -1 "$O1JS_GATES"/*.json 2>/dev/null | tee -a "$LOG"
echo "" | tee -a "$LOG"

# Find the wrap circuit files (largest among cs_0_*)
OCAML_WRAP=$(ls -S "$OCAML_GATES"/cs_0_*gates.json 2>/dev/null | head -1)
O1JS_WRAP=$(ls -S "$O1JS_GATES"/cs_0_*gates.json 2>/dev/null | head -1)

if [ -z "$OCAML_WRAP" ] || [ -z "$O1JS_WRAP" ]; then
  echo "ERROR: Could not find wrap circuit dumps" | tee -a "$LOG"
  exit 1
fi

python3 -c "
import json, sys

with open('$O1JS_WRAP') as f:
    o1js = json.load(f)
with open('$OCAML_WRAP') as f:
    ocaml = json.load(f)

og = ocaml['gates']
ng = o1js['gates']
def gt(g): return g.get('typ', g.get('type', '?'))
def decode_coeff0(g):
    coeffs = g.get('coeffs', [])
    if not coeffs: return None
    try: return int.from_bytes(bytes.fromhex(coeffs[0]), 'little')
    except: return None

print(f'o1js wrap:  {len(ng)} gates  ({sys.argv[1]})')
print(f'OCaml wrap: {len(og)} gates  ({sys.argv[2]})')
print()

# Find and show all markers
print('Markers:')
for label, gates in [('o1js ', ng), ('OCaml', og)]:
    for i, g in enumerate(gates):
        if gt(g) == 'Zero':
            coeffs = g.get('coeffs', [])
            if len(coeffs) == 7:
                c0 = decode_coeff0(g)
                if c0 and c0 >= 8000:
                    print(f'  {label} marker {c0} at gate {i}')
print()

# Show all mismatches
mismatches = 0
for i in range(min(len(ng), len(og))):
    a, b = ng[i], og[i]
    type_match = gt(a) == gt(b)
    coeff_match = a.get('coeffs') == b.get('coeffs')
    wire_match = a.get('wires') == b.get('wires')
    if not (type_match and coeff_match and wire_match):
        mismatches += 1
        if mismatches <= 20:
            issues = []
            if not type_match: issues.append(f'type: {gt(a)} vs {gt(b)}')
            if not coeff_match: issues.append('coeffs')
            if not wire_match: issues.append('wires')
            print(f'  gate {i} ({gt(a)}): {\" | \".join(issues)}')
if mismatches > 20:
    print(f'  ... and {mismatches - 20} more')
if mismatches == 0:
    print('EXACT MATCH!')
else:
    print(f'Total: {mismatches} mismatches')
" "$O1JS_WRAP" "$OCAML_WRAP" 2>&1 | tee -a "$LOG"

echo "" | tee -a "$LOG"
echo "Full log: $LOG" | tee -a "$LOG"
echo "Files: $OCAML_GATES/ vs $O1JS_GATES/" | tee -a "$LOG"
