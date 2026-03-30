#!/usr/bin/env bash
# Sync the o1js submodule with the current Mina branch, rebuild o1js,
# dump gate JSONs from both OCaml and o1js, and compare wrap circuits.
#
# Usage:
#   ./sync_and_compare.sh [--skip-rebuild]
#
# How it works:
#   1. In the o1js submodule (o1js/src/mina), fetches from `local-mina` remote
#      (which points at this Mina repo) and resets to the current branch HEAD.
#   2. Applies any uncommitted local diff on top (so marker injection etc. works).
#   3. Rebuilds o1js node bindings.
#   4. Dumps gates from both OCaml and o1js.
#   5. Compares the wrap circuits.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
MINA_DIR="$(cd "$SCRIPT_DIR/../../../.." && pwd)"
O1JS_DIR="${MINA_DIR}/../o1js"
SUBMOD_MINA="$O1JS_DIR/src/mina"

OCAML_GATES="/tmp/ocaml_compat_gates"
O1JS_GATES="/tmp/o1js_compat_gates"

BRANCH="$(cd "$MINA_DIR" && git rev-parse --abbrev-ref HEAD)"

SKIP_REBUILD=false
if [[ "${1:-}" == "--skip-rebuild" ]]; then
  SKIP_REBUILD=true
fi

echo "=== Mina → o1js sync & gate comparison ==="
echo "  Mina:   $MINA_DIR"
echo "  o1js:   $O1JS_DIR"
echo "  Branch: $BRANCH"
echo ""

# --- Step 1: Sync Mina branch into o1js submodule ---
echo "[1/5] Syncing Mina branch into o1js submodule..."
cd "$SUBMOD_MINA"

# Fetch the latest from local-mina
git fetch local-mina "$BRANCH" --quiet

# Reset to the branch HEAD (without touching submodules of the submodule)
git reset --no-recurse-submodules --hard "local-mina/$BRANCH"

# If there's a local diff in the Mina repo (uncommitted changes), apply it
cd "$MINA_DIR"
LOCAL_DIFF="$(git diff)"
if [ -n "$LOCAL_DIFF" ]; then
  echo "  Applying uncommitted local diff..."
  cd "$SUBMOD_MINA"
  echo "$LOCAL_DIFF" | git apply --allow-empty || echo "  (some hunks failed, continuing)"
fi

echo "  Submodule now at: $(cd "$SUBMOD_MINA" && git log --oneline -1)"

# --- Step 2: Rebuild o1js bindings ---
if [ "$SKIP_REBUILD" = true ]; then
  echo "[2/5] Skipping o1js rebuild (--skip-rebuild)"
else
  echo "[2/5] Rebuilding o1js (WASM + node bindings)..."
  cd "$O1JS_DIR"
  # Rebuild OCaml→WASM, then TS
  npm run build:wasm:node 2>&1 | tail -5
  npm run build:dev 2>&1 | tail -3
  echo "  done"
fi

# --- Step 3: Build OCaml test ---
echo "[3/5] Building OCaml compat test..."
cd "$MINA_DIR"
dune build src/lib/proof_conversion/test/test_pickles_compat.exe 2>&1 | tail -3
echo "  done"

# --- Step 4: Dump gates from both sides ---
echo "[4/5] Dumping gate JSONs..."
rm -rf "$OCAML_GATES" "$O1JS_GATES"
mkdir -p "$OCAML_GATES" "$O1JS_GATES"

# OCaml side
cd "$MINA_DIR"
DUMP_PCS_GATES="$OCAML_GATES" dune exec src/lib/proof_conversion/test/test_pickles_compat.exe 2>&1 | grep "PCS" | head -6

# o1js side
cd "$O1JS_DIR"
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
" 2>&1 | grep "PCS" | head -6

echo "  done"

# --- Step 5: Compare ---
echo ""
echo "[5/5] Comparing wrap circuits..."
echo ""

cd "$MINA_DIR"

# Find the wrap circuit files (largest gate count among cs_0_* files)
OCAML_WRAP=$(ls -S "$OCAML_GATES"/cs_0_*gates.json 2>/dev/null | head -1)
O1JS_WRAP=$(ls -S "$O1JS_GATES"/cs_0_*gates.json 2>/dev/null | head -1)

if [ -z "$OCAML_WRAP" ] || [ -z "$O1JS_WRAP" ]; then
  echo "ERROR: Could not find wrap circuit dumps"
  ls "$OCAML_GATES"/*.json "$O1JS_GATES"/*.json 2>/dev/null
  exit 1
fi

echo "  OCaml wrap: $OCAML_WRAP"
echo "  o1js wrap:  $O1JS_WRAP"
echo ""

python3 -c "
import json
with open('$O1JS_WRAP') as f:
    o1js = json.load(f)
with open('$OCAML_WRAP') as f:
    ocaml = json.load(f)

og = ocaml['gates']
ng = o1js['gates']
def gt(g): return g.get('typ', g.get('type', '?'))

print(f'o1js:  {len(ng)} gates')
print(f'OCaml: {len(og)} gates')

mismatches = 0
for i in range(min(len(ng), len(og))):
    a, b = ng[i], og[i]
    type_match = gt(a) == gt(b)
    coeff_match = a.get('coeffs') == b.get('coeffs')
    wire_match = a.get('wires') == b.get('wires')
    if not (type_match and coeff_match and wire_match):
        mismatches += 1
        if mismatches <= 15:
            issues = []
            if not type_match: issues.append(f'type: {gt(a)} vs {gt(b)}')
            if not coeff_match: issues.append('coeffs differ')
            if not wire_match: issues.append('wires differ')
            print(f'  gate {i}: {\" | \".join(issues)}')
if mismatches > 15:
    print(f'  ... and {mismatches - 15} more')
if mismatches == 0:
    print('  EXACT MATCH!')
else:
    print(f'Total: {mismatches} mismatches')
"

echo ""
echo "Files: $OCAML_GATES/ vs $O1JS_GATES/"
