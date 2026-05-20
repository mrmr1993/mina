# Proof Conversion Library

This library ports the [nori-proof-conversion](https://github.com/nori-zk/proof-conversion) TypeScript/o1js circuits to OCaml. The goal is to produce **gate-identical** constraint systems so that verification keys are cross-compatible between the two implementations.

## Library layout

The library is split into focused sub-libraries, each its own dune
library with explicit dependencies (the dependency graph is acyclic and
enforced by dune):

```
src/lib/proof_conversion/
  circuit_kit/      Shared circuit helpers (Circuit_utils, Cache_config)
  bn254/            BN254 curve primitives
    towers/           Tower fields Fp2/Fp6/Fp12
    ec/               Curve points G1/G2
    lines/            Pairing-line types + Miller loop
  groth16/          Groth16 (Risc0/SP1) conversion circuits
  pairing_utils/    OCaml wrapper over the Rust pairing-utils FFI
  plonk/            PLONK (SP1) conversion circuits
    transcript/       SHA-256 + Fiat-Shamir transcript
    kzg/              KZG accumulators
  compressor/       Binary-tree proof-compression circuits
  workdir/          Staged working-directory orchestration
  proof_conversion.ml   Umbrella: re-exports each sub-library as a namespace
  test/             Test executables + the regression gate
src/app/proof_conversion/   CLI binaries (mina-proof-conversion, nori-proof-converter)
```

`bn254/` and `plonk/` use `(include_subdirs unqualified)` because their
modules are mutually recursive across the subdirectories — see the
comment in each `dune` file.

## Cross-checking against the reference implementation

Gate-level debugging against the reference TypeScript involves three
sibling repositories:

```
~/source_code/
  mina/                          # This repo (OCaml circuits)
  o1js/                          # o1js (Mina's TypeScript SNARK SDK)
    src/mina/                    # Git submodule pointing at mina repo
  nori-proof-conversion/         # Reference TypeScript implementation
```

The o1js submodule at `o1js/src/mina/` has a `local-mina` remote pointing at `../../../mina`. The `sync_and_compare.sh` script uses this to propagate mina branch changes into o1js without pushing.

## Prerequisites

- **OCaml 4.14.2** with the mina opam switch configured (`make switch` in mina root)
- **Node.js >= 22** (via nvm: `nvm use 22`)
- **nori-proof-conversion** checked out at `../nori-proof-conversion` relative to the mina root
- **o1js** checked out at `../o1js` relative to the mina root, with submodules initialized

## Building

### OCaml (mina)

```bash
# Type-check only (fast):
dune build @check

# Build the proof conversion binary:
dune build src/app/proof_conversion/main.exe

# Build a specific test:
dune build src/lib/proof_conversion/test/test_groth16_vk.exe
```

### o1js

When you modify mina's constraint system code (`plonk_constraint_system.ml`, `snarky_foreign_field/`, etc.), o1js must be rebuilt so that its js_of_ocaml bindings reflect the changes:

```bash
cd ../o1js

# 1. Point the mina submodule at your branch:
cd src/mina
git fetch local-mina <your-branch>
git reset --no-recurse-submodules --hard local-mina/<your-branch>
cd ../..

# 2. Rebuild WASM + JSOO bindings, then TypeScript:
npm run build:bindings-node   # ~5 min: compiles kimchi WASM + jsoo
npm run build                 # ~1 min: compiles TypeScript
```

If you only changed TypeScript in nori (no mina/snarky changes), you can skip the o1js rebuild entirely.

### nori-proof-conversion

```bash
cd ../nori-proof-conversion
npm install          # first time only (uses local o1js via file:../o1js)
npm run build        # compiles TypeScript
```

After rebuilding o1js, `npm run build` in nori picks up the changes automatically (nori's `package.json` has `"o1js": "file:../o1js"`).

## Regression gate

`test/verify_golden.sh` is the canonical regression gate. It compiles
every circuit the converter uses (24 PLONK base + 2 compressor + 16
Groth16 base), captures each circuit's step-circuit gate JSON via
`DUMP_PCS_GATES`, hashes it together with the Pickles `~name:` string,
and diffs the result against the committed golden
`test/golden/step_gate_digests.json`.

```bash
# Verify the circuits are unchanged (~20 min):
src/lib/proof_conversion/test/verify_golden.sh

# Regenerate the golden after an intentional circuit change:
src/lib/proof_conversion/test/regen_golden.sh
```

Step-circuit gate digests — not VK hashes — are used because they are
the only fingerprint that is byte-stable across rebuilds: Pickles'
wrap-circuit dumps and `Side_loaded` verification-key hashes drift
between otherwise-identical builds, whereas the step-circuit gate JSON
is a pure function of the constraint-system code. See
`test/golden/README.md` for the full rationale.

Any change that should leave the circuits bit-identical (refactors,
file moves, the embedded line tables) must keep this gate green; any
change that flips a digest must be an intentional, reviewed circuit
change accompanied by a `regen_golden.sh` run.

## Dumping gate sequences

Gate comparison is the primary debugging tool. Both sides can dump their constraint systems as JSON via the `DUMP_PCS_GATES` environment variable.

### OCaml side

The `DUMP_PCS_GATES` env var is checked in `plonk_constraint_system.ml`. When set, every circuit's gate list is written to `<dir>/cs_<field>_<counter>_<n>_gates.json` at finalization time.

```bash
# Dump gates for all 16 Groth16 circuits ([--info] compiles every
# circuit; COMPILE_ZKP is not honoured on the groth16 path):
mkdir -p /tmp/ocaml_gates
DUMP_PCS_GATES=/tmp/ocaml_gates \
  dune exec src/app/proof_conversion/main.exe -- \
    --proof-type groth16 --vk ../nori-proof-conversion/src/groth/example_jsons/vk.json --info

# Dump a single PLONK circuit (the plonk [--info] path honours COMPILE_ZKP):
mkdir -p /tmp/ocaml_gates
COMPILE_ZKP=zkp7 DUMP_PCS_GATES=/tmp/ocaml_gates \
  dune exec src/app/proof_conversion/main.exe -- --proof-type plonk --info
```

### Nori (TypeScript) side

Use `compile_circuits.ts` to run a circuit through the full Pickles `compile()` pipeline. This produces the same Pickles-wrapped step and wrap constraint systems that OCaml generates, making the gate dumps directly comparable. Set `DUMP_PCS_GATES` to capture the output.

The script compiles one circuit per invocation (set via `COMPILE_ZKP`) using dynamic imports to avoid loading all 16 modules and running out of memory.

```bash
cd ../nori-proof-conversion

# Compile a single circuit:
mkdir -p /tmp/nori_zkp7
COMPILE_ZKP=zkp7 DUMP_PCS_GATES=/tmp/nori_zkp7 \
  GROTH16_VK_PATH=./src/groth/example_jsons/vk.json \
  npx tsx src/groth/recursion/compile_circuits.ts

# Compile all 16 circuits (one process per circuit to avoid OOM):
mkdir -p /tmp/nori_gates
for n in $(seq 0 15); do
  echo "=== zkp$n ==="
  COMPILE_ZKP=zkp$n DUMP_PCS_GATES=/tmp/nori_gates \
    GROTH16_VK_PATH=./src/groth/example_jsons/vk.json \
    npx tsx src/groth/recursion/compile_circuits.ts
done
```

**Note**: `dump_digests.ts` uses `analyzeMethods()` which only gives the raw circuit body without the Pickles step_main wrapper. This is useful for quick gate counts and digests, but **not** for gate-level comparison with OCaml — always use `compile_circuits.ts` for that.

## Comparing gates for all circuits

The following script dumps gate sequences from both OCaml and nori for all 16 Groth16 circuits and produces a per-circuit comparison summary. Run it from the `src/lib/proof_conversion/` directory:

```bash
#!/usr/bin/env bash
# compare_all_circuits.sh — dump and compare gates for all 16 Groth16 circuits.
# Run from: mina/src/lib/proof_conversion/
set -euo pipefail

MINA_ROOT="$(cd ../../.. && pwd)"
NORI_DIR="$MINA_ROOT/../nori-proof-conversion"
OCAML_DIR="/tmp/proof_conversion_ocaml_gates"
NORI_DIR_OUT="/tmp/proof_conversion_nori_gates"

# --- Step 1: Build OCaml ---
echo "=== Building OCaml proof conversion binary ==="
cd "$MINA_ROOT"
dune build src/app/proof_conversion/main.exe

# --- Step 2: Dump OCaml gates ---
echo "=== Dumping OCaml gates ==="
rm -rf "$OCAML_DIR" && mkdir -p "$OCAML_DIR"
DUMP_PCS_GATES="$OCAML_DIR" \
  dune exec src/app/proof_conversion/main.exe -- \
    --proof-type groth16 --info 2>&1 | grep -E '\[PCS\]|error' || true

# --- Step 3: Dump nori gates (one circuit per process to avoid OOM) ---
echo "=== Compiling nori circuits ==="
rm -rf "$NORI_DIR_OUT" && mkdir -p "$NORI_DIR_OUT"
cd "$NORI_DIR"
for n in $(seq 0 15); do
  echo "  zkp$n..."
  COMPILE_ZKP=zkp$n DUMP_PCS_GATES="$NORI_DIR_OUT" \
    GROTH16_VK_PATH=./src/groth/example_jsons/vk.json \
    npx tsx src/groth/recursion/compile_circuits.ts 2>&1 | grep -E '\[PCS\]|error' || true
done

# --- Step 4: Extract gate type lists ---
echo "=== Extracting gate types ==="
mkdir -p /tmp/proof_conversion_comparison

# Both sides use DUMP_PCS_GATES which produces cs_30ED_0_<N>_gates.json
# for Pickles step circuits.  compile() dumps each step circuit twice
# (compilation + VK), so even-numbered N are unique circuits.
# With compile_circuits.ts running circuits sequentially, zkpK maps to
# N = K*2 on both sides.
for n in $(seq 0 15); do
  nori_file="$NORI_DIR_OUT/cs_30ED_0_$((n * 2))_gates.json"
  if [ -f "$nori_file" ]; then
    jq -r '.gates[].typ' "$nori_file" > "/tmp/proof_conversion_comparison/nori_zkp${n}.txt"
  fi
done

for n in $(seq 0 15); do
  ocaml_file="$OCAML_DIR/cs_30ED_0_$((n * 2))_gates.json"
  if [ -f "$ocaml_file" ]; then
    jq -r '.gates[].typ' "$ocaml_file" > "/tmp/proof_conversion_comparison/ocaml_zkp${n}.txt"
  fi
done

# --- Step 5: Compare ---
echo ""
echo "=== Per-circuit comparison ==="
printf "%-8s %12s %12s %10s\n" "Circuit" "OCaml" "Nori" "Delta"
printf "%-8s %12s %12s %10s\n" "-------" "-----" "----" "-----"

for n in $(seq 0 15); do
  ocaml_f="/tmp/proof_conversion_comparison/ocaml_zkp${n}.txt"
  nori_f="/tmp/proof_conversion_comparison/nori_zkp${n}.txt"
  if [ -f "$ocaml_f" ] && [ -f "$nori_f" ]; then
    oc=$(wc -l < "$ocaml_f")
    nr=$(wc -l < "$nori_f")
    delta=$((oc - nr))
    sign=""; [ "$delta" -gt 0 ] && sign="+"
    printf "zkp%-5d %12d %12d %10s\n" "$n" "$oc" "$nr" "${sign}${delta}"
  elif [ -f "$nori_f" ]; then
    nr=$(wc -l < "$nori_f")
    printf "zkp%-5d %12s %12d %10s\n" "$n" "(missing)" "$nr" "—"
  else
    printf "zkp%-5d %12s %12s %10s\n" "$n" "?" "?" "—"
  fi
done

echo ""
echo "Gate type files: /tmp/proof_conversion_comparison/{ocaml,nori}_zkpN.txt"
echo ""
echo "To diff a specific circuit (e.g., zkp7):"
echo "  diff /tmp/proof_conversion_comparison/{ocaml,nori}_zkp7.txt"
echo ""
echo "To see the first divergence point:"
echo "  diff /tmp/proof_conversion_comparison/{ocaml,nori}_zkp7.txt | head -20"
echo ""
echo "To count mismatches by gate type:"
echo "  diff --side-by-side /tmp/proof_conversion_comparison/{ocaml,nori}_zkp7.txt | grep '|' | awk '{print \$1, \$3}' | sort | uniq -c | sort -rn"
```

### Comparing a single circuit

To quickly compare one circuit without running all 16:

```bash
# Nori side — compile zkp7 through Pickles:
cd ../nori-proof-conversion
rm -rf /tmp/nori_zkp7 && mkdir -p /tmp/nori_zkp7
COMPILE_ZKP=zkp7 DUMP_PCS_GATES=/tmp/nori_zkp7 \
  GROTH16_VK_PATH=./src/groth/example_jsons/vk.json \
  npx tsx src/groth/recursion/compile_circuits.ts
jq -r '.gates[].typ' /tmp/nori_zkp7/cs_30ED_0_0_gates.json > /tmp/nori_zkp7_types.txt

# OCaml side — compile zkp7 through Pickles:
cd ../mina
rm -rf /tmp/ocaml_zkp7 && mkdir -p /tmp/ocaml_zkp7
DUMP_PCS_GATES=/tmp/ocaml_zkp7 \
  dune exec src/app/proof_conversion/main.exe -- \
    --proof-type groth16 --info 2>&1 | grep '\[PCS\]'
jq -r '.gates[].typ' /tmp/ocaml_zkp7/cs_30ED_0_0_gates.json > /tmp/ocaml_zkp7_types.txt

# Compare:
diff /tmp/{ocaml,nori}_zkp7_types.txt | head -30
```

Both sides produce `cs_30ED_0_*_gates.json` files with the same JSON schema (`gates[].typ`), so the `jq` expression is identical.

### Understanding `DUMP_PCS_GATES` file naming

Files are named `cs_<FIELD>_<MAKE>_<N>_gates.json`:

| Component | Description |
|-----------|-------------|
| `FIELD` | Last 4 hex digits of the field modulus: `30ED` = Vesta (step circuits), `EB21` = Pallas (wrap circuits) |
| `MAKE` | PCS module instance counter. `0` = Pickles step/wrap circuits (the ones to compare) |
| `N` | Auto-incrementing dump counter across all circuits in the process |

When using `compile()`, both sides produce `cs_30ED_0_*` files for step circuits. Pickles dumps each step circuit **twice** (once at compilation, once at VK computation), producing identical files. So `N=0,2,4,...` are unique step circuits for zkp0, zkp1, zkp2, etc., and `N=1,3,5,...` are duplicates.

Nori's compile also produces `cs_30ED_2_*` files — these are the raw circuit bodies **without** the Pickles step_main wrapper and should be ignored for comparison purposes.

### Gate comparison test executable

```bash
dune exec src/lib/proof_conversion/test/test_gate_comparison.exe -- \
  --reference /tmp/nori_gates --candidate /tmp/ocaml_gates
```

This reports the first divergence point, gate count delta by type, and total mismatches.

## Using markers for fine-grained alignment

The `Gadgets.marker(id)` function in o1js emits a Zero gate with identifiable coefficients `[id, 1, 2, 3, 4, 5, 6]`. On the OCaml side, the equivalent is:

```ocaml
(* OCaml marker *)
Step.assert_
  (Raw { kind = Zero
       ; values = [| Step.Field.zero; Step.Field.zero; Step.Field.zero |]
       ; coeffs = Array.map ~f:Step.Field.Constant.of_int [| id; 1; 2; 3; 4; 5; 6 |]
       })
```

```typescript
// TypeScript marker (requires o1js with Gadgets.marker)
Gadgets.marker(8000);
```

Insert matching marker IDs on both sides to bisect which section of a circuit diverges. Markers add one Zero gate each, so remove them before final gate-count comparisons.

**Important**: markers call `Gates.raw()` which requires a Snarky context. They will crash if called outside `Provable.constraintSystem()` / `analyzeMethods()` (e.g., during VK constant precomputation at module load time). Guard with a counter or flag if needed.

### Locating markers in gate dumps

```bash
# Find all markers in a nori gate dump:
python3 -c "
import json, sys
with open(sys.argv[1]) as f:
    data = json.load(f)
gates = data.get('full_gates', data.get('gates', []))
for i, g in enumerate(gates):
    typ = g.get('typ', g.get('type', ''))
    coeffs = g.get('coeffs', [])
    if typ == 'Zero' and len(coeffs) >= 7:
        try:
            c0 = int(coeffs[0], 16) if isinstance(coeffs[0], str) else coeffs[0]
            c1 = int(coeffs[1], 16) if isinstance(coeffs[1], str) else coeffs[1]
            if c1 == 1:
                print(f'  row {i}: marker {c0}')
        except: pass
" /tmp/nori_zkp7.json

# Same for an OCaml gate dump:
python3 -c "
import json, sys
with open(sys.argv[1]) as f:
    data = json.load(f)
for i, g in enumerate(data['gates']):
    coeffs = g.get('coeffs', [])
    if g.get('typ') == 'Zero' and len(coeffs) >= 7:
        try:
            c0 = int(coeffs[0], 16)
            c1 = int(coeffs[1], 16)
            if c1 == 1:
                print(f'  row {i}: marker {c0}')
        except: pass
" /tmp/ocaml_zkp7/cs_30ED_0_0_gates.json
```

## Automated sync and compare

The `sync_and_compare.sh` script automates the full workflow for comparing **Pickles-level** (wrap circuit) gates between OCaml-native and o1js:

```bash
./src/lib/proof_conversion/test/sync_and_compare.sh
```

This:
1. Syncs the current mina branch (including uncommitted changes) into the o1js submodule
2. Rebuilds o1js bindings + TypeScript
3. Builds the OCaml compatibility test
4. Dumps gates from both sides
5. Runs a Python comparison of the wrap circuits

Output goes to `/tmp/sync_and_compare.log`. Use `--skip-rebuild` to skip the o1js rebuild if bindings haven't changed (note: the script always rebuilds TypeScript regardless of this flag).

## Generating reference fixtures

```bash
# Generate nori gate fixtures for all Groth16 circuits:
./src/lib/proof_conversion/test/generate_gate_fixtures.sh groth16 /tmp/nori_fixtures

# Generate nori gate fixtures for all PLONK circuits:
./src/lib/proof_conversion/test/generate_gate_fixtures.sh plonk /tmp/nori_plonk_fixtures
```

## Test executables

| Executable | Purpose |
|------------|---------|
| `test_step_gate_golden` | The regression gate's driver — see "Regression gate" above. Run via `verify_golden.sh`. |
| `test_plonk_e2e` | Full end-to-end PLONK conversion: proves all 24 base circuits + the compression tree from a committed fixture. |
| `test_pairing_utils` | Checks the Rust pairing-utils FFI against the committed Groth16 example fixture. |
| `test_tower_field` | Unit tests for Fp2/Fp6/Fp12 arithmetic. |
| `test_groth16_vk` | Per-circuit Groth16 VK hash dump (defaults to the committed example VK; override with `GROTH16_VK_PATH`). |
| `test_pickles_compat` | Validates the Pickles pipeline against o1js-equivalent VK hashes. |
| `test_gate_comparison` | Compares two directories of gate JSON dumps (`--reference` / `--candidate`). |

Run any of them from the workspace root with:

```bash
dune exec src/lib/proof_conversion/test/<name>.exe
```

## Environment variables reference

| Variable | Description |
|----------|-------------|
| `DUMP_PCS_GATES=<dir>` | Write gate JSONs for every finalized circuit to `<dir>/` |
| `COMPILE_ZKP=<name>` | Select a single circuit to compile (e.g. `zkp7`). Required by nori's `compile_circuits.ts`; honoured by `mina-proof-conversion --proof-type plonk --info` (the groth16 `--info` path always compiles all circuits) |
| `DUMP_ZKP=<name>` | In nori's `dump_digests.ts`: dump raw (non-Pickles) CS for one circuit |
| `GROTH16_VK_PATH=<path>` | Path to Groth16 VK JSON (required by nori Groth16 circuits) |
| `SKIP_RECURSIVE=1` | In `test_pickles_compat`: skip the recursive test, run simple test only |

## Typical debugging workflow

1. Make a change to the OCaml circuit code
2. `dune build @check` to verify it compiles
3. Run the comparison script above, or dump a single circuit for quick iteration
4. If gate counts diverge, add markers on both sides to bisect the divergence
5. Diff the gate type lists to find the first mismatch
6. Once identified, inspect coefficients and wiring with `jq` on the full gate JSON

If you changed `plonk_constraint_system.ml` or `snarky_foreign_field/`, you must also rebuild o1js before dumping nori gates (see "Building > o1js" above).
