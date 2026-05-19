# proof_conversion regression-gate goldens

This directory holds the canonical regression artifact every refactor of
`src/lib/proof_conversion/` must preserve byte-for-byte.

## What's here

| File | What it is |
|---|---|
| `step_gate_digests.json` | Sorted map `{ "<circuit>": "<sha256>" }` over every circuit the converter compiles: 24 PLONK base + 2 compressor (layer1, node) + 16 Groth16 base. The hash input is `<pickles_name>\n<step_circuit_gate_dump_bytes>`. |

## Why step-circuit gate digests

Pickles' step-circuit gate JSONs (the `cs_30ED_*` dumps under
`DUMP_PCS_GATES=`) are pure functions of the OCaml constraint-system
code: identical source produces byte-identical dumps, even after a full
clean rebuild.

Two other plausible fingerprints were rejected:

- **VK hashes drift across rebuilds.** Empirically, the same source code
  compiled twice with no changes produces different Pickles `Side_loaded`
  verification-key hashes. Something in Pickles' wrap-circuit derivation
  (likely SRS-commitment or wrap-domain bookkeeping) is non-deterministic
  across builds. Production handles this by pinning VKs in an on-disk
  cache shipped with the workers; per-commit VK diffs would never be
  green.
- **Proof bytes are non-deterministic at runtime.** Pickles' kimchi
  prover passes `&mut rand::rngs::OsRng` to `ProverProof::create_recursive`,
  so two runs of the same prover produce two different proofs even on
  the same binary.

Step-circuit gate dumps avoid both problems and capture every gate, wire,
and coefficient — strictly stronger than a VK hash even if VKs were
stable. The hash input includes the `~name:` argument to
`Pickles.compile_promise`, so a refactor that accidentally renames a
circuit (which would silently change the production VK) still flips the
digest.

## Running the gate

```bash
# Diff actual step-gate digests against golden (~20 minutes):
src/lib/proof_conversion/test/verify_golden.sh

# Regenerate the golden (only after intentional semantic changes):
src/lib/proof_conversion/test/regen_golden.sh
```

The driver is `src/lib/proof_conversion/test/test_step_gate_golden.ml`.
The gate is invoked via a shell script rather than a dune rule because
the `proof_conversion` library hardcodes workspace-relative data-file
paths (e.g. `src/lib/proof_conversion/plonk/data/g2_lines.json`) that
are not available in dune's sandbox. The script chdir's to the workspace
root and runs the driver with `DUMP_PCS_GATES` pointing at a fresh
tempdir, then diffs the per-circuit step-dump sha256 map against this
file.
