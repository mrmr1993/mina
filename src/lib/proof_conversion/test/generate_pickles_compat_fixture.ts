/**
 * Generate gate dumps for the Pickles compatibility test circuits.
 *
 * Run from the o1js repo root:
 *   DUMP_PCS_GATES=/tmp/o1js_compat_gates node --experimental-specifier-resolution=node -e "require('./dist/node/index.cjs')" -e "..."
 *
 * Or more practically:
 *   cd <o1js-repo>
 *   DUMP_PCS_GATES=/tmp/o1js_compat_gates node -e "
 *     const { Field, ZkProgram, Gadgets } = require('./dist/node/index.cjs');
 *     ... (inline the code below)
 *   "
 *
 * This script matches the OCaml test_pickles_compat.ml Simple circuit.
 */
import { Field, ZkProgram, Provable, Gadgets } from 'o1js';

/**
 * Inject a Zero gate marker with coefficients [x, 1, 2, 3, 4, 5, 6].
 * Matches the OCaml `marker` function in test_pickles_compat.ml.
 */
function marker(x: number) {
  // Gadgets.addRaw injects a raw plonk constraint
  // For now, use the Snarky bindings directly
  (Provable as any).asProver(() => {});
  // TODO: inject Zero gate with coeffs [x, 1, 2, 3, 4, 5, 6]
  // This requires access to the low-level constraint API
}

async function main() {
  // Simple test: matches OCaml Simple module
  const Simple = ZkProgram({
    name: 'simple-compat-test',
    publicInput: Provable.Array(Field, 1),
    publicOutput: Provable.Array(Field, 0),
    methods: {
      compute: {
        privateInputs: [],
        async method(pub: Field[]) {
          // marker(1000);  // TODO: inject when raw constraint API available
          // dummy_constraints are injected by o1js automatically
          // marker(1001);
          const x = Provable.witness(Field, () => Field(0));
          const xSq = x.mul(x);
          pub[0].assertEquals(xSq);
          // marker(1002);
          return [];
        },
      },
    },
  });

  console.log('Compiling simple-compat-test...');
  await Simple.compile();
  console.log('Done. Gate dumps written to DUMP_PCS_GATES directory.');

  const analysis = await Simple.analyzeMethods();
  const method = analysis.compute;
  console.log(`Step circuit: ${method.rows} gates, digest=${method.digest}`);
}

main().catch((e) => {
  console.error(e);
  process.exit(1);
});
