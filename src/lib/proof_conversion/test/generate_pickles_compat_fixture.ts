/**
 * Generate a gate-sequence fixture for a trivial ZkProgram.
 *
 * Run from the o1js repo root:
 *   npx tsx <path-to-this-script>
 *
 * Outputs JSON to stdout with the gate types for the step circuit.
 */
import { Field, ZkProgram, Provable } from 'o1js';

async function main() {
  const Trivial = ZkProgram({
    name: 'trivial-compat-test',
    methods: {
      compute: {
        privateInputs: [],
        async method() {
          // Empty circuit body — we only care about the Pickles overhead
        },
      },
    },
  });

  const analysis = await Trivial.analyzeMethods();
  const gates = analysis.compute.gates.map(
    (g: { type: string }) => g.type
  );

  const result = {
    name: 'trivial-compat-test',
    gate_count: gates.length,
    gates: gates,
  };

  console.log(JSON.stringify(result, null, 2));
}

main();
