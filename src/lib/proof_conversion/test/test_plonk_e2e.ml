(** End-to-end test: parse SP1 proof, prove zkp0-11 with accumulator chaining. *)

open Core_kernel
module Step = Pickles.Impls.Step

let () =
  let fixture_path = "src/lib/proof_conversion/test/plonk_e2e_fixture.json" in
  Printf.eprintf "Loading fixture from %s...\n%!" fixture_path ;
  let acc_const = Proof_conversion.Plonk_proof_json.load_fixture fixture_path in
  let input_hash =
    Proof_conversion.Plonk_witness_tracker.hash_accumulator_const acc_const
  in
  Printf.eprintf "Initial hash: %s\n%!"
    (Step.Field.Constant.to_string input_hash) ;
  let current_hash = ref input_hash in
  let current_acc = ref acc_const in
  for n = 0 to 11 do
    Printf.eprintf "Proving zkp%d...\n%!" n ;
    let witness : Proof_conversion.Plonk_requests.witness =
      { Proof_conversion.Plonk_requests.empty_witness with
        plonk_acc = Some !current_acc
      }
    in
    let output_hash, acc_after, _proof =
      Proof_conversion.Plonk_pickles_rules.compile_and_prove_one_with_plonk_acc
        ~n ~input_hash:!current_hash ~witness
    in
    Printf.eprintf "  zkp%d proved. Output: %s\n%!" n
      (Step.Field.Constant.to_string output_hash) ;
    current_hash := output_hash ;
    current_acc := acc_after
  done ;
  Printf.eprintf "All 12 PLONK accumulator circuits proved successfully!\n%!" ;
  Printf.eprintf "Done.\n%!"
