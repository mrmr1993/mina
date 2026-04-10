(** End-to-end test: parse SP1 proof, prove zkp0+zkp1 with chaining. *)

open Core_kernel
module Step = Pickles.Impls.Step

let () =
  let fixture_path = "src/lib/proof_conversion/test/plonk_e2e_fixture.json" in
  Printf.eprintf "Loading fixture from %s...\n%!" fixture_path ;
  let acc_const = Proof_conversion.Plonk_proof_json.load_fixture fixture_path in
  let input_hash_0 =
    Proof_conversion.Plonk_witness_tracker.hash_accumulator_const acc_const
  in
  Printf.eprintf "Input hash 0: %s\n%!"
    (Step.Field.Constant.to_string input_hash_0) ;
  (* Prove zkp0 with auxiliary_output chaining *)
  Printf.eprintf "Proving zkp0 (with acc chaining)...\n%!" ;
  let witness_0 : Proof_conversion.Plonk_requests.witness =
    { Proof_conversion.Plonk_requests.empty_witness with
      plonk_acc = Some acc_const
    }
  in
  let output_hash_0, acc_after_0, _proof_0 =
    Proof_conversion.Plonk_pickles_rules.compile_and_prove_one_with_plonk_acc
      ~n:0 ~input_hash:input_hash_0 ~witness:witness_0
  in
  Printf.eprintf "zkp0 proved! Output hash: %s\n%!"
    (Step.Field.Constant.to_string output_hash_0) ;
  (* Prove zkp1 using acc_after_0 as witness *)
  Printf.eprintf "Proving zkp1 (chained from zkp0)...\n%!" ;
  let witness_1 : Proof_conversion.Plonk_requests.witness =
    { Proof_conversion.Plonk_requests.empty_witness with
      plonk_acc = Some acc_after_0
    }
  in
  let output_hash_1, _acc_after_1, _proof_1 =
    Proof_conversion.Plonk_pickles_rules.compile_and_prove_one_with_plonk_acc
      ~n:1 ~input_hash:output_hash_0 ~witness:witness_1
  in
  Printf.eprintf "zkp1 proved! Output hash: %s\n%!"
    (Step.Field.Constant.to_string output_hash_1) ;
  Printf.eprintf "Chaining successful: zkp0 -> zkp1\n%!" ;
  Printf.eprintf "Done.\n%!"
