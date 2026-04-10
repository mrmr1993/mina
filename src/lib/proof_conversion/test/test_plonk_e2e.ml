(** End-to-end test: parse SP1 proof, prove zkp0, export for nori verification. *)

open Core_kernel
module Step = Pickles.Impls.Step

let () =
  let fixture_path = "src/lib/proof_conversion/test/plonk_e2e_fixture.json" in
  Printf.eprintf "Loading fixture from %s...\n%!" fixture_path ;
  let acc_const = Proof_conversion.Plonk_proof_json.load_fixture fixture_path in
  Printf.eprintf "Fixture loaded. Computing input hash...\n%!" ;
  (* Compute input hash = Poseidon.hashPacked(Accumulator, initial_acc) *)
  let input_hash =
    Proof_conversion.Plonk_witness_tracker.hash_accumulator_const acc_const
  in
  Printf.eprintf "Input hash: %s\n%!"
    (Step.Field.Constant.to_string input_hash) ;
  (* Create witness for zkp0: the initial accumulator *)
  let witness : Proof_conversion.Plonk_requests.witness =
    { Proof_conversion.Plonk_requests.empty_witness with
      plonk_acc = Some acc_const
    }
  in
  Printf.eprintf "Compiling and proving zkp0...\n%!" ;
  let output_hash, _proof =
    Proof_conversion.Plonk_pickles_rules.compile_and_prove_one ~n:0
      ~input_hash ~witness
  in
  Printf.eprintf "zkp0 proved successfully!\n%!" ;
  Printf.eprintf "Output hash: %s\n%!"
    (Step.Field.Constant.to_string output_hash) ;
  Printf.eprintf "Done.\n%!"
