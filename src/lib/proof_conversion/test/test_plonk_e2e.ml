(** End-to-end test: prove zkp0+zkp1 and merge with layer1 tree compressor. *)

open Core_kernel
module Step = Pickles.Impls.Step

let () =
  let fixture_path = "src/lib/proof_conversion/test/plonk_e2e_fixture.json" in
  Printf.eprintf "Loading fixture...\n%!" ;
  let acc_const, _aux =
    Proof_conversion.Plonk_proof_json.load_fixture_with_aux fixture_path
  in
  let input_hash =
    Proof_conversion.Plonk_witness_tracker.hash_accumulator_const acc_const
  in
  (* Prove zkp0 with VK *)
  Printf.eprintf "Proving zkp0...\n%!" ;
  let w0 : Proof_conversion.Plonk_requests.witness =
    { Proof_conversion.Plonk_requests.empty_witness with
      plonk_acc = Some acc_const
    }
  in
  let output_hash_0, proof_0, vk_0 =
    Proof_conversion.Plonk_pickles_rules.compile_prove_and_export ~n:0
      ~input_hash ~witness:w0
  in
  Printf.eprintf "  zkp0 proved. Output: %s\n%!"
    (Step.Field.Constant.to_string output_hash_0) ;
  (* Prove zkp1 — need acc after zkp0 *)
  Printf.eprintf "Proving zkp0 with acc chaining for zkp1...\n%!" ;
  let _, acc_after_0, _ =
    Proof_conversion.Plonk_pickles_rules.compile_and_prove_one_with_plonk_acc
      ~n:0 ~input_hash ~witness:w0
  in
  let w1 : Proof_conversion.Plonk_requests.witness =
    { Proof_conversion.Plonk_requests.empty_witness with
      plonk_acc = Some acc_after_0
    }
  in
  let output_hash_1, proof_1, vk_1 =
    Proof_conversion.Plonk_pickles_rules.compile_prove_and_export ~n:1
      ~input_hash:output_hash_0 ~witness:w1
  in
  Printf.eprintf "  zkp1 proved. Output: %s\n%!"
    (Step.Field.Constant.to_string output_hash_1) ;
  (* Now merge with layer1 *)
  Printf.eprintf "Compiling layer1 circuit...\n%!" ;
  let _layer1_tag, (module Layer1Proof), layer1_prove =
    Proof_conversion.Tree_compressor.compile_layer1 ()
  in
  Printf.eprintf "Layer1 compiled. Proving merge of zkp0+zkp1...\n%!" ;
  let layer1_witness : Proof_conversion.Tree_compressor.layer1_witness =
    { proof_left = Pickles.Side_loaded.Proof.of_proof proof_0
    ; vk_left = vk_0
    ; verify_left = true
    ; proof_right = Pickles.Side_loaded.Proof.of_proof proof_1
    ; vk_right = vk_1
    ; verify_right = true
    ; pi_left = (input_hash, output_hash_0)
    ; pi_right = (output_hash_0, output_hash_1)
    }
  in
  let carry, _layer1_proof =
    Proof_conversion.Tree_compressor.prove_layer1 ~prover:layer1_prove
      ~witness:layer1_witness
  in
  let (left_in, right_out), _vk_digest = carry in
  Printf.eprintf "Layer1 proved!\n%!" ;
  Printf.eprintf "  leftIn:   %s\n%!" (Step.Field.Constant.to_string left_in) ;
  Printf.eprintf "  rightOut: %s\n%!" (Step.Field.Constant.to_string right_out) ;
  (* Verify carry values *)
  assert (Step.Field.Constant.equal left_in input_hash) ;
  assert (Step.Field.Constant.equal right_out output_hash_1) ;
  Printf.eprintf "Layer1 carry values correct!\n%!" ;
  Printf.eprintf "Done.\n%!"
