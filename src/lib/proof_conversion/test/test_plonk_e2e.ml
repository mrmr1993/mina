(** End-to-end test: parse SP1 proof, prove zkp0-16 with accumulator chaining. *)

open Core_kernel
module Step = Pickles.Impls.Step

let () =
  let fixture_path = "src/lib/proof_conversion/test/plonk_e2e_fixture.json" in
  Printf.eprintf "Loading fixture from %s...\n%!" fixture_path ;
  let acc_const, aux =
    Proof_conversion.Plonk_proof_json.load_fixture_with_aux fixture_path
  in
  let input_hash =
    Proof_conversion.Plonk_witness_tracker.hash_accumulator_const acc_const
  in
  Printf.eprintf "Initial hash: %s\n%!"
    (Step.Field.Constant.to_string input_hash) ;
  (* Chain circuits 0-11 *)
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
  (* zkp12: transition to KZG accumulator *)
  Printf.eprintf "Proving zkp12 (KZG transition)...\n%!" ;
  let witness_12 : Proof_conversion.Plonk_requests.witness =
    { Proof_conversion.Plonk_requests.empty_witness with
      plonk_acc = Some !current_acc
    ; shift_power = Some aux.shift_power
    ; c_fp12 = Some aux.c_fp12
    }
  in
  let output_hash_12, kzg_const, _proof_12 =
    Proof_conversion.Plonk_pickles_rules.compile_and_prove_zkp12
      ~input_hash:!current_hash ~witness:witness_12
  in
  Printf.eprintf "  zkp12 proved. Output: %s\n%!"
    (Step.Field.Constant.to_string output_hash_12) ;
  current_hash := output_hash_12 ;
  (* zkp13-16: line hashing circuits with KZG chaining *)
  let current_kzg = ref kzg_const in
  let ate_loop_len = Proof_conversion.Kzg_accumulator.ate_loop_len in
  let current_lines_hashes =
    ref (Array.create ~len:ate_loop_len Step.Field.Constant.zero)
  in
  for n = 13 to 16 do
    Printf.eprintf "Proving zkp%d (line hashing)...\n%!" n ;
    let witness : Proof_conversion.Plonk_requests.witness =
      { Proof_conversion.Plonk_requests.empty_witness with
        kzg_acc = Some !current_kzg
      ; lines_hashes = Some !current_lines_hashes
      }
    in
    let output_hash, kzg_after, lh_after, _proof =
      Proof_conversion.Plonk_pickles_rules.compile_and_prove_zkp_lines
        ~circuit_index:n ~input_hash:!current_hash ~witness
    in
    Printf.eprintf "  zkp%d proved. Output: %s\n%!" n
      (Step.Field.Constant.to_string output_hash) ;
    current_hash := output_hash ;
    current_kzg := kzg_after ;
    current_lines_hashes := lh_after
  done ;
  Printf.eprintf "All 17 circuits (zkp0-16) proved successfully!\n%!" ;
  Printf.eprintf "Done.\n%!"
