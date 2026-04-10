(** End-to-end test: parse SP1 proof, prove all 24 PLONK circuits. *)

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
  (* === Phase 1: zkp0-11 (PLONK accumulator) === *)
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
  (* === Phase 2: zkp12 (KZG transition) === *)
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
  (* === Phase 3: zkp13-16 (line hashing, collect g values) === *)
  let current_kzg = ref kzg_const in
  let all_g_values = ref [||] in
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
    let output_hash, kzg_after, lh_after, gv, _proof =
      Proof_conversion.Plonk_pickles_rules.compile_and_prove_zkp_lines
        ~circuit_index:n ~input_hash:!current_hash ~witness
    in
    Printf.eprintf "  zkp%d proved. Output: %s (%d g values)\n%!" n
      (Step.Field.Constant.to_string output_hash)
      (Array.length gv) ;
    all_g_values := Array.append !all_g_values gv ;
    current_hash := output_hash ;
    current_kzg := kzg_after ;
    current_lines_hashes := lh_after
  done ;
  Printf.eprintf "Collected %d total g values\n%!" (Array.length !all_g_values) ;
  (* === Phase 4: zkp17-22 (f-accumulation) === *)
  let g_values = !all_g_values in
  let lines_hashes = !current_lines_hashes in
  let f_accum_params =
    [| (1, 10, 9, 0)
     ; (10, 21, 11, 9)
     ; (21, 32, 11, 20)
     ; (32, 43, 11, 31)
     ; (43, 54, 11, 42)
     ; (54, 65, 11, 53)
    |]
  in
  for idx = 0 to 5 do
    let n = 17 + idx in
    let _from_i, _to_i, chunk_size, lhs_size = f_accum_params.(idx) in
    Printf.eprintf "Proving zkp%d (f-accumulation)...\n%!" n ;
    (* Extract g_chunk: g_values[lhs_size .. lhs_size+chunk_size) *)
    let g_chunk = Array.sub g_values ~pos:lhs_size ~len:chunk_size in
    (* Build flat_hashes: lhs ++ rhs (lines_hashes with chunk entries removed) *)
    let lhs_hashes = Array.sub lines_hashes ~pos:0 ~len:lhs_size in
    let rhs_start = lhs_size + chunk_size in
    let rhs_hashes =
      Array.sub lines_hashes ~pos:rhs_start ~len:(ate_loop_len - rhs_start)
    in
    let flat_hashes = Array.append lhs_hashes rhs_hashes in
    let witness : Proof_conversion.Plonk_requests.witness =
      { Proof_conversion.Plonk_requests.empty_witness with
        kzg_acc = Some !current_kzg
      ; g_chunk = Some g_chunk
      ; flat_hashes = Some flat_hashes
      }
    in
    let output_hash, kzg_after, _proof =
      Proof_conversion.Plonk_pickles_rules.compile_and_prove_zkp_f_accum
        ~circuit_index:n ~input_hash:!current_hash ~witness
    in
    Printf.eprintf "  zkp%d proved. Output: %s\n%!" n
      (Step.Field.Constant.to_string output_hash) ;
    current_hash := output_hash ;
    current_kzg := kzg_after
  done ;
  (* === Phase 5: zkp23 (final pairing check) === *)
  Printf.eprintf "Proving zkp23 (final pairing check)...\n%!" ;
  let lhs_hashes_23 = Array.sub lines_hashes ~pos:0 ~len:(ate_loop_len - 1) in
  let g_chunk_23 = [| g_values.(ate_loop_len - 1) |] in
  let witness_23 : Proof_conversion.Plonk_requests.witness =
    { Proof_conversion.Plonk_requests.empty_witness with
      kzg_acc = Some !current_kzg
    ; lhs_hashes = Some lhs_hashes_23
    ; g_chunk = Some g_chunk_23
    }
  in
  let output_hash_23, _proof_23 =
    Proof_conversion.Plonk_pickles_rules.compile_and_prove_one ~n:23
      ~input_hash:!current_hash ~witness:witness_23
  in
  Printf.eprintf "  zkp23 proved. Output: %s\n%!"
    (Step.Field.Constant.to_string output_hash_23) ;
  Printf.eprintf "ALL 24 PLONK CIRCUITS PROVED SUCCESSFULLY!\n%!" ;
  Printf.eprintf "Done.\n%!"
