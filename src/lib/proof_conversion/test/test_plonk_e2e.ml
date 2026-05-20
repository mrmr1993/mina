(** Full end-to-end test: prove all 24 PLONK circuits + tree compression.
    Pad to 32, merge via layer1 (16 pairs) then node layers (8→4→2→1). *)

open Core_kernel
module Step = Pickles.Impls.Step
module TC = Proof_conversion.Tree_compressor

let () =
  let fixture_path = "src/lib/proof_conversion/test/plonk_e2e_fixture.json" in
  Printf.eprintf "=== FULL PLONK E2E TEST ===\n%!" ;
  Printf.eprintf "Loading fixture...\n%!" ;
  let acc_const, aux =
    Proof_conversion.Plonk.Proof_json.load_fixture_with_aux fixture_path
  in
  let input_hash =
    Proof_conversion.Plonk.Witness_tracker.hash_accumulator_const acc_const
  in
  (* === Phase 1: Prove all 24 base circuits === *)
  Printf.eprintf "\n--- Phase 1: Proving 24 base circuits ---\n%!" ;
  let current_hash = ref input_hash in
  let current_acc = ref acc_const in
  (* Collect (input_hash, output_hash, proof, vk) for each circuit *)
  let base_proofs =
    Array.create ~len:24
      ( Step.Field.Constant.zero
      , Step.Field.Constant.zero
      , (Obj.magic () : Pickles_types.Nat.N0.n Pickles.Proof.t)
      , (Obj.magic () : Pickles.Side_loaded.Verification_key.t) )
  in
  (* zkp0-11: PLONK accumulator phase *)
  for n = 0 to 11 do
    Printf.eprintf "Proving zkp%d...\n%!" n ;
    let w : Proof_conversion.Plonk.Requests.witness =
      { Proof_conversion.Plonk.Requests.empty_witness with
        plonk_acc = Some !current_acc
      }
    in
    let output_hash, proof, vk =
      Proof_conversion.Plonk.Pickles_rules.compile_prove_and_export
        ~skip_verify:false ~n ~input_hash:!current_hash ~witness:w
    in
    (* Also get acc for chaining *)
    let _, acc_after, _ =
      Proof_conversion.Plonk.Pickles_rules.compile_and_prove_one_with_plonk_acc
        ~n ~input_hash:!current_hash ~witness:w
    in
    base_proofs.(n) <- (!current_hash, output_hash, proof, vk) ;
    current_hash := output_hash ;
    current_acc := acc_after
  done ;
  (* zkp12: KZG transition *)
  Printf.eprintf "Proving zkp12...\n%!" ;
  let w12 : Proof_conversion.Plonk.Requests.witness =
    { Proof_conversion.Plonk.Requests.empty_witness with
      plonk_acc = Some !current_acc
    ; shift_power = Some aux.shift_power
    ; c_fp12 = Some aux.c_fp12
    }
  in
  let output_hash_12, proof_12, vk_12 =
    Proof_conversion.Plonk.Pickles_rules.compile_prove_and_export
      ~skip_verify:false ~n:12 ~input_hash:!current_hash ~witness:w12
  in
  let _, kzg_const, _ =
    Proof_conversion.Plonk.Pickles_rules.compile_and_prove_zkp12
      ~input_hash:!current_hash ~witness:w12
  in
  base_proofs.(12) <- (!current_hash, output_hash_12, proof_12, vk_12) ;
  current_hash := output_hash_12 ;
  (* zkp13-16: Line hashing *)
  let current_kzg = ref kzg_const in
  let all_g_values = ref [||] in
  let ate_loop_len = Proof_conversion.Plonk.Kzg_accumulator.ate_loop_len in
  let current_lines_hashes =
    ref (Array.create ~len:ate_loop_len Step.Field.Constant.zero)
  in
  for n = 13 to 16 do
    Printf.eprintf "Proving zkp%d...\n%!" n ;
    let w : Proof_conversion.Plonk.Requests.witness =
      { Proof_conversion.Plonk.Requests.empty_witness with
        kzg_acc = Some !current_kzg
      ; lines_hashes = Some !current_lines_hashes
      }
    in
    let output_hash, proof, vk =
      Proof_conversion.Plonk.Pickles_rules.compile_prove_and_export
        ~skip_verify:false ~n ~input_hash:!current_hash ~witness:w
    in
    let _, kzg_after, lh_after, gv, _ =
      Proof_conversion.Plonk.Pickles_rules.compile_and_prove_zkp_lines
        ~circuit_index:n ~input_hash:!current_hash ~witness:w
    in
    base_proofs.(n) <- (!current_hash, output_hash, proof, vk) ;
    all_g_values := Array.append !all_g_values gv ;
    current_hash := output_hash ;
    current_kzg := kzg_after ;
    current_lines_hashes := lh_after
  done ;
  (* zkp17-22: f-accumulation *)
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
    Printf.eprintf "Proving zkp%d...\n%!" n ;
    let _, _, chunk_size, lhs_size = f_accum_params.(idx) in
    let g_chunk = Array.sub g_values ~pos:lhs_size ~len:chunk_size in
    let lhs_h = Array.sub lines_hashes ~pos:0 ~len:lhs_size in
    let rhs_start = lhs_size + chunk_size in
    let rhs_h =
      Array.sub lines_hashes ~pos:rhs_start ~len:(ate_loop_len - rhs_start)
    in
    let flat_hashes = Array.append lhs_h rhs_h in
    let w : Proof_conversion.Plonk.Requests.witness =
      { Proof_conversion.Plonk.Requests.empty_witness with
        kzg_acc = Some !current_kzg
      ; g_chunk = Some g_chunk
      ; flat_hashes = Some flat_hashes
      }
    in
    let output_hash, proof, vk =
      Proof_conversion.Plonk.Pickles_rules.compile_prove_and_export
        ~skip_verify:false ~n ~input_hash:!current_hash ~witness:w
    in
    let _, kzg_after, _ =
      Proof_conversion.Plonk.Pickles_rules.compile_and_prove_zkp_f_accum
        ~circuit_index:n ~input_hash:!current_hash ~witness:w
    in
    base_proofs.(n) <- (!current_hash, output_hash, proof, vk) ;
    current_hash := output_hash ;
    current_kzg := kzg_after
  done ;
  (* zkp23: Final pairing check *)
  Printf.eprintf "Proving zkp23...\n%!" ;
  let lhs_hashes_23 = Array.sub lines_hashes ~pos:0 ~len:(ate_loop_len - 1) in
  let g_chunk_23 = [| g_values.(ate_loop_len - 1) |] in
  let w23 : Proof_conversion.Plonk.Requests.witness =
    { Proof_conversion.Plonk.Requests.empty_witness with
      kzg_acc = Some !current_kzg
    ; lhs_hashes = Some lhs_hashes_23
    ; g_chunk = Some g_chunk_23
    }
  in
  let output_hash_23, proof_23, vk_23 =
    Proof_conversion.Plonk.Pickles_rules.compile_prove_and_export
      ~skip_verify:false ~n:23 ~input_hash:!current_hash ~witness:w23
  in
  base_proofs.(23) <- (!current_hash, output_hash_23, proof_23, vk_23) ;
  Printf.eprintf "All 24 base circuits proved!\n%!" ;
  (* === Phase 2: Layer1 compression (24 → 16 pairs, pad to 32) === *)
  Printf.eprintf
    "\n--- Phase 2: Layer1 compression (32 pairs → 16 nodes) ---\n%!" ;
  let _layer1_tag, (module Layer1Proof), layer1_prove = TC.compile_layer1 () in
  (* Pad to 32 circuits: circuits 24-31 are dummy (verify=false) *)
  let padded_proofs =
    Array.init 32 ~f:(fun i ->
        if i < 24 then
          let cin, cout, proof, vk = base_proofs.(i) in
          (cin, cout, proof, vk, true)
        else
          (* Dummy: use zkp0's proof/vk with verify=false.
             Set cin=cout=cout23 so continuity checks pass at merge boundaries. *)
          let _, _, proof, vk = base_proofs.(0) in
          let _, cout23, _, _ = base_proofs.(23) in
          (cout23, cout23, proof, vk, false) )
  in
  let layer1_results =
    Array.init 16 ~f:(fun i ->
        let li = i * 2 in
        let ri = (i * 2) + 1 in
        let cin_l, cout_l, proof_l, vk_l, verify_l = padded_proofs.(li) in
        let cin_r, cout_r, proof_r, vk_r, verify_r = padded_proofs.(ri) in
        Printf.eprintf "Layer1 node %d: zkp%d + zkp%d (verify=%b,%b)...\n%!" i
          li ri verify_l verify_r ;
        let witness : TC.layer1_witness =
          { proof_left = Pickles.Side_loaded.Proof.of_proof proof_l
          ; vk_left = vk_l
          ; verify_left = verify_l
          ; proof_right = Pickles.Side_loaded.Proof.of_proof proof_r
          ; vk_right = vk_r
          ; verify_right = verify_r
          ; pi_left = (cin_l, cout_l)
          ; pi_right = (cin_r, cout_r)
          }
        in
        let carry, proof = TC.prove_layer1 ~prover:layer1_prove ~witness in
        Printf.eprintf "  Layer1 node %d proved.\n%!" i ;
        (carry, proof) )
  in
  Printf.eprintf "Layer1 done: %d nodes\n%!" (Array.length layer1_results) ;
  (* === Phase 3: Node compression layers (16→8→4→2→1) === *)
  Printf.eprintf "\n--- Phase 3: Node compression ---\n%!" ;
  let _node_tag, (module NodeProof), node_prove = TC.compile_node () in
  (* Get the layer1 VK for node verification *)
  let layer1_vk =
    Promise.block_on_async_exn (fun () ->
        Pickles.Side_loaded.Verification_key.of_compiled_promise _layer1_tag )
  in
  let current_layer :
      (TC.subtree_carry_const * Pickles_types.Nat.N2.n Pickles.Proof.t) array
      ref =
    ref layer1_results
  in
  let current_vk = ref layer1_vk in
  let layer = ref 2 in
  while Array.length !current_layer > 1 do
    let n = Array.length !current_layer in
    Printf.eprintf "Node layer %d: %d → %d nodes\n%!" !layer n (n / 2) ;
    let next_layer =
      Array.init (n / 2) ~f:(fun i ->
          let li = i * 2 in
          let ri = (i * 2) + 1 in
          let carry_l, proof_l = !current_layer.(li) in
          let carry_r, proof_r = !current_layer.(ri) in
          Printf.eprintf "  Node %d: merge %d + %d...\n%!" i li ri ;
          let witness : TC.node_witness =
            { proof_left = Pickles.Side_loaded.Proof.of_proof proof_l
            ; vk_left = !current_vk
            ; proof_right = Pickles.Side_loaded.Proof.of_proof proof_r
            ; vk_right = !current_vk
            ; layer = !layer
            ; carry_left = carry_l
            ; carry_right = carry_r
            }
          in
          let carry, proof = TC.prove_node ~prover:node_prove ~witness in
          Printf.eprintf "  Node %d proved.\n%!" i ;
          (carry, proof) )
    in
    (* Get VK for this layer's proofs (for next layer) *)
    let node_vk =
      Promise.block_on_async_exn (fun () ->
          Pickles.Side_loaded.Verification_key.of_compiled_promise _node_tag )
    in
    current_layer := next_layer ;
    current_vk := node_vk ;
    incr layer
  done ;
  let final_carry, final_proof = !current_layer.(0) in
  let (final_left_in, final_right_out), final_vk_digest = final_carry in
  Printf.eprintf "\n=== TREE COMPRESSION COMPLETE ===\n%!" ;
  Printf.eprintf "Final leftIn:   %s\n%!"
    (Step.Field.Constant.to_string final_left_in) ;
  Printf.eprintf "Final rightOut: %s\n%!"
    (Step.Field.Constant.to_string final_right_out) ;
  Printf.eprintf "Final VK digest: %s\n%!"
    (Step.Field.Constant.to_string final_vk_digest) ;
  (* Verify: leftIn should be the initial input hash (cin0) *)
  assert (Step.Field.Constant.equal final_left_in input_hash) ;
  (* rightOut should be the final output hash (cout23) *)
  let _, cout23, _, _ = base_proofs.(23) in
  assert (Step.Field.Constant.equal final_right_out cout23) ;
  Printf.eprintf "Carry values verified: leftIn=cin0, rightOut=cout23\n%!" ;
  (* Export the final proof for cross-verification *)
  let module P = Pickles.Proof.Make (Pickles_types.Nat.N2) in
  let proof_base64 = P.to_base64 final_proof in
  let node_vk_base64 =
    Pickles.Side_loaded.Verification_key.to_base64 !current_vk
  in
  let json_proof =
    `Assoc
      [ ("publicInput", `List [])
      ; ( "publicOutput"
        , `List
            [ `String (Step.Field.Constant.to_string final_left_in)
            ; `String (Step.Field.Constant.to_string final_right_out)
            ; `String (Step.Field.Constant.to_string final_vk_digest)
            ] )
      ; ("maxProofsVerified", `Int 2)
      ; ("proof", `String proof_base64)
      ]
  in
  let json_vk = `Assoc [ ("data", `String node_vk_base64) ] in
  Yojson.Safe.to_file "src/lib/proof_conversion/test/final_proof.json"
    json_proof ;
  Yojson.Safe.to_file "src/lib/proof_conversion/test/final_vk.json" json_vk ;
  Printf.eprintf "Final proof exported to test/final_proof.json\n%!" ;
  Printf.eprintf "Final VK exported to test/final_vk.json\n%!" ;
  Printf.eprintf "\n=== ALL DONE ===\n%!"
