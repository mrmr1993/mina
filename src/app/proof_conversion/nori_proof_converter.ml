(** Nori proof converter CLI — drop-in replacement for the nori binary.

    Usage:
      nori-proof-converter sp1ToPlonk <input.json> <aux_witness.json>

    The input.json can be either:
    - SP1 format: {proof:{Plonk:{encoded_proof,public_inputs}},public_values:{buffer:{data}}}
    - Fixture format: {hexProof, programVk, piHex, auxWtns}

    Output is written to <input>.sp1ToPlonk.json *)

open Core_kernel
module Step = Pickles.Impls.Step
module TC = Proof_conversion.Tree_compressor

let run_sp1_to_plonk ~input_path ~aux_path =
  Printf.eprintf "=== SP1 to PLONK Proof Conversion ===\n%!" ;
  (* Load input *)
  let acc_const, aux =
    (* Try fixture format first, fall back to SP1 format *)
    try Proof_conversion.Plonk_proof_json.load_fixture_with_aux input_path
    with _ ->
      let acc = Proof_conversion.Plonk_proof_json.load_sp1 input_path in
      let aux_json = Yojson.Safe.from_file aux_path in
      let aux = Proof_conversion.Plonk_proof_json.parse_aux_witness aux_json in
      (acc, aux)
  in
  let input_hash =
    Proof_conversion.Plonk_witness_tracker.hash_accumulator_const acc_const
  in
  Printf.eprintf "Initial hash: %s\n%!"
    (Step.Field.Constant.to_string input_hash) ;
  (* === Prove all 24 base circuits === *)
  Printf.eprintf "Proving 24 base circuits...\n%!" ;
  let current_hash = ref input_hash in
  let current_acc = ref acc_const in
  let base_proofs =
    Array.create ~len:24
      ( Step.Field.Constant.zero
      , Step.Field.Constant.zero
      , (Obj.magic () : Pickles_types.Nat.N0.n Pickles.Proof.t)
      , (Obj.magic () : Pickles.Side_loaded.Verification_key.t) )
  in
  (* zkp0-11 *)
  for n = 0 to 11 do
    Printf.eprintf "  zkp%d...\n%!" n ;
    let w : Proof_conversion.Plonk_requests.witness =
      { Proof_conversion.Plonk_requests.empty_witness with
        plonk_acc = Some !current_acc
      }
    in
    let output_hash, proof, vk =
      Proof_conversion.Plonk_pickles_rules.compile_prove_and_export ~n
        ~input_hash:!current_hash ~witness:w
    in
    let _, acc_after, _ =
      Proof_conversion.Plonk_pickles_rules.compile_and_prove_one_with_plonk_acc
        ~n ~input_hash:!current_hash ~witness:w
    in
    base_proofs.(n) <- (!current_hash, output_hash, proof, vk) ;
    current_hash := output_hash ;
    current_acc := acc_after
  done ;
  (* zkp12 *)
  Printf.eprintf "  zkp12...\n%!" ;
  let w12 : Proof_conversion.Plonk_requests.witness =
    { Proof_conversion.Plonk_requests.empty_witness with
      plonk_acc = Some !current_acc
    ; shift_power = Some aux.shift_power
    ; c_fp12 = Some aux.c_fp12
    }
  in
  let output_hash_12, proof_12, vk_12 =
    Proof_conversion.Plonk_pickles_rules.compile_prove_and_export ~n:12
      ~input_hash:!current_hash ~witness:w12
  in
  let _, kzg_const, _ =
    Proof_conversion.Plonk_pickles_rules.compile_and_prove_zkp12
      ~input_hash:!current_hash ~witness:w12
  in
  base_proofs.(12) <- (!current_hash, output_hash_12, proof_12, vk_12) ;
  current_hash := output_hash_12 ;
  (* zkp13-16 *)
  let current_kzg = ref kzg_const in
  let all_g_values = ref [||] in
  let ate_loop_len = Proof_conversion.Kzg_accumulator.ate_loop_len in
  let current_lines_hashes =
    ref (Array.create ~len:ate_loop_len Step.Field.Constant.zero)
  in
  for n = 13 to 16 do
    Printf.eprintf "  zkp%d...\n%!" n ;
    let w : Proof_conversion.Plonk_requests.witness =
      { Proof_conversion.Plonk_requests.empty_witness with
        kzg_acc = Some !current_kzg
      ; lines_hashes = Some !current_lines_hashes
      }
    in
    let output_hash, proof, vk =
      Proof_conversion.Plonk_pickles_rules.compile_prove_and_export ~n
        ~input_hash:!current_hash ~witness:w
    in
    let _, kzg_after, lh_after, gv, _ =
      Proof_conversion.Plonk_pickles_rules.compile_and_prove_zkp_lines
        ~circuit_index:n ~input_hash:!current_hash ~witness:w
    in
    base_proofs.(n) <- (!current_hash, output_hash, proof, vk) ;
    all_g_values := Array.append !all_g_values gv ;
    current_hash := output_hash ;
    current_kzg := kzg_after ;
    current_lines_hashes := lh_after
  done ;
  (* zkp17-22 *)
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
    Printf.eprintf "  zkp%d...\n%!" n ;
    let _, _, chunk_size, lhs_size = f_accum_params.(idx) in
    let g_chunk = Array.sub g_values ~pos:lhs_size ~len:chunk_size in
    let lhs_h = Array.sub lines_hashes ~pos:0 ~len:lhs_size in
    let rhs_start = lhs_size + chunk_size in
    let rhs_h =
      Array.sub lines_hashes ~pos:rhs_start ~len:(ate_loop_len - rhs_start)
    in
    let flat_hashes = Array.append lhs_h rhs_h in
    let w : Proof_conversion.Plonk_requests.witness =
      { Proof_conversion.Plonk_requests.empty_witness with
        kzg_acc = Some !current_kzg
      ; g_chunk = Some g_chunk
      ; flat_hashes = Some flat_hashes
      }
    in
    let output_hash, proof, vk =
      Proof_conversion.Plonk_pickles_rules.compile_prove_and_export ~n
        ~input_hash:!current_hash ~witness:w
    in
    let _, kzg_after, _ =
      Proof_conversion.Plonk_pickles_rules.compile_and_prove_zkp_f_accum
        ~circuit_index:n ~input_hash:!current_hash ~witness:w
    in
    base_proofs.(n) <- (!current_hash, output_hash, proof, vk) ;
    current_hash := output_hash ;
    current_kzg := kzg_after
  done ;
  (* zkp23 *)
  Printf.eprintf "  zkp23...\n%!" ;
  let lhs_hashes_23 = Array.sub lines_hashes ~pos:0 ~len:(ate_loop_len - 1) in
  let g_chunk_23 = [| g_values.(ate_loop_len - 1) |] in
  let w23 : Proof_conversion.Plonk_requests.witness =
    { Proof_conversion.Plonk_requests.empty_witness with
      kzg_acc = Some !current_kzg
    ; lhs_hashes = Some lhs_hashes_23
    ; g_chunk = Some g_chunk_23
    }
  in
  let output_hash_23, proof_23, vk_23 =
    Proof_conversion.Plonk_pickles_rules.compile_prove_and_export ~n:23
      ~input_hash:!current_hash ~witness:w23
  in
  base_proofs.(23) <- (!current_hash, output_hash_23, proof_23, vk_23) ;
  Printf.eprintf "All 24 base circuits proved.\n%!" ;
  (* === Tree compression === *)
  Printf.eprintf "Tree compression...\n%!" ;
  let layer1_tag, (module Layer1Proof), layer1_prove = TC.compile_layer1 () in
  ignore (module Layer1Proof : Pickles.Proof_intf) ;
  let _, cout23, _, _ = base_proofs.(23) in
  let padded_proofs =
    Array.init 32 ~f:(fun i ->
        if i < 24 then
          let cin, cout, proof, vk = base_proofs.(i) in
          (cin, cout, proof, vk, true)
        else
          let _, _, proof, vk = base_proofs.(0) in
          (cout23, cout23, proof, vk, false) )
  in
  let layer1_results =
    Array.init 16 ~f:(fun i ->
        let li = i * 2 in
        let ri = (i * 2) + 1 in
        let cin_l, cout_l, proof_l, vk_l, verify_l = padded_proofs.(li) in
        let cin_r, cout_r, proof_r, vk_r, verify_r = padded_proofs.(ri) in
        Printf.eprintf "  Layer1 %d...\n%!" i ;
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
        TC.prove_layer1 ~prover:layer1_prove ~witness )
  in
  let node_tag, (module NodeProof), node_prove = TC.compile_node () in
  ignore (module NodeProof : Pickles.Proof_intf) ;
  let layer1_vk =
    Promise.block_on_async_exn (fun () ->
        Pickles.Side_loaded.Verification_key.of_compiled_promise layer1_tag )
  in
  let current_layer = ref layer1_results in
  let current_vk = ref layer1_vk in
  let layer = ref 2 in
  while Array.length !current_layer > 1 do
    let n = Array.length !current_layer in
    Printf.eprintf "  Node layer %d: %d → %d\n%!" !layer n (n / 2) ;
    let next =
      Array.init (n / 2) ~f:(fun i ->
          let carry_l, proof_l = !current_layer.(i * 2) in
          let carry_r, proof_r = !current_layer.((i * 2) + 1) in
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
          TC.prove_node ~prover:node_prove ~witness )
    in
    let node_vk =
      Promise.block_on_async_exn (fun () ->
          Pickles.Side_loaded.Verification_key.of_compiled_promise node_tag )
    in
    current_layer := next ;
    current_vk := node_vk ;
    incr layer
  done ;
  let final_carry, final_proof = !current_layer.(0) in
  let (final_left_in, final_right_out), final_vk_digest = final_carry in
  Printf.eprintf "Conversion complete.\n%!" ;
  (* === Output === *)
  let module P = Pickles.Proof.Make (Pickles_types.Nat.N2) in
  let proof_base64 = P.to_base64 final_proof in
  let node_vk = !current_vk in
  let node_vk_base64 = Pickles.Side_loaded.Verification_key.to_base64 node_vk in
  (* Compute VK hash matching o1js: Poseidon.hash(pack_input(to_input(vk))) *)
  let vk_hash =
    let input = Pickles.Side_loaded.Verification_key.to_input node_vk in
    let packed = Random_oracle.pack_input input in
    Random_oracle.hash packed
  in
  let vk_hash_str = Kimchi_pasta.Pasta.Fp.to_string vk_hash in
  let output =
    `Assoc
      [ ( "vkData"
        , `Assoc
            [ ("data", `String node_vk_base64); ("hash", `String vk_hash_str) ]
        )
      ; ( "proofData"
        , `Assoc
            [ ("maxProofsVerified", `Int 2)
            ; ("proof", `String proof_base64)
            ; ("publicInput", `List [])
            ; ( "publicOutput"
              , `List
                  [ `String (Step.Field.Constant.to_string final_left_in)
                  ; `String (Step.Field.Constant.to_string final_right_out)
                  ; `String (Step.Field.Constant.to_string final_vk_digest)
                  ] )
            ] )
      ]
  in
  (* Write output — match nori's file naming: strip .json, append .commandName.json *)
  let dir = Filename.dirname input_path in
  let base = Filename.basename input_path in
  let base_no_ext =
    if String.is_suffix ~suffix:".json" (String.lowercase base) then
      String.sub base ~pos:0 ~len:(String.length base - 5)
    else base
  in
  let output_path = Filename.concat dir (base_no_ext ^ ".sp1ToPlonk.json") in
  Yojson.Safe.to_file output_path output ;
  Printf.eprintf "Output written to %s\n%!" output_path

let () =
  match Sys.argv with
  | [| _; "sp1ToPlonk"; input_path |] ->
      run_sp1_to_plonk ~input_path ~aux_path:""
  | [| _; "sp1ToPlonk"; input_path; aux_path |] ->
      run_sp1_to_plonk ~input_path ~aux_path
  | _ ->
      Printf.eprintf
        "Usage: nori-proof-converter sp1ToPlonk <input.json> [aux_witness.json]\n" ;
      Printf.eprintf "\nSupported commands:\n" ;
      Printf.eprintf
        "  sp1ToPlonk    Convert SP1 PLONK proof to Mina-compatible proof\n" ;
      exit 1
