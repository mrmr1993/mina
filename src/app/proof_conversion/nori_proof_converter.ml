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
  (* Detect input format: SP1 (has proof.Plonk) vs fixture (has hexProof) *)
  let json = Yojson.Safe.from_file input_path in
  let is_sp1_format =
    match Yojson.Safe.Util.member "proof" json with
    | `Null ->
        false
    | proof_json -> (
        match Yojson.Safe.Util.member "Plonk" proof_json with
        | `Null ->
            false
        | _ ->
            true )
  in
  let acc_const, aux =
    if is_sp1_format then (
      Printf.eprintf "Detected SP1 format.\n%!" ;
      let acc = Proof_conversion.Plonk_proof_json.load_sp1 input_path in
      let aux =
        let try_path p =
          if String.length p > 0 && Stdlib.Sys.file_exists p then Some p
          else None
        in
        let aux_file =
          match try_path aux_path with
          | Some p ->
              Some p
          | None ->
              (* Try default location next to input *)
              let dir = Filename.dirname input_path in
              try_path (Filename.concat dir "aux_witness.json")
        in
        match aux_file with
        | Some p ->
            Printf.eprintf "Loading aux witness from %s\n%!" p ;
            let aux_json = Yojson.Safe.from_file p in
            Proof_conversion.Plonk_proof_json.parse_aux_witness aux_json
        | None ->
            Printf.eprintf
              "Computing PLONK aux witness natively (circuits 0-12 unchecked + \
               Rust FFI)...\n\
               %!" ;
            let mlo =
              Proof_conversion.Plonk_witness_tracker.compute_kzg_mlo acc
            in
            let w27 = Proof_conversion.Bn254_params.w27 () in
            let groth16_aux =
              Proof_conversion.Pairing_utils_bridge.compute_aux_witness_with_w27
                mlo w27
            in
            { Proof_conversion.Plonk_proof_json.shift_power =
                Step.Field.Constant.of_int groth16_aux.shift_power
            ; c_fp12 = groth16_aux.c
            }
      in
      (acc, aux) )
    else (
      Printf.eprintf "Detected fixture format.\n%!" ;
      Proof_conversion.Plonk_proof_json.load_fixture_with_aux input_path )
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
  let oc = Out_channel.create output_path in
  Yojson.Safe.pretty_to_channel ~std:true oc output ;
  Out_channel.close oc ;
  Printf.eprintf "Output written to %s\n%!" output_path

let run_risc0_to_groth16 ~proof_path ~vk_path =
  Printf.eprintf "=== RISC Zero to Groth16 Proof Conversion ===\n%!" ;
  Printf.eprintf "Proof: %s\n%!" proof_path ;
  Printf.eprintf "VK: %s\n%!" vk_path ;
  let module WT = Proof_conversion.Witness_tracker in
  let proof = Proof_conversion.Proof_json.load_proof proof_path in
  let vk_raw = Proof_conversion.Proof_json.load_vk vk_path in
  (* Enrich VK: compute alpha_beta if missing (raw VK) *)
  let vk =
    let ((g00, _), _, _), _ = vk_raw.alpha_beta in
    if Bignum_bigint.(g00 = zero) then (
      Printf.eprintf "Computing alpha_beta via Rust FFI...\n%!" ;
      let alpha_beta =
        Proof_conversion.Pairing_utils_bridge.make_alpha_beta
          ~alpha_x:vk_raw.alpha.x ~alpha_y:vk_raw.alpha.y
          ~beta_x_c0:(fst vk_raw.beta.x) ~beta_x_c1:(snd vk_raw.beta.x)
          ~beta_y_c0:(fst vk_raw.beta.y) ~beta_y_c1:(snd vk_raw.beta.y)
      in
      { vk_raw with alpha_beta } )
    else vk_raw
  in
  let aux =
    match Sys.getenv_opt "GROTH16_AUX_PATH" with
    | Some p ->
        Printf.eprintf "Loading aux witness from %s\n%!" p ;
        Proof_conversion.Proof_json.load_aux_witness p
    | None ->
        (* Try default path, fall back to native computation *)
        let default_path =
          Filename.concat (Filename.dirname proof_path) "aux_witness.json"
        in
        if Stdlib.Sys.file_exists default_path then (
          Printf.eprintf "Loading aux witness from %s\n%!" default_path ;
          Proof_conversion.Proof_json.load_aux_witness default_path )
        else (
          Printf.eprintf "Computing aux witness natively via Rust FFI...\n%!" ;
          Proof_conversion.Pairing_utils_bridge.groth16_aux_witness ~proof ~vk )
  in
  let tracker = WT.create ~proof ~vk ~aux in
  Proof_conversion.Circuit_config.set_tracker tracker ;
  let vk_const = Proof_conversion.Vk_constants.create vk in
  let b_lines = WT.get_all_b_lines tracker in
  (* Compute initial accumulator *)
  let n_total = Array.length Proof_conversion.Bn254_params.ate_loop_count in
  let initial_acc =
    let acc = WT.get_accumulator_constant tracker in
    let initial_g_digest =
      let zeros = Array.create ~len:n_total Step.Field.Constant.zero in
      Random_oracle.hash zeros
    in
    { acc with
      state =
        { g_digest = initial_g_digest
        ; t_point = acc.proof.b
        ; f =
            ( Proof_conversion.Fp6.Constant.zero
            , Proof_conversion.Fp6.Constant.zero )
        }
    }
  in
  let initial_hash =
    Step.run_and_check_exn (fun () ->
        let acc =
          Step.exists Proof_conversion.Accumulator.typ ~compute:(fun () ->
              initial_acc )
        in
        let h = Proof_conversion.Accumulator.hash acc in
        fun () -> Step.As_prover.read_var h )
  in
  Printf.eprintf "Initial hash: %s\n%!"
    (Step.Field.Constant.to_string initial_hash) ;
  (* === Prove all 16 base circuits === *)
  Printf.eprintf "Proving 16 base circuits...\n%!" ;
  let num_circuits = Proof_conversion.Circuits.num_circuits in
  let current_hash = ref initial_hash in
  let current_acc = ref initial_acc in
  let evolving_line_hashes =
    ref (Array.create ~len:n_total Step.Field.Constant.zero)
  in
  let all_g_values = ref [||] in
  let base_proofs =
    Array.create ~len:num_circuits
      ( Step.Field.Constant.zero
      , Step.Field.Constant.zero
      , (Obj.magic () : Pickles_types.Nat.N0.n Pickles.Proof.t)
      , (Obj.magic () : Pickles.Side_loaded.Verification_key.t) )
  in
  (* Circuits 0-6: ate loop with accumulator chaining *)
  for n = 0 to 6 do
    Printf.eprintf "  zkp%d...\n%!" n ;
    let witness : Proof_conversion.Groth16_requests.witness =
      { Proof_conversion.Groth16_requests.empty_witness with
        accumulator = Some !current_acc
      ; line_hashes = Some !evolving_line_hashes
      ; b_lines =
          Some
            (Array.map b_lines ~f:(fun (l : WT.Line.t) -> (l.lambda, l.neg_mu)))
      }
    in
    let output_hash, acc_after, lh_after, gv_after, proof, side_vk =
      Proof_conversion.Pickles_rules.compile_prove_and_export_with_acc
        ~vk:vk_const ~n ~input_hash:!current_hash ~witness
    in
    base_proofs.(n) <- (!current_hash, output_hash, proof, side_vk) ;
    current_hash := output_hash ;
    current_acc := acc_after ;
    evolving_line_hashes := lh_after ;
    all_g_values := Array.append !all_g_values gv_after
  done ;
  (* Circuits 7-12: f-update with accumulator chaining.
     These don't produce new line_hashes or g_values. *)
  for n = 7 to 12 do
    Printf.eprintf "  zkp%d...\n%!" n ;
    let idx = n - 7 in
    let n_iters =
      Proof_conversion.Fupdate_circuit.iterations_per_circuit.(idx)
    in
    let g_start = Proof_conversion.Fupdate_circuit.g_start_per_circuit.(idx) in
    let all_lh = !evolving_line_hashes in
    let lhs = Array.sub all_lh ~pos:0 ~len:g_start in
    let g_chunk = Array.sub !all_g_values ~pos:g_start ~len:n_iters in
    let rhs_start = g_start + n_iters in
    let rhs =
      Array.sub all_lh ~pos:rhs_start ~len:(Array.length all_lh - rhs_start)
    in
    let witness : Proof_conversion.Groth16_requests.witness =
      { Proof_conversion.Groth16_requests.empty_witness with
        accumulator = Some !current_acc
      ; g_chunk = Some g_chunk
      ; lhs_hashes = Some lhs
      ; rhs_hashes = Some rhs
      }
    in
    (* Use compile_prove_and_export_with_acc for acc + VK, but don't
       update line_hashes or g_values (f-update doesn't change them). *)
    let output_hash, acc_after, _lh, _gv, proof, side_vk =
      Proof_conversion.Pickles_rules.compile_prove_and_export_with_acc
        ~vk:vk_const ~n ~input_hash:!current_hash ~witness
    in
    base_proofs.(n) <- (!current_hash, output_hash, proof, side_vk) ;
    current_hash := output_hash ;
    current_acc := acc_after
  done ;
  (* Circuit 13: final exponentiation *)
  Printf.eprintf "  zkp13...\n%!" ;
  let all_lh = !evolving_line_hashes in
  let lhs_13 = Array.sub all_lh ~pos:0 ~len:(n_total - 1) in
  let witness_13 : Proof_conversion.Groth16_requests.witness =
    { Proof_conversion.Groth16_requests.empty_witness with
      accumulator = Some !current_acc
    ; lhs_hashes = Some lhs_13
    ; final_g = Some !all_g_values.(Array.length !all_g_values - 1)
    }
  in
  let output_hash_13, proof_13, vk_13 =
    Proof_conversion.Pickles_rules.compile_prove_and_export ~vk:vk_const ~n:13
      ~input_hash:!current_hash ~witness:witness_13
  in
  base_proofs.(13) <- (!current_hash, output_hash_13, proof_13, vk_13) ;
  current_hash := output_hash_13 ;
  (* Circuit 14: partial IC *)
  Printf.eprintf "  zkp14...\n%!" ;
  let n_pi = WT.num_public_inputs tracker in
  let pis = Array.init n_pi ~f:(fun i -> WT.get_public_input tracker i) in
  let witness_14 : Proof_conversion.Groth16_requests.witness =
    { Proof_conversion.Groth16_requests.empty_witness with
      public_inputs = Some pis
    }
  in
  let output_hash_14, proof_14, vk_14 =
    Proof_conversion.Pickles_rules.compile_prove_and_export ~vk:vk_const ~n:14
      ~input_hash:!current_hash ~witness:witness_14
  in
  base_proofs.(14) <- (!current_hash, output_hash_14, proof_14, vk_14) ;
  current_hash := output_hash_14 ;
  (* Circuit 15: full IC *)
  Printf.eprintf "  zkp15...\n%!" ;
  let pis_15 = Array.init n_pi ~f:(fun i -> WT.get_public_input tracker i) in
  let pi = WT.get_pi tracker in
  let partial_acc = WT.get_partial_ic_acc tracker in
  let g1_to_const (p : WT.G1.t) : Proof_conversion.G1.Constant.t =
    { x = p.x; y = p.y }
  in
  let witness_15 : Proof_conversion.Groth16_requests.witness =
    { Proof_conversion.Groth16_requests.empty_witness with
      public_inputs = Some pis_15
    ; pi_point = Some (g1_to_const pi)
    ; partial_ic_acc = Some (g1_to_const partial_acc)
    }
  in
  let output_hash_15, proof_15, vk_15 =
    Proof_conversion.Pickles_rules.compile_prove_and_export ~vk:vk_const ~n:15
      ~input_hash:!current_hash ~witness:witness_15
  in
  base_proofs.(15) <- (!current_hash, output_hash_15, proof_15, vk_15) ;
  Printf.eprintf "All 16 base circuits proved.\n%!" ;
  (* === Tree compression === *)
  Printf.eprintf "Tree compression...\n%!" ;
  let layer1_tag, (module Layer1Proof), layer1_prove = TC.compile_layer1 () in
  ignore (module Layer1Proof : Pickles.Proof_intf) ;
  (* 16 = 2^4, so we need 8 layer1 + 4 node-layer2 + 2 node-layer3 + 1 node-layer4 *)
  let layer1_results =
    Array.init 8 ~f:(fun i ->
        let li = i * 2 in
        let ri = (i * 2) + 1 in
        let cin_l, cout_l, proof_l, vk_l = base_proofs.(li) in
        let cin_r, cout_r, proof_r, vk_r = base_proofs.(ri) in
        Printf.eprintf "  Layer1 %d (zkp%d + zkp%d)...\n%!" i li ri ;
        let witness : TC.layer1_witness =
          { proof_left = Pickles.Side_loaded.Proof.of_proof proof_l
          ; vk_left = vk_l
          ; verify_left = true
          ; proof_right = Pickles.Side_loaded.Proof.of_proof proof_r
          ; vk_right = vk_r
          ; verify_right = true
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
    Printf.eprintf "  Node layer %d: %d -> %d\n%!" !layer n (n / 2) ;
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
  let dir = Filename.dirname proof_path in
  let base = Filename.basename proof_path in
  let base_no_ext =
    if String.is_suffix ~suffix:".json" (String.lowercase base) then
      String.sub base ~pos:0 ~len:(String.length base - 5)
    else base
  in
  let output_path =
    Filename.concat dir (base_no_ext ^ ".risc0ToGroth16.json")
  in
  let oc = Out_channel.create output_path in
  Yojson.Safe.pretty_to_channel ~std:true oc output ;
  Out_channel.close oc ;
  Printf.eprintf "Output written to %s\n%!" output_path

(* ==== Internal stage commands ==== *)

module W = Proof_conversion.Workdir

(** Initialize a working directory for staged execution. *)
let run_internal_init_workdir ~workdir ~system ~input_path ~vk_path =
  Printf.eprintf "Initializing workdir: %s (%s)\n%!" workdir system ;
  ( match system with
  | "plonk" ->
      W.init ~workdir ~system:(W.Plonk { base_count = 24 }) ;
      (* Copy input file *)
      let data = In_channel.read_all input_path in
      Out_channel.write_all (Filename.concat workdir "input.json") ~data
  | "groth16" ->
      W.init ~workdir ~system:(W.Groth16 { base_count = 16 }) ;
      let proof_data = In_channel.read_all input_path in
      Out_channel.write_all
        (Filename.concat workdir "proof.json")
        ~data:proof_data ;
      let vk_p = Option.value_exn vk_path in
      let vk_data = In_channel.read_all vk_p in
      Out_channel.write_all (Filename.concat workdir "vk.json") ~data:vk_data
  | s ->
      failwith (sprintf "Unknown system: %s" s) ) ;
  Printf.eprintf "Workdir initialized.\n%!"

(** Generate witness: compute aux witness and write initial state. *)
let run_internal_generate_witness ~workdir =
  Printf.eprintf "Generating witness in %s\n%!" workdir ;
  let system = W.detect_system ~workdir in
  ( match system with
  | W.Plonk _ ->
      let input_path = Filename.concat workdir "input.json" in
      let json = Yojson.Safe.from_file input_path in
      let is_sp1 =
        match Yojson.Safe.Util.member "proof" json with
        | `Null ->
            false
        | pj -> (
            match Yojson.Safe.Util.member "Plonk" pj with
            | `Null ->
                false
            | _ ->
                true )
      in
      let acc_const, aux =
        if is_sp1 then
          let acc = Proof_conversion.Plonk_proof_json.load_sp1 input_path in
          let aux_file = Filename.concat workdir "aux_witness.json" in
          let aux =
            if Stdlib.Sys.file_exists aux_file then
              let aj = Yojson.Safe.from_file aux_file in
              Proof_conversion.Plonk_proof_json.parse_aux_witness aj
            else
              let mlo =
                Proof_conversion.Plonk_witness_tracker.compute_kzg_mlo acc
              in
              let w27 = Proof_conversion.Bn254_params.w27 () in
              let g_aux =
                Proof_conversion.Pairing_utils_bridge
                .compute_aux_witness_with_w27 mlo w27
              in
              { Proof_conversion.Plonk_proof_json.shift_power =
                  Step.Field.Constant.of_int g_aux.shift_power
              ; c_fp12 = g_aux.c
              }
          in
          (acc, aux)
        else Proof_conversion.Plonk_proof_json.load_fixture_with_aux input_path
      in
      (* Write aux witness *)
      let aux_json =
        `Assoc
          [ ( "shift_power"
            , `String (Step.Field.Constant.to_string aux.shift_power) )
          ; ("c", Proof_conversion.Proof_json.fp12_to_json aux.c_fp12)
          ]
      in
      Yojson.Safe.to_file (Filename.concat workdir "aux_witness.json") aux_json ;
      (* Write initial state *)
      let initial_hash =
        Proof_conversion.Plonk_witness_tracker.hash_accumulator_const acc_const
      in
      W.write_hash ~workdir ~n:(-1) ~hash:initial_hash ;
      W.write_plonk_state ~workdir ~n:(-1) ~acc:acc_const
  | W.Groth16 _ ->
      let proof_path = Filename.concat workdir "proof.json" in
      let vk_path = Filename.concat workdir "vk.json" in
      let proof = Proof_conversion.Proof_json.load_proof proof_path in
      let vk = Proof_conversion.Proof_json.load_vk vk_path in
      let aux =
        Proof_conversion.Pairing_utils_bridge.groth16_aux_witness ~proof ~vk
      in
      (* Write aux witness in nori-compatible format *)
      Proof_conversion.Proof_json.save_aux_witness
        (Filename.concat workdir "aux_witness.json")
        aux ;
      (* Set up tracker and initial accumulator *)
      let module WT = Proof_conversion.Witness_tracker in
      let tracker = WT.create ~proof ~vk ~aux in
      Proof_conversion.Circuit_config.set_tracker tracker ;
      let n_total = Array.length Proof_conversion.Bn254_params.ate_loop_count in
      let initial_acc =
        let acc = WT.get_accumulator_constant tracker in
        let initial_g_digest =
          let zeros = Array.create ~len:n_total Step.Field.Constant.zero in
          Random_oracle.hash zeros
        in
        { acc with
          state =
            { g_digest = initial_g_digest
            ; t_point = acc.proof.b
            ; f =
                ( Proof_conversion.Fp6.Constant.zero
                , Proof_conversion.Fp6.Constant.zero )
            }
        }
      in
      let initial_hash =
        Step.run_and_check_exn (fun () ->
            let acc =
              Step.exists Proof_conversion.Accumulator.typ ~compute:(fun () ->
                  initial_acc )
            in
            let h = Proof_conversion.Accumulator.hash acc in
            fun () -> Step.As_prover.read_var h )
      in
      W.write_hash ~workdir ~n:(-1) ~hash:initial_hash ;
      let line_hashes = Array.create ~len:n_total Step.Field.Constant.zero in
      W.write_groth16_state ~workdir ~n:(-1) ~acc:initial_acc ~line_hashes
        ~g_values:[||] ) ;
  Printf.eprintf "Witness generated.\n%!"

(** Compute the intermediate state for a single circuit via run_unchecked.
    Reads state n-1 from disk, runs the circuit body without constraint
    checking, and writes state n.  This enables pipelining: prove-zkp N
    can start as soon as compute-state N finishes, while compute-state N+1
    runs in parallel. *)
let run_internal_compute_state ~workdir ~n =
  Printf.eprintf "Computing state for circuit %d in %s\n%!" n workdir ;
  let system = W.detect_system ~workdir in
  Snarky_backendless.Snark0.set_eval_constraints false ;
  ( match system with
  | W.Plonk _ ->
      let ate_loop_len = Proof_conversion.Kzg_accumulator.ate_loop_len in
      if n <= 11 then (
        (* Circuits 0-11: evolve Plonk_accumulator *)
        let cur_hash = W.read_hash ~workdir ~n:(n - 1) in
        let cur_acc = W.read_plonk_state ~workdir ~n:(n - 1) in
        let zkp_fns =
          Proof_conversion.Plonk_circuits.
            [| zkp0
             ; zkp1
             ; zkp2
             ; zkp3
             ; zkp4
             ; zkp5
             ; zkp6
             ; zkp7
             ; zkp8
             ; zkp9
             ; zkp10
             ; zkp11
            |]
        in
        let witness : Proof_conversion.Plonk_requests.witness =
          { Proof_conversion.Plonk_requests.empty_witness with
            plonk_acc = Some cur_acc
          }
        in
        let handler = Proof_conversion.Plonk_requests.handler witness in
        let result = ref (Step.Field.Constant.zero, cur_acc) in
        Step.run_unchecked (fun () ->
            Step.handle
              (fun () ->
                let input_var = Step.Field.constant cur_hash in
                let output_hash, acc = zkp_fns.(n) input_var in
                Step.as_prover (fun () ->
                    let oh = Step.As_prover.read_var output_hash in
                    let ac =
                      Step.As_prover.read Proof_conversion.Plonk_accumulator.typ
                        acc
                    in
                    result := (oh, ac) ) )
              handler ) ;
        let oh, ac = !result in
        W.write_hash ~workdir ~n ~hash:oh ;
        W.write_plonk_state ~workdir ~n ~acc:ac )
      else if n = 12 then (
        (* Circuit 12: transition Plonk_accumulator → Kzg_accumulator *)
        let cur_hash = W.read_hash ~workdir ~n:11 in
        let cur_acc = W.read_plonk_state ~workdir ~n:11 in
        let aux_path = Filename.concat workdir "aux_witness.json" in
        let aux_json = Yojson.Safe.from_file aux_path in
        let shift_power =
          Step.Field.Constant.of_string
            Yojson.Safe.Util.(member "shift_power" aux_json |> to_string)
        in
        let c_fp12 =
          Proof_conversion.Proof_json.fp12_of_json
            (Yojson.Safe.Util.member "c" aux_json)
        in
        let w12 : Proof_conversion.Plonk_requests.witness =
          { Proof_conversion.Plonk_requests.empty_witness with
            plonk_acc = Some cur_acc
          ; shift_power = Some shift_power
          ; c_fp12 = Some c_fp12
          }
        in
        let handler12 = Proof_conversion.Plonk_requests.handler w12 in
        let result12 =
          ref
            ( Step.Field.Constant.zero
            , (Obj.magic () : Proof_conversion.Kzg_accumulator.t_const) )
        in
        Step.run_unchecked (fun () ->
            Step.handle
              (fun () ->
                let input_var = Step.Field.constant cur_hash in
                let output_hash, kzg =
                  Proof_conversion.Plonk_circuits.zkp12 input_var
                in
                Step.as_prover (fun () ->
                    let oh = Step.As_prover.read_var output_hash in
                    let kc =
                      Step.As_prover.read Proof_conversion.Kzg_accumulator.typ
                        kzg
                    in
                    result12 := (oh, kc) ) )
              handler12 ) ;
        let oh12, kzg12 = !result12 in
        W.write_hash ~workdir ~n:12 ~hash:oh12 ;
        W.write_plonk_kzg_state ~workdir ~n:12 ~kzg:kzg12
          ~lines_hashes:(Array.create ~len:ate_loop_len Step.Field.Constant.zero)
          ~g_values:[||] )
      else if n <= 16 then (
        (* Circuits 13-16: KZG line circuits *)
        let cur_hash = W.read_hash ~workdir ~n:(n - 1) in
        let cur_kzg, cur_kzg_lh, cur_kzg_gv =
          W.read_plonk_kzg_state ~workdir ~n:(n - 1)
        in
        let w : Proof_conversion.Plonk_requests.witness =
          { Proof_conversion.Plonk_requests.empty_witness with
            kzg_acc = Some cur_kzg
          ; lines_hashes = Some cur_kzg_lh
          }
        in
        let handler = Proof_conversion.Plonk_requests.handler w in
        let result_hash = ref cur_hash in
        let result_kzg = ref cur_kzg in
        let result_lh = ref cur_kzg_lh in
        let result_gv = ref [||] in
        Step.run_unchecked (fun () ->
            Step.handle
              (fun () ->
                let input_var = Step.Field.constant cur_hash in
                let output_hash, kzg_var, lh_var, gv_arr =
                  Proof_conversion.Plonk_circuits.zkp_lines ~circuit_index:n
                    input_var
                in
                Step.as_prover (fun () ->
                    result_hash := Step.As_prover.read_var output_hash ;
                    result_kzg :=
                      Step.As_prover.read Proof_conversion.Kzg_accumulator.typ
                        kzg_var ;
                    result_lh :=
                      Step.As_prover.read
                        (Step.Typ.array ~length:ate_loop_len Step.Field.typ)
                        lh_var ;
                    result_gv :=
                      Array.map gv_arr ~f:(fun g ->
                          Step.As_prover.read Proof_conversion.Fp12.typ g ) ) )
              handler ) ;
        W.write_hash ~workdir ~n ~hash:!result_hash ;
        W.write_plonk_kzg_state ~workdir ~n ~kzg:!result_kzg
          ~lines_hashes:!result_lh
          ~g_values:(Array.append cur_kzg_gv !result_gv) )
      else if n <= 22 then (
        (* Circuits 17-22: f-accumulation.
           g_values and lines_hashes are a snapshot from state 16;
           only kzg evolves. *)
        let cur_hash = W.read_hash ~workdir ~n:(n - 1) in
        let cur_kzg, _lh_prev, _gv_prev =
          W.read_plonk_kzg_state ~workdir ~n:(n - 1)
        in
        (* Read the g_values/lines_hashes snapshot from state 16 *)
        let _kzg16, lines_hashes_snapshot, g_values_snapshot =
          W.read_plonk_kzg_state ~workdir ~n:16
        in
        let f_accum_params =
          [| (1, 10, 9, 0)
           ; (10, 21, 11, 9)
           ; (21, 32, 11, 20)
           ; (32, 43, 11, 31)
           ; (43, 54, 11, 42)
           ; (54, 65, 11, 53)
          |]
        in
        let idx = n - 17 in
        let _, _, chunk_size, lhs_size = f_accum_params.(idx) in
        let g_chunk =
          Array.sub g_values_snapshot ~pos:lhs_size ~len:chunk_size
        in
        let lhs_h = Array.sub lines_hashes_snapshot ~pos:0 ~len:lhs_size in
        let rhs_start = lhs_size + chunk_size in
        let rhs_h =
          Array.sub lines_hashes_snapshot ~pos:rhs_start
            ~len:(ate_loop_len - rhs_start)
        in
        let w : Proof_conversion.Plonk_requests.witness =
          { Proof_conversion.Plonk_requests.empty_witness with
            kzg_acc = Some cur_kzg
          ; g_chunk = Some g_chunk
          ; flat_hashes = Some (Array.append lhs_h rhs_h)
          }
        in
        let handler = Proof_conversion.Plonk_requests.handler w in
        let result_hash = ref cur_hash in
        let result_kzg = ref cur_kzg in
        Step.run_unchecked (fun () ->
            Step.handle
              (fun () ->
                let input_var = Step.Field.constant cur_hash in
                let output_hash, kzg_var =
                  Proof_conversion.Plonk_circuits.zkp_f_accum ~circuit_index:n
                    input_var
                in
                Step.as_prover (fun () ->
                    result_hash := Step.As_prover.read_var output_hash ;
                    result_kzg :=
                      Step.As_prover.read Proof_conversion.Kzg_accumulator.typ
                        kzg_var ) )
              handler ) ;
        W.write_hash ~workdir ~n ~hash:!result_hash ;
        W.write_plonk_kzg_state ~workdir ~n ~kzg:!result_kzg
          ~lines_hashes:lines_hashes_snapshot ~g_values:g_values_snapshot )
      else (
        (* Circuit 23: final exponentiation *)
        assert (n = 23) ;
        let cur_hash = W.read_hash ~workdir ~n:22 in
        let cur_kzg, _lh_prev, _gv_prev =
          W.read_plonk_kzg_state ~workdir ~n:22
        in
        let _kzg16, lines_hashes_snapshot, g_values_snapshot =
          W.read_plonk_kzg_state ~workdir ~n:16
        in
        let lhs_hashes_23 =
          Array.sub lines_hashes_snapshot ~pos:0 ~len:(ate_loop_len - 1)
        in
        let g_chunk_23 = [| g_values_snapshot.(ate_loop_len - 1) |] in
        let w23 : Proof_conversion.Plonk_requests.witness =
          { Proof_conversion.Plonk_requests.empty_witness with
            kzg_acc = Some cur_kzg
          ; lhs_hashes = Some lhs_hashes_23
          ; g_chunk = Some g_chunk_23
          }
        in
        let handler23 = Proof_conversion.Plonk_requests.handler w23 in
        let result_hash23 = ref cur_hash in
        Step.run_unchecked (fun () ->
            Step.handle
              (fun () ->
                let input_var = Step.Field.constant cur_hash in
                let output_hash =
                  Proof_conversion.Plonk_circuits.zkp23 input_var
                in
                Step.as_prover (fun () ->
                    result_hash23 := Step.As_prover.read_var output_hash ) )
              handler23 ) ;
        W.write_hash ~workdir ~n:23 ~hash:!result_hash23 ;
        W.write_plonk_kzg_state ~workdir ~n:23 ~kzg:cur_kzg
          ~lines_hashes:lines_hashes_snapshot ~g_values:g_values_snapshot )
  | W.Groth16 _ ->
      let proof_path = Filename.concat workdir "proof.json" in
      let vk_path = Filename.concat workdir "vk.json" in
      let proof = Proof_conversion.Proof_json.load_proof proof_path in
      let vk = Proof_conversion.Proof_json.load_vk vk_path in
      let vk_const = Proof_conversion.Vk_constants.create vk in
      let aux =
        Proof_conversion.Proof_json.load_aux_witness
          (Filename.concat workdir "aux_witness.json")
      in
      let module WT = Proof_conversion.Witness_tracker in
      let tracker = WT.create ~proof ~vk ~aux in
      Proof_conversion.Circuit_config.set_tracker tracker ;
      let n_total = Array.length Proof_conversion.Bn254_params.ate_loop_count in
      let b_lines = WT.get_all_b_lines tracker in
      let cur_hash = W.read_hash ~workdir ~n:(n - 1) in
      let cur_acc, cur_lh, cur_gv =
        W.read_groth16_state ~workdir ~n:(n - 1)
      in
      let witness : Proof_conversion.Groth16_requests.witness =
        if n <= 6 then
          { Proof_conversion.Groth16_requests.empty_witness with
            accumulator = Some cur_acc
          ; line_hashes = Some cur_lh
          ; b_lines =
              Some
                (Array.map b_lines ~f:(fun (l : WT.Line.t) ->
                     (l.lambda, l.neg_mu) ) )
          }
        else if n <= 12 then
          let idx = n - 7 in
          let n_iters =
            Proof_conversion.Fupdate_circuit.iterations_per_circuit.(idx)
          in
          let g_start =
            Proof_conversion.Fupdate_circuit.g_start_per_circuit.(idx)
          in
          let lhs = Array.sub cur_lh ~pos:0 ~len:g_start in
          let g_chunk = Array.sub cur_gv ~pos:g_start ~len:n_iters in
          let rhs_start = g_start + n_iters in
          let rhs =
            Array.sub cur_lh ~pos:rhs_start
              ~len:(Array.length cur_lh - rhs_start)
          in
          { Proof_conversion.Groth16_requests.empty_witness with
            accumulator = Some cur_acc
          ; g_chunk = Some g_chunk
          ; lhs_hashes = Some lhs
          ; rhs_hashes = Some rhs
          }
        else if n = 13 then
          { Proof_conversion.Groth16_requests.empty_witness with
            accumulator = Some cur_acc
          ; lhs_hashes = Some (Array.sub cur_lh ~pos:0 ~len:(n_total - 1))
          ; final_g = Some cur_gv.(Array.length cur_gv - 1)
          }
        else if n = 14 then
          let n_pi = WT.num_public_inputs tracker in
          { Proof_conversion.Groth16_requests.empty_witness with
            public_inputs =
              Some
                (Array.init n_pi ~f:(fun i -> WT.get_public_input tracker i))
          }
        else
          let n_pi = WT.num_public_inputs tracker in
          let pi = WT.get_pi tracker in
          let pa = WT.get_partial_ic_acc tracker in
          let g1c (p : WT.G1.t) : Proof_conversion.G1.Constant.t =
            { x = p.x; y = p.y }
          in
          { Proof_conversion.Groth16_requests.empty_witness with
            public_inputs =
              Some
                (Array.init n_pi ~f:(fun i -> WT.get_public_input tracker i))
          ; pi_point = Some (g1c pi)
          ; partial_ic_acc = Some (g1c pa)
          }
      in
      let handler = Proof_conversion.Groth16_requests.handler witness in
      let result_hash = ref cur_hash in
      let result_acc = ref cur_acc in
      let result_lh = ref cur_lh in
      let result_gv = ref cur_gv in
      ( if n <= 12 then (
        let body =
          Proof_conversion.Circuits.build_circuit_body_with_acc ~vk:vk_const
            ~circuit_index:n
        in
        let res_gv = ref [||] in
        Step.run_unchecked (fun () ->
            Step.handle
              (fun () ->
                let input_var = Step.Field.constant cur_hash in
                let output_hash, (acc_var, lh_var, gv_arr) = body input_var in
                Step.as_prover (fun () ->
                    result_hash := Step.As_prover.read_var output_hash ;
                    result_acc :=
                      Step.As_prover.read Proof_conversion.Accumulator.typ
                        acc_var ;
                    result_lh :=
                      Step.As_prover.read
                        (Step.Typ.array ~length:n_total Step.Field.typ)
                        lh_var ;
                    res_gv :=
                      Array.map gv_arr ~f:(fun g ->
                          Step.As_prover.read Proof_conversion.Fp12.typ g ) ) )
              handler ) ;
        if n <= 6 then (
          result_lh := !result_lh ;
          result_gv := Array.append cur_gv !res_gv )
        else result_gv := cur_gv )
      else
        let body =
          Proof_conversion.Circuits.build_circuit_body ~vk:vk_const
            ~circuit_index:n
        in
        Step.run_unchecked (fun () ->
            Step.handle
              (fun () ->
                let input_var = Step.Field.constant cur_hash in
                let output_hash = body input_var in
                Step.as_prover (fun () ->
                    result_hash := Step.As_prover.read_var output_hash ) )
              handler ) ) ;
      W.write_hash ~workdir ~n ~hash:!result_hash ;
      W.write_groth16_state ~workdir ~n ~acc:!result_acc
        ~line_hashes:!result_lh ~g_values:!result_gv ) ;
  Snarky_backendless.Snark0.set_eval_constraints true ;
  Printf.eprintf "State for circuit %d computed.\n%!" n

(** Prove a single base circuit. *)
let run_internal_prove_zkp ~workdir ~n =
  Printf.eprintf "Proving zkp%d in %s\n%!" n workdir ;
  let system = W.detect_system ~workdir in
  let prev = n - 1 in
  let input_hash = W.read_hash ~workdir ~n:prev in
  ( match system with
  | W.Plonk _ ->
      let module P = Pickles.Proof.Make (Pickles_types.Nat.N0) in
      let write_base_proof ~proof_out ~side_vk =
        W.write_proof_file
          ~path:(W.proof_path workdir ~layer:0 ~index:n)
          ~proof_base64:(P.to_base64 proof_out) ~max_proofs_verified:0 ;
        let vk_b64 = Pickles.Side_loaded.Verification_key.to_base64 side_vk in
        let vk_hash =
          let input = Pickles.Side_loaded.Verification_key.to_input side_vk in
          let packed = Random_oracle.pack_input input in
          Kimchi_pasta.Pasta.Fp.to_string (Random_oracle.hash packed)
        in
        W.write_vk_file
          ~path:(W.vk_path workdir ~layer:0 ~index:n)
          ~vk_base64:vk_b64 ~vk_hash
      in
      let aux_path = Filename.concat workdir "aux_witness.json" in
      let ate_loop_len = Proof_conversion.Kzg_accumulator.ate_loop_len in
      if n <= 11 then (
        (* PLONK verification circuits 0-11: Plonk_accumulator.
           State was already pre-computed by generate-witness; only need
           to compile, prove, and export the proof + VK. *)
        let acc = W.read_plonk_state ~workdir ~n:prev in
        let w : Proof_conversion.Plonk_requests.witness =
          { Proof_conversion.Plonk_requests.empty_witness with
            plonk_acc = Some acc
          }
        in
        let output_hash, proof_out, side_vk =
          Proof_conversion.Plonk_pickles_rules.compile_prove_and_export ~n
            ~input_hash ~witness:w
        in
        write_base_proof ~proof_out ~side_vk ;
        W.write_hash ~workdir ~n ~hash:output_hash )
      else if n = 12 then (
        (* Circuit 12: transition Plonk_accumulator → Kzg_accumulator *)
        let acc = W.read_plonk_state ~workdir ~n:prev in
        let aux_json = Yojson.Safe.from_file aux_path in
        let shift_power =
          Step.Field.Constant.of_string
            Yojson.Safe.Util.(member "shift_power" aux_json |> to_string)
        in
        let c_fp12 =
          Proof_conversion.Proof_json.fp12_of_json
            (Yojson.Safe.Util.member "c" aux_json)
        in
        let w : Proof_conversion.Plonk_requests.witness =
          { Proof_conversion.Plonk_requests.empty_witness with
            plonk_acc = Some acc
          ; shift_power = Some shift_power
          ; c_fp12 = Some c_fp12
          }
        in
        let output_hash, proof_out, side_vk =
          Proof_conversion.Plonk_pickles_rules.compile_prove_and_export ~n:12
            ~input_hash ~witness:w
        in
        (* KZG state was already pre-computed by generate-witness. *)
        write_base_proof ~proof_out ~side_vk ;
        W.write_hash ~workdir ~n ~hash:output_hash )
      else if n <= 16 then (
        (* Circuits 13-16: KZG line circuits.
           KZG state was already pre-computed by generate-witness. *)
        let kzg, lines_hashes, _g_values_prev =
          W.read_plonk_kzg_state ~workdir ~n:prev
        in
        let w : Proof_conversion.Plonk_requests.witness =
          { Proof_conversion.Plonk_requests.empty_witness with
            kzg_acc = Some kzg
          ; lines_hashes = Some lines_hashes
          }
        in
        let output_hash, proof_out, side_vk =
          Proof_conversion.Plonk_pickles_rules.compile_prove_and_export ~n
            ~input_hash ~witness:w
        in
        write_base_proof ~proof_out ~side_vk ;
        W.write_hash ~workdir ~n ~hash:output_hash )
      else if n <= 22 then (
        (* Circuits 17-22: f-accumulation.
           KZG state was already pre-computed by generate-witness. *)
        let kzg, lines_hashes, g_values =
          W.read_plonk_kzg_state ~workdir ~n:prev
        in
        let f_accum_params =
          [| (1, 10, 9, 0)
           ; (10, 21, 11, 9)
           ; (21, 32, 11, 20)
           ; (32, 43, 11, 31)
           ; (43, 54, 11, 42)
           ; (54, 65, 11, 53)
          |]
        in
        let idx = n - 17 in
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
            kzg_acc = Some kzg
          ; g_chunk = Some g_chunk
          ; flat_hashes = Some flat_hashes
          }
        in
        let output_hash, proof_out, side_vk =
          Proof_conversion.Plonk_pickles_rules.compile_prove_and_export ~n
            ~input_hash ~witness:w
        in
        write_base_proof ~proof_out ~side_vk ;
        W.write_hash ~workdir ~n ~hash:output_hash )
      else (
        (* Circuit 23: final exponentiation *)
        assert (n = 23) ;
        let kzg, lines_hashes, g_values =
          W.read_plonk_kzg_state ~workdir ~n:prev
        in
        let lhs_hashes =
          Array.sub lines_hashes ~pos:0 ~len:(ate_loop_len - 1)
        in
        let g_chunk = [| g_values.(ate_loop_len - 1) |] in
        let w : Proof_conversion.Plonk_requests.witness =
          { Proof_conversion.Plonk_requests.empty_witness with
            kzg_acc = Some kzg
          ; lhs_hashes = Some lhs_hashes
          ; g_chunk = Some g_chunk
          }
        in
        let output_hash, proof_out, side_vk =
          Proof_conversion.Plonk_pickles_rules.compile_prove_and_export ~n:23
            ~input_hash ~witness:w
        in
        write_base_proof ~proof_out ~side_vk ;
        W.write_hash ~workdir ~n ~hash:output_hash ;
        (* Write final KZG state unchanged for collect-output *)
        W.write_plonk_kzg_state ~workdir ~n ~kzg ~lines_hashes ~g_values )
  | W.Groth16 _ ->
      let vk_path = Filename.concat workdir "vk.json" in
      let vk = Proof_conversion.Proof_json.load_vk vk_path in
      let vk_const = Proof_conversion.Vk_constants.create vk in
      let proof_path = Filename.concat workdir "proof.json" in
      let proof = Proof_conversion.Proof_json.load_proof proof_path in
      let aux =
        Proof_conversion.Proof_json.load_aux_witness
          (Filename.concat workdir "aux_witness.json")
      in
      let module WT = Proof_conversion.Witness_tracker in
      let tracker = WT.create ~proof ~vk ~aux in
      Proof_conversion.Circuit_config.set_tracker tracker ;
      let acc, line_hashes, g_values = W.read_groth16_state ~workdir ~n:prev in
      let b_lines = WT.get_all_b_lines tracker in
      if n <= 6 then (
        (* Ate loop circuit *)
        let witness : Proof_conversion.Groth16_requests.witness =
          { Proof_conversion.Groth16_requests.empty_witness with
            accumulator = Some acc
          ; line_hashes = Some line_hashes
          ; b_lines =
              Some
                (Array.map b_lines ~f:(fun (l : WT.Line.t) ->
                     (l.lambda, l.neg_mu) ) )
          }
        in
        let output_hash, acc_after, lh_after, gv_after, proof_out, side_vk =
          Proof_conversion.Pickles_rules.compile_prove_and_export_with_acc
            ~vk:vk_const ~n ~input_hash ~witness
        in
        let module P = Pickles.Proof.Make (Pickles_types.Nat.N0) in
        W.write_proof_file
          ~path:(W.proof_path workdir ~layer:0 ~index:n)
          ~proof_base64:(P.to_base64 proof_out) ~max_proofs_verified:0 ;
        let vk_b64 = Pickles.Side_loaded.Verification_key.to_base64 side_vk in
        let vk_hash =
          let input = Pickles.Side_loaded.Verification_key.to_input side_vk in
          let packed = Random_oracle.pack_input input in
          Kimchi_pasta.Pasta.Fp.to_string (Random_oracle.hash packed)
        in
        W.write_vk_file
          ~path:(W.vk_path workdir ~layer:0 ~index:n)
          ~vk_base64:vk_b64 ~vk_hash ;
        W.write_hash ~workdir ~n ~hash:output_hash ;
        let new_g_values = Array.append g_values gv_after in
        W.write_groth16_state ~workdir ~n ~acc:acc_after ~line_hashes:lh_after
          ~g_values:new_g_values )
      else if n <= 12 then (
        (* F-update circuit *)
        let idx = n - 7 in
        let n_iters =
          Proof_conversion.Fupdate_circuit.iterations_per_circuit.(idx)
        in
        let g_start =
          Proof_conversion.Fupdate_circuit.g_start_per_circuit.(idx)
        in
        let all_lh = line_hashes in
        let lhs = Array.sub all_lh ~pos:0 ~len:g_start in
        let g_chunk = Array.sub g_values ~pos:g_start ~len:n_iters in
        let rhs_start = g_start + n_iters in
        let rhs =
          Array.sub all_lh ~pos:rhs_start ~len:(Array.length all_lh - rhs_start)
        in
        let witness : Proof_conversion.Groth16_requests.witness =
          { Proof_conversion.Groth16_requests.empty_witness with
            accumulator = Some acc
          ; g_chunk = Some g_chunk
          ; lhs_hashes = Some lhs
          ; rhs_hashes = Some rhs
          }
        in
        let output_hash, acc_after, _lh, _gv, proof_out, side_vk =
          Proof_conversion.Pickles_rules.compile_prove_and_export_with_acc
            ~vk:vk_const ~n ~input_hash ~witness
        in
        let module P = Pickles.Proof.Make (Pickles_types.Nat.N0) in
        W.write_proof_file
          ~path:(W.proof_path workdir ~layer:0 ~index:n)
          ~proof_base64:(P.to_base64 proof_out) ~max_proofs_verified:0 ;
        let vk_b64 = Pickles.Side_loaded.Verification_key.to_base64 side_vk in
        let vk_hash =
          let input = Pickles.Side_loaded.Verification_key.to_input side_vk in
          let packed = Random_oracle.pack_input input in
          Kimchi_pasta.Pasta.Fp.to_string (Random_oracle.hash packed)
        in
        W.write_vk_file
          ~path:(W.vk_path workdir ~layer:0 ~index:n)
          ~vk_base64:vk_b64 ~vk_hash ;
        W.write_hash ~workdir ~n ~hash:output_hash ;
        W.write_groth16_state ~workdir ~n ~acc:acc_after ~line_hashes ~g_values
        )
      else
        (* Circuits 13-15 *)
        let n_total =
          Array.length Proof_conversion.Bn254_params.ate_loop_count
        in
        let witness : Proof_conversion.Groth16_requests.witness =
          match n with
          | 13 ->
              let lhs_13 = Array.sub line_hashes ~pos:0 ~len:(n_total - 1) in
              { Proof_conversion.Groth16_requests.empty_witness with
                accumulator = Some acc
              ; lhs_hashes = Some lhs_13
              ; final_g = Some g_values.(Array.length g_values - 1)
              }
          | 14 ->
              let n_pi = WT.num_public_inputs tracker in
              let pis =
                Array.init n_pi ~f:(fun i -> WT.get_public_input tracker i)
              in
              { Proof_conversion.Groth16_requests.empty_witness with
                public_inputs = Some pis
              }
          | 15 ->
              let n_pi = WT.num_public_inputs tracker in
              let pis =
                Array.init n_pi ~f:(fun i -> WT.get_public_input tracker i)
              in
              let pi = WT.get_pi tracker in
              let partial_acc = WT.get_partial_ic_acc tracker in
              let g1c (p : WT.G1.t) : Proof_conversion.G1.Constant.t =
                { x = p.x; y = p.y }
              in
              { Proof_conversion.Groth16_requests.empty_witness with
                public_inputs = Some pis
              ; pi_point = Some (g1c pi)
              ; partial_ic_acc = Some (g1c partial_acc)
              }
          | _ ->
              Proof_conversion.Groth16_requests.empty_witness
        in
        let output_hash, proof_out, side_vk =
          Proof_conversion.Pickles_rules.compile_prove_and_export ~vk:vk_const
            ~n ~input_hash ~witness
        in
        let module P = Pickles.Proof.Make (Pickles_types.Nat.N0) in
        W.write_proof_file
          ~path:(W.proof_path workdir ~layer:0 ~index:n)
          ~proof_base64:(P.to_base64 proof_out) ~max_proofs_verified:0 ;
        let vk_b64 = Pickles.Side_loaded.Verification_key.to_base64 side_vk in
        let vk_hash =
          let input = Pickles.Side_loaded.Verification_key.to_input side_vk in
          let packed = Random_oracle.pack_input input in
          Kimchi_pasta.Pasta.Fp.to_string (Random_oracle.hash packed)
        in
        W.write_vk_file
          ~path:(W.vk_path workdir ~layer:0 ~index:n)
          ~vk_base64:vk_b64 ~vk_hash ;
        W.write_hash ~workdir ~n ~hash:output_hash ;
        W.write_groth16_state ~workdir ~n ~acc ~line_hashes ~g_values ) ;
  Printf.eprintf "zkp%d proved.\n%!" n

(** Core compression logic.  Takes pre-compiled provers, tags, and VKs
    so the caller can choose whether to compile per-invocation or reuse
    a long-lived daemon. *)
let do_compress ~layer1_prove ~layer1_vk ~node_prove ~node_vk ~workdir
    ~base_count ~layer ~index =
  Printf.eprintf "Compressing: base=%d layer=%d index=%d in %s\n%!" base_count
    layer index workdir ;
  let system = W.detect_system ~workdir in
  let left_idx = index * 2 in
  let right_idx = (index * 2) + 1 in
  let prev_layer = layer - 1 in
  if layer = 1 then (
    (* Layer 1: merge two base proofs *)
    let actual_base = W.base_count system in
    (* last_hash is only needed for dummy/padding slots (index >= base_count).
       Read lazily so compression of early pairs can start before all states
       are computed. *)
    let last_hash = lazy (W.read_hash ~workdir ~n:(actual_base - 1)) in
    let read_base i =
      let real_i = if i < actual_base then i else 0 in
      let proof_b64, _ =
        W.read_proof_file ~path:(W.proof_path workdir ~layer:0 ~index:real_i)
      in
      let vk_b64, _ =
        W.read_vk_file ~path:(W.vk_path workdir ~layer:0 ~index:real_i)
      in
      let module P = Pickles.Proof.Make (Pickles_types.Nat.N0) in
      let proof = P.of_base64 proof_b64 |> Result.ok_or_failwith in
      let vk =
        Pickles.Side_loaded.Verification_key.of_base64 vk_b64 |> Or_error.ok_exn
      in
      if i < actual_base then
        let cin = W.read_hash ~workdir ~n:(i - 1) in
        let cout = W.read_hash ~workdir ~n:i in
        (cin, cout, proof, vk, true)
      else
        let lh = Lazy.force last_hash in
        (lh, lh, proof, vk, false)
    in
    let cin_l, cout_l, proof_l, vk_l, verify_l = read_base left_idx in
    let cin_r, cout_r, proof_r, vk_r, verify_r = read_base right_idx in
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
    let module P2 = Pickles.Proof.Make (Pickles_types.Nat.N2) in
    W.write_proof_file
      ~path:(W.proof_path workdir ~layer ~index)
      ~proof_base64:(P2.to_base64 proof) ~max_proofs_verified:2 ;
    let vk_b64 = Pickles.Side_loaded.Verification_key.to_base64 layer1_vk in
    let vk_hash =
      let input = Pickles.Side_loaded.Verification_key.to_input layer1_vk in
      let packed = Random_oracle.pack_input input in
      Kimchi_pasta.Pasta.Fp.to_string (Random_oracle.hash packed)
    in
    W.write_vk_file
      ~path:(W.vk_path workdir ~layer ~index)
      ~vk_base64:vk_b64 ~vk_hash ;
    W.marshal_to_file
      ~path:
        (Filename.concat (W.state_dir workdir)
           (sprintf "carry_%d_%d.bin" layer index) )
      (let (li, ro), vkd = carry in
       ( Step.Field.Constant.to_string li
       , Step.Field.Constant.to_string ro
       , Step.Field.Constant.to_string vkd ) ) ;
    Printf.eprintf "Layer1 %d compressed.\n%!" index )
  else
    let read_carry l i =
      let (li_s, ro_s, vkd_s) =
        ( W.marshal_from_file
            ~path:
              (Filename.concat (W.state_dir workdir)
                 (sprintf "carry_%d_%d.bin" l i) )
          : string * string * string )
      in
      ( (Step.Field.Constant.of_string li_s, Step.Field.Constant.of_string ro_s)
      , Step.Field.Constant.of_string vkd_s )
    in
    let carry_l = read_carry prev_layer left_idx in
    let carry_r = read_carry prev_layer right_idx in
    let proof_l_b64, _ =
      W.read_proof_file
        ~path:(W.proof_path workdir ~layer:prev_layer ~index:left_idx)
    in
    let proof_r_b64, _ =
      W.read_proof_file
        ~path:(W.proof_path workdir ~layer:prev_layer ~index:right_idx)
    in
    let module P2 = Pickles.Proof.Make (Pickles_types.Nat.N2) in
    let proof_l = P2.of_base64 proof_l_b64 |> Result.ok_or_failwith in
    let proof_r = P2.of_base64 proof_r_b64 |> Result.ok_or_failwith in
    let prev_vk_b64, _ =
      W.read_vk_file ~path:(W.vk_path workdir ~layer:prev_layer ~index:left_idx)
    in
    let prev_vk =
      Pickles.Side_loaded.Verification_key.of_base64 prev_vk_b64
      |> Or_error.ok_exn
    in
    let witness : TC.node_witness =
      { proof_left = Pickles.Side_loaded.Proof.of_proof proof_l
      ; vk_left = prev_vk
      ; proof_right = Pickles.Side_loaded.Proof.of_proof proof_r
      ; vk_right = prev_vk
      ; layer
      ; carry_left = carry_l
      ; carry_right = carry_r
      }
    in
    let carry, proof = TC.prove_node ~prover:node_prove ~witness in
    W.write_proof_file
      ~path:(W.proof_path workdir ~layer ~index)
      ~proof_base64:(P2.to_base64 proof) ~max_proofs_verified:2 ;
    let vk_b64 = Pickles.Side_loaded.Verification_key.to_base64 node_vk in
    let vk_hash =
      let input = Pickles.Side_loaded.Verification_key.to_input node_vk in
      let packed = Random_oracle.pack_input input in
      Kimchi_pasta.Pasta.Fp.to_string (Random_oracle.hash packed)
    in
    W.write_vk_file
      ~path:(W.vk_path workdir ~layer ~index)
      ~vk_base64:vk_b64 ~vk_hash ;
    W.write_vk_file ~path:(W.node_vk_path workdir) ~vk_base64:vk_b64 ~vk_hash ;
    W.marshal_to_file
      ~path:
        (Filename.concat (W.state_dir workdir)
           (sprintf "carry_%d_%d.bin" layer index) )
      (let (li, ro), vkd = carry in
       ( Step.Field.Constant.to_string li
       , Step.Field.Constant.to_string ro
       , Step.Field.Constant.to_string vkd ) ) ;
    Printf.eprintf "Node layer %d index %d compressed.\n%!" layer index

(** Standalone compress: compile circuits, then compress.
    Used by [internal compress] for backwards compatibility. *)
let run_internal_compress ~workdir ~base_count ~layer ~index =
  let layer1_tag, (module Layer1Proof_), layer1_prove = TC.compile_layer1 () in
  let layer1_vk =
    Promise.block_on_async_exn (fun () ->
        Pickles.Side_loaded.Verification_key.of_compiled_promise layer1_tag )
  in
  let node_tag, (module NodeProof_), node_prove = TC.compile_node () in
  let node_vk =
    Promise.block_on_async_exn (fun () ->
        Pickles.Side_loaded.Verification_key.of_compiled_promise node_tag )
  in
  do_compress ~layer1_prove ~layer1_vk ~node_prove ~node_vk ~workdir ~base_count
    ~layer ~index

(** Compression daemon: compile circuits once, then serve compress requests
    over a Unix domain socket.  Each connection sends a single line command
    and receives a single line response. *)
let run_internal_compress_daemon ~socket_path =
  Printf.eprintf "Compress daemon: compiling circuits...\n%!" ;
  let layer1_tag, (module Layer1Proof_), layer1_prove = TC.compile_layer1 () in
  let layer1_vk =
    Promise.block_on_async_exn (fun () ->
        Pickles.Side_loaded.Verification_key.of_compiled_promise layer1_tag )
  in
  Printf.eprintf "Compress daemon: layer1 compiled.\n%!" ;
  let node_tag, (module NodeProof_), node_prove = TC.compile_node () in
  let node_vk =
    Promise.block_on_async_exn (fun () ->
        Pickles.Side_loaded.Verification_key.of_compiled_promise node_tag )
  in
  Printf.eprintf "Compress daemon: node compiled.  Listening on %s\n%!"
    socket_path ;
  let socket =
    Core_unix.socket ~domain:PF_UNIX ~kind:SOCK_STREAM ~protocol:0 ()
  in
  ( try Core_unix.bind socket ~addr:(ADDR_UNIX socket_path)
    with exn ->
      Core_unix.close socket ;
      raise exn ) ;
  Core_unix.listen socket ~backlog:16 ;
  let running = ref true in
  while !running do
    let client_fd, _addr = Core_unix.accept socket in
    let ic = Core_unix.in_channel_of_descr client_fd in
    let oc = Core_unix.out_channel_of_descr client_fd in
    ( try
        let line = In_channel.input_line_exn ic in
        let parts = String.split line ~on:' ' in
        ( match parts with
        | [ "shutdown" ] ->
            Out_channel.output_string oc "OK\n" ;
            Out_channel.flush oc ;
            running := false
        | [ workdir; base_count_s; layer_s; index_s ] ->
            let base_count = Int.of_string base_count_s in
            let layer = Int.of_string layer_s in
            let index = Int.of_string index_s in
            do_compress ~layer1_prove ~layer1_vk ~node_prove ~node_vk ~workdir
              ~base_count ~layer ~index ;
            Out_channel.output_string oc "OK\n" ;
            Out_channel.flush oc
        | _ ->
            Out_channel.output_string oc
              (sprintf "ERROR bad command: %s\n" line) ;
            Out_channel.flush oc )
      with exn ->
        ( try
            Out_channel.output_string oc
              (sprintf "ERROR %s\n" (Exn.to_string exn)) ;
            Out_channel.flush oc
          with _ -> () ) ) ;
    Core_unix.close client_fd
  done ;
  Core_unix.close socket ;
  Printf.eprintf "Compress daemon: shutdown.\n%!"

(** Thin client for compress-via-daemon: connect to the daemon's Unix
    socket, send a compress command, wait for the response. *)
let run_internal_compress_via_daemon ~socket_path ~workdir ~base_count ~layer
    ~index =
  Printf.eprintf "compress-via-daemon: layer=%d index=%d\n%!" layer index ;
  let cmd_line =
    sprintf "%s %d %d %d" workdir base_count layer index
  in
  let socket =
    Core_unix.socket ~domain:PF_UNIX ~kind:SOCK_STREAM ~protocol:0 ()
  in
  (* Retry connection until daemon is ready *)
  let rec connect_retry attempts =
    try Core_unix.connect socket ~addr:(ADDR_UNIX socket_path)
    with Core_unix.Unix_error ((ENOENT | ECONNREFUSED), _, _) ->
      if attempts <= 0 then
        failwith
          (sprintf "compress-via-daemon: could not connect to %s after retries"
             socket_path )
      else (
        ignore (Core_unix.nanosleep 0.2 : float) ;
        connect_retry (attempts - 1) )
  in
  connect_retry 600 (* 2 minutes of retries *) ;
  let oc = Core_unix.out_channel_of_descr socket in
  let ic = Core_unix.in_channel_of_descr socket in
  Out_channel.output_string oc (cmd_line ^ "\n") ;
  Out_channel.flush oc ;
  let response = In_channel.input_line_exn ic in
  Core_unix.close socket ;
  if not (String.is_prefix response ~prefix:"OK") then
    failwith (sprintf "compress-via-daemon failed: %s" response) ;
  Printf.eprintf "compress-via-daemon: layer=%d index=%d done.\n%!" layer index

(** Send a shutdown command to the compress daemon. *)
let shutdown_compress_daemon ~socket_path =
  let socket =
    Core_unix.socket ~domain:PF_UNIX ~kind:SOCK_STREAM ~protocol:0 ()
  in
  ( try
      Core_unix.connect socket ~addr:(ADDR_UNIX socket_path) ;
      let oc = Core_unix.out_channel_of_descr socket in
      let ic = Core_unix.in_channel_of_descr socket in
      Out_channel.output_string oc "shutdown\n" ;
      Out_channel.flush oc ;
      let _response = In_channel.input_line_exn ic in
      Core_unix.close socket
    with exn ->
      Printf.eprintf "Warning: shutdown_compress_daemon: %s\n%!"
        (Exn.to_string exn) ;
      Core_unix.close socket )

(** Collect final output from workdir. *)
let run_internal_collect_output ~workdir =
  Printf.eprintf "Collecting output from %s\n%!" workdir ;
  let system = W.detect_system ~workdir in
  let ml = W.max_layer system in
  let proof_b64, _mpv =
    W.read_proof_file ~path:(W.proof_path workdir ~layer:ml ~index:0)
  in
  let vk_b64, vk_hash = W.read_vk_file ~path:(W.node_vk_path workdir) in
  (* Read public output from final carry *)
  let carry_path =
    Filename.concat (W.state_dir workdir) (sprintf "carry_%d_0.bin" ml)
  in
  let public_output =
    if Stdlib.Sys.file_exists carry_path then
      let (li_s, ro_s, vkd_s) =
        (W.marshal_from_file ~path:carry_path : string * string * string)
      in
      [ `String li_s; `String ro_s; `String vkd_s ]
    else []
  in
  let output =
    `Assoc
      [ ( "vkData"
        , `Assoc [ ("data", `String vk_b64); ("hash", `String vk_hash) ] )
      ; ( "proofData"
        , `Assoc
            [ ("maxProofsVerified", `Int 2)
            ; ("proof", `String proof_b64)
            ; ("publicInput", `List [])
            ; ("publicOutput", `List public_output)
            ] )
      ]
  in
  let oc = Out_channel.create (Filename.concat workdir "output.json") in
  Yojson.Safe.pretty_to_channel ~std:true oc output ;
  Out_channel.close oc ;
  Printf.eprintf "Output written to %s/output.json\n%!" workdir

(* ==== Parallel orchestrator ==== *)

(** Run a shell command, fail if it exits non-zero. *)
let run_cmd cmd =
  Printf.eprintf "  $ %s\n%!" cmd ;
  let exit_code = Stdlib.Sys.command cmd in
  if exit_code <> 0 then
    failwith (sprintf "Command failed (exit %d): %s" exit_code cmd)

(** DAG-based task scheduler with bounded parallelism.
    Each task has a command and a list of dependency indices.  Tasks whose
    dependencies have all completed are eligible to run.  Up to [parallelism]
    processes run concurrently; as each finishes, the next eligible task is
    started immediately (work-stealing, no batch barriers). *)

type task_status = Pending | Running of Pid.t | Done | Failed of int

type dag_task =
  { cmd : string
  ; deps : int array
  ; priority : int  (** Higher = scheduled first when multiple tasks ready. *)
  ; mutable status : task_status
  }

let run_dag ~parallelism (tasks : dag_task array) =
  let n = Array.length tasks in
  if n = 0 then ()
  else if parallelism <= 1 then
    (* Sequential fallback: topological order is guaranteed by deps pointing
       to lower indices only. *)
    Array.iter tasks ~f:(fun t ->
        run_cmd t.cmd ;
        t.status <- Done )
  else
    (* pid_to_task maps a child PID to its task index *)
    let pid_to_task : (Pid.t, int) Hashtbl.t =
      Hashtbl.create (module Pid) ~size:parallelism
    in
    let running = ref 0 in
    let completed = ref 0 in
    let failures = ref [] in
    let is_ready i =
      match tasks.(i).status with
      | Pending ->
          Array.for_all tasks.(i).deps ~f:(fun d ->
              match tasks.(d).status with Done -> true | _ -> false )
      | _ ->
          false
    in
    let start_task i =
      let cmd = tasks.(i).cmd in
      Printf.eprintf "  [%d/%d] $ %s\n%!" (i + 1) n cmd ;
      match Core_unix.fork () with
      | `In_the_child ->
          let exit_code = Stdlib.Sys.command cmd in
          Stdlib.exit exit_code
      | `In_the_parent pid ->
          tasks.(i).status <- Running pid ;
          Hashtbl.set pid_to_task ~key:pid ~data:i ;
          incr running
    in
    (* Fill slots with ready tasks, highest priority first.
       Among equal-priority tasks, preserve index order. *)
    let fill_slots () =
      let found = ref true in
      while !running < parallelism && !found do
        let best = ref (-1) in
        let best_pri = ref Int.min_value in
        for i = 0 to n - 1 do
          if is_ready i && tasks.(i).priority > !best_pri then (
            best := i ;
            best_pri := tasks.(i).priority )
        done ;
        if !best >= 0 then start_task !best else found := false
      done
    in
    fill_slots () ;
    (* Main loop: wait for any child, mark done, start new tasks *)
    while !running > 0 do
      (* Wait for any child *)
      let pid, status = Core_unix.wait `Any in
      ( match Hashtbl.find pid_to_task pid with
      | Some task_idx ->
          Hashtbl.remove pid_to_task pid ;
          decr running ;
          ( match status with
          | Ok () ->
              tasks.(task_idx).status <- Done ;
              incr completed ;
              Printf.eprintf "  %d completed [%d/%d]\n%!"
                (task_idx + 1) !completed n
          | Error (`Exit_non_zero code) ->
              tasks.(task_idx).status <- Failed code ;
              failures := (task_idx, code) :: !failures
          | Error (`Signal s) ->
              let code = Core.Signal.to_system_int s in
              tasks.(task_idx).status <- Failed code ;
              failures := (task_idx, code) :: !failures ) ;
          (* If any task failed, don't start new ones — let running tasks
             finish then report the failure. *)
          if List.is_empty !failures then fill_slots ()
      | None ->
          (* Unknown child — ignore (shouldn't happen) *)
          () )
    done ;
    if not (List.is_empty !failures) then (
      let msgs =
        List.map !failures ~f:(fun (i, code) ->
            sprintf "task %d (exit %d): %s" i code tasks.(i).cmd )
      in
      failwith
        (sprintf "DAG execution failed:\n  %s" (String.concat ~sep:"\n  " msgs))
    ) ;
    if !completed < n then
      failwith
        (sprintf "DAG scheduler bug: only %d of %d tasks completed" !completed n)

(** Build the self-invocation command prefix, forwarding --cache-dir. *)
let self_cmd ~cache_dir =
  let exe = Sys.argv.(0) in
  match cache_dir with
  | Some dir ->
      sprintf "%s --cache-dir %s" (Filename.quote exe) (Filename.quote dir)
  | None ->
      Filename.quote exe

(** Build the full DAG of proving + compression tasks and execute them with
    bounded parallelism.  Base proofs have no dependencies; each compression
    node depends on its two children from the previous layer.  The scheduler
    starts compression as soon as both children are done — no layer barriers.

    [system]: "plonk" or "groth16"
    [base_count]: 24 or 16
    [max_layer]: 5 or 4
    [input_path]: path to the input proof JSON
    [vk_path]: optional VK path (Groth16 only) *)
let run_parallel_pipeline ~cache_dir ~parallelism ~system ~base_count ~max_layer
    ~input_path ~vk_path =
  let self = self_cmd ~cache_dir in
  (* Create temp working directory *)
  let workdir =
    let base = Filename.temp_dir_name in
    let name =
      sprintf "nori-%s-%d" system (Core_unix.getpid () |> Pid.to_int)
    in
    Filename.concat base name
  in
  Printf.eprintf "Working directory: %s\n%!" workdir ;
  (* Stage 1: init-workdir (serial) *)
  let init_cmd =
    match vk_path with
    | Some vk ->
        sprintf "%s internal init-workdir %s %s %s %s" self
          (Filename.quote workdir) system
          (Filename.quote input_path)
          (Filename.quote vk)
    | None ->
        sprintf "%s internal init-workdir %s %s %s" self
          (Filename.quote workdir) system
          (Filename.quote input_path)
  in
  run_cmd init_cmd ;
  (* Fork compression daemon early so circuit compilation overlaps with
     witness generation.  The daemon only needs the workdir to exist
     (for its socket path); it doesn't read any witness/state files. *)
  let socket_path = Filename.concat workdir "compress.sock" in
  let daemon_pid =
    match Core_unix.fork () with
    | `In_the_child ->
        run_internal_compress_daemon ~socket_path ;
        Stdlib.exit 0
    | `In_the_parent pid ->
        pid
  in
  Printf.eprintf "Compress daemon started (pid %d), compiling in background\n%!"
    (Pid.to_int daemon_pid) ;
  (* Build the DAG.  generate-witness is task 0 so it runs in parallel
     with daemon compilation rather than blocking the DAG start.

     Task layout (indices):
       0                                    : generate-witness
       1 .. base_count                      : compute-state 0..N-1
       base_count+1 .. 2*base_count         : prove-zkp 0..N-1
       2*base_count+1 ..                    : compression tasks

     Dependencies:
       generate-witness    : (none)
       compute-state 0     : generate-witness
       compute-state n>0   : compute-state n-1
       prove-zkp n         : compute-state n
       compress layer=1, i : prove-zkp 2i, prove-zkp 2i+1
       compress layer>1, i : compress prev_layer 2i, compress prev_layer 2i+1 *)
  let padded_count =
    let rec next_pow2 x = if x >= base_count then x else next_pow2 (x * 2) in
    next_pow2 1
  in
  if padded_count > base_count then
    Printf.eprintf "Padding %d → %d for binary tree\n%!" base_count
      padded_count ;
  let compression_counts =
    Array.init max_layer ~f:(fun i ->
        let layer = i + 1 in
        let prev_count =
          if layer = 1 then padded_count
          else padded_count / Int.pow 2 (layer - 1)
        in
        prev_count / 2 )
  in
  let total_compression =
    Array.fold compression_counts ~init:0 ~f:( + )
  in
  (* generate-witness + compute-state + prove-zkp + compression *)
  let total_tasks = 1 + base_count + base_count + total_compression in
  let gw_idx = 0 in                           (* generate-witness *)
  let cs_start = 1 in                         (* compute-state tasks *)
  let prove_start = 1 + base_count in          (* prove-zkp tasks *)
  let compress_start = 1 + 2 * base_count in   (* compression tasks *)
  Printf.eprintf
    "Building DAG: 1 generate-witness + %d compute-state + %d prove-zkp + %d \
     compression = %d tasks (parallelism=%d)\n\
     %!"
    base_count base_count total_compression total_tasks parallelism ;
  let tasks = Array.create ~len:total_tasks
      { cmd = ""; deps = [||]; priority = 0; status = Pending }
  in
  (* generate-witness: high priority, no deps — runs in parallel with
     daemon compilation *)
  tasks.(gw_idx) <-
    { cmd =
        sprintf "%s internal generate-witness %s" self (Filename.quote workdir)
    ; deps = [||]
    ; priority = 1
    ; status = Pending
    } ;
  (* compute-state tasks: sequential chain, high priority — gates all
     proving so must not be starved by leaf proofs. *)
  for n = 0 to base_count - 1 do
    tasks.(cs_start + n) <-
      { cmd =
          sprintf "%s internal compute-state %s %d" self
            (Filename.quote workdir) n
      ; deps =
          (if n = 0 then [| gw_idx |] else [| cs_start + n - 1 |])
      ; priority = 1
      ; status = Pending
      }
  done ;
  (* prove-zkp tasks: lowest priority — most plentiful, fill idle slots *)
  for n = 0 to base_count - 1 do
    tasks.(prove_start + n) <-
      { cmd =
          sprintf "%s internal prove-zkp %s %d" self (Filename.quote workdir) n
      ; deps = [| cs_start + n |]
      ; priority = 0
      ; status = Pending
      }
  done ;
  (* Compression tasks: highest priority — on the critical path of the
     reduction tree.  Starting these as soon as their children are done
     overlaps compression with remaining base proving. *)
  let layer_start = Array.create ~len:(max_layer + 1) 0 in
  layer_start.(0) <- prove_start ;  (* layer 0 = prove-zkp tasks *)
  let task_idx = ref compress_start in
  for li = 0 to max_layer - 1 do
    let layer = li + 1 in
    layer_start.(layer) <- !task_idx ;
    let n_merges = compression_counts.(li) in
    for index = 0 to n_merges - 1 do
      let left_child = index * 2 in
      let right_child = (index * 2) + 1 in
      let deps =
        if layer = 1 then
          let dep_l = prove_start + min left_child (base_count - 1) in
          let dep_r = prove_start + min right_child (base_count - 1) in
          if dep_l = dep_r then [| dep_l |] else [| dep_l; dep_r |]
        else
          let prev_start = layer_start.(layer - 1) in
          [| prev_start + left_child; prev_start + right_child |]
      in
      tasks.(!task_idx) <-
        { cmd =
            sprintf "%s internal compress-via-daemon %s %s %d %d %d" self
              (Filename.quote socket_path)
              (Filename.quote workdir) base_count layer index
        ; deps
        ; priority = 2
        ; status = Pending
        } ;
      incr task_idx
    done
  done ;
  assert (!task_idx = total_tasks) ;
  (* Execute the DAG *)
  run_dag ~parallelism tasks ;
  (* Shut down compression daemon *)
  shutdown_compress_daemon ~socket_path ;
  ( try
      match Core_unix.waitpid daemon_pid with
      | Ok () ->
          Printf.eprintf "Compress daemon exited normally.\n%!"
      | Error _ ->
          Printf.eprintf "Warning: compress daemon exited abnormally.\n%!"
    with Core_unix.Unix_error (ECHILD, _, _) ->
      (* Already reaped by the DAG scheduler's wait(`Any) *)
      Printf.eprintf "Compress daemon already exited.\n%!" ) ;
  (* Collect output (serial) *)
  run_cmd
    (sprintf "%s internal collect-output %s" self (Filename.quote workdir)) ;
  (* Copy output to final location *)
  let output_src = Filename.concat workdir "output.json" in
  let dir = Filename.dirname input_path in
  let base = Filename.basename input_path in
  let base_no_ext =
    if String.is_suffix ~suffix:".json" (String.lowercase base) then
      String.sub base ~pos:0 ~len:(String.length base - 5)
    else base
  in
  let command_name =
    match system with "plonk" -> "sp1ToPlonk" | _ -> "risc0ToGroth16"
  in
  let output_dst =
    Filename.concat dir (base_no_ext ^ "." ^ command_name ^ ".json")
  in
  let data = In_channel.read_all output_src in
  Out_channel.write_all output_dst ~data ;
  Printf.eprintf "Output written to %s\n%!" output_dst

let () =
  (* Extract --cache-dir and --parallelism options before command dispatch *)
  let argv = Array.to_list Sys.argv in
  let cache_dir, parallelism, argv =
    let rec extract ~cd ~par acc = function
      | "--cache-dir" :: dir :: rest ->
          extract ~cd:(Some dir) ~par acc rest
      | "--parallelism" :: n :: rest ->
          extract ~cd ~par:(Some (Int.of_string n)) acc rest
      | x :: rest ->
          extract ~cd ~par (x :: acc) rest
      | [] ->
          (cd, par, List.rev acc)
    in
    extract ~cd:None ~par:None [] argv
  in
  let parallelism = Option.value parallelism ~default:1 in
  ( match cache_dir with
  | Some dir ->
      Printf.eprintf "Using cache directory: %s\n%!" dir ;
      let () = Key_cache_native.linkme in
      Core_unix.mkdir_p dir ;
      Proof_conversion.Cache_config.set_cache_dir dir
  | None ->
      () ) ;
  let argv = Array.of_list argv in
  match argv with
  | [| _; "sp1ToPlonk"; input_path |] ->
      run_sp1_to_plonk ~input_path ~aux_path:""
  | [| _; "sp1ToPlonk"; input_path; aux_path |] ->
      run_sp1_to_plonk ~input_path ~aux_path
  | [| _; "risc0ToGroth16"; proof_path; vk_path |] ->
      run_risc0_to_groth16 ~proof_path ~vk_path
  | [| _; "sp1ToPlonkParallel"; input_path |] ->
      run_parallel_pipeline ~cache_dir ~parallelism ~system:"plonk"
        ~base_count:24 ~max_layer:5 ~input_path ~vk_path:None
  | [| _; "risc0ToGroth16Parallel"; proof_path; vk_path |] ->
      run_parallel_pipeline ~cache_dir ~parallelism ~system:"groth16"
        ~base_count:16 ~max_layer:4 ~input_path:proof_path
        ~vk_path:(Some vk_path)
  (* ---- Internal stage commands ---- *)
  | [| _; "internal"; "init-workdir"; workdir; "plonk"; input_path |] ->
      run_internal_init_workdir ~workdir ~system:"plonk" ~input_path
        ~vk_path:None
  | [| _; "internal"; "init-workdir"; workdir; "groth16"; proof_path; vk_path |]
    ->
      run_internal_init_workdir ~workdir ~system:"groth16"
        ~input_path:proof_path ~vk_path:(Some vk_path)
  | [| _; "internal"; "generate-witness"; workdir |] ->
      run_internal_generate_witness ~workdir
  | [| _; "internal"; "compute-state"; workdir; n_str |] ->
      run_internal_compute_state ~workdir ~n:(Int.of_string n_str)
  | [| _; "internal"; "prove-zkp"; workdir; n_str |] ->
      run_internal_prove_zkp ~workdir ~n:(Int.of_string n_str)
  | [| _; "internal"; "compress"; workdir; base_count; layer; index |] ->
      run_internal_compress ~workdir ~base_count:(Int.of_string base_count)
        ~layer:(Int.of_string layer) ~index:(Int.of_string index)
  | [| _; "internal"; "compress-daemon"; socket_path |] ->
      run_internal_compress_daemon ~socket_path
  | [| _; "internal"; "compress-via-daemon"
     ; socket_path; workdir; base_count; layer; index |] ->
      run_internal_compress_via_daemon ~socket_path ~workdir
        ~base_count:(Int.of_string base_count) ~layer:(Int.of_string layer)
        ~index:(Int.of_string index)
  | [| _; "internal"; "collect-output"; workdir |] ->
      run_internal_collect_output ~workdir
  | _ ->
      Printf.eprintf
        "Usage: nori-proof-converter [--cache-dir <dir>] [--parallelism <n>] \
         <command> [args...]\n\n" ;
      Printf.eprintf
        "Available commands: sp1ToPlonk, risc0ToGroth16, sp1ToPlonkParallel, \
         risc0ToGroth16Parallel\n\n" ;
      Printf.eprintf "Parallel commands:\n" ;
      Printf.eprintf "  sp1ToPlonkParallel <input.json>\n" ;
      Printf.eprintf "  risc0ToGroth16Parallel <proof.json> <vk.json>\n\n" ;
      Printf.eprintf "Internal commands (for staged/parallel execution):\n" ;
      Printf.eprintf "  internal init-workdir <workdir> plonk <input.json>\n" ;
      Printf.eprintf
        "  internal init-workdir <workdir> groth16 <proof.json> <vk.json>\n" ;
      Printf.eprintf "  internal generate-witness <workdir>\n" ;
      Printf.eprintf "  internal compute-state <workdir> <n>\n" ;
      Printf.eprintf "  internal prove-zkp <workdir> <n>\n" ;
      Printf.eprintf
        "  internal compress <workdir> <base_count> <layer> <index>\n" ;
      Printf.eprintf "  internal collect-output <workdir>\n\n" ;
      Printf.eprintf "Options:\n" ;
      Printf.eprintf
        "  --cache-dir <dir>     Cache proving keys to disk for reuse\n" ;
      Printf.eprintf
        "  --parallelism <n>     Max parallel processes for compression \
         (default: 1)\n" ;
      exit 1
