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
      let acc = Proof_conversion.Plonk.Proof_json.load_sp1 input_path in
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
            Proof_conversion.Plonk.Proof_json.parse_aux_witness aux_json
        | None ->
            Printf.eprintf
              "Computing PLONK aux witness natively (circuits 0-12 unchecked + \
               Rust FFI)...\n\
               %!" ;
            let mlo =
              Proof_conversion.Plonk.Witness_tracker.compute_kzg_mlo acc
            in
            let w27 = Proof_conversion.Bn254.Bn254_params.w27 () in
            let groth16_aux =
              Proof_conversion.Pairing_utils_bridge.compute_aux_witness_with_w27
                mlo w27
            in
            { Proof_conversion.Plonk.Proof_json.shift_power =
                Step.Field.Constant.of_int groth16_aux.shift_power
            ; c_fp12 = groth16_aux.c
            }
      in
      (acc, aux) )
    else (
      Printf.eprintf "Detected fixture format.\n%!" ;
      Proof_conversion.Plonk.Proof_json.load_fixture_with_aux input_path )
  in
  let input_hash =
    Proof_conversion.Plonk.Witness_tracker.hash_accumulator_const acc_const
  in
  Printf.eprintf "Initial hash: %s\n%!"
    (Step.Field.Constant.to_string input_hash) ;
  (* === Prove all 24 base circuits === *)
  Printf.eprintf "Proving 24 base circuits...\n%!" ;
  let current_hash = ref input_hash in
  let current_acc = ref acc_const in
  let base_proofs :
      ( Step.Field.Constant.t
      * Step.Field.Constant.t
      * Pickles_types.Nat.N0.n Pickles.Proof.t
      * Pickles.Side_loaded.Verification_key.t )
      option
      array =
    Array.create ~len:24 None
  in
  (* zkp0-11 *)
  for n = 0 to 11 do
    Printf.eprintf "  zkp%d...\n%!" n ;
    let w : Proof_conversion.Plonk.Requests.witness =
      { Proof_conversion.Plonk.Requests.empty_witness with
        plonk_acc = Some !current_acc
      }
    in
    let output_hash, proof, vk =
      Proof_conversion.Plonk.Pickles_rules.compile_prove_and_export
        ~skip_verify:true ~n ~input_hash:!current_hash ~witness:w
    in
    let _, acc_after, _ =
      Proof_conversion.Plonk.Pickles_rules.compile_and_prove_one_with_plonk_acc
        ~n ~input_hash:!current_hash ~witness:w
    in
    base_proofs.(n) <- Some (!current_hash, output_hash, proof, vk) ;
    current_hash := output_hash ;
    current_acc := acc_after
  done ;
  (* zkp12 *)
  Printf.eprintf "  zkp12...\n%!" ;
  let w12 : Proof_conversion.Plonk.Requests.witness =
    { Proof_conversion.Plonk.Requests.empty_witness with
      plonk_acc = Some !current_acc
    ; shift_power = Some aux.shift_power
    ; c_fp12 = Some aux.c_fp12
    }
  in
  let output_hash_12, proof_12, vk_12 =
    Proof_conversion.Plonk.Pickles_rules.compile_prove_and_export
      ~skip_verify:true ~n:12 ~input_hash:!current_hash ~witness:w12
  in
  let _, kzg_const, _ =
    Proof_conversion.Plonk.Pickles_rules.compile_and_prove_zkp12
      ~input_hash:!current_hash ~witness:w12
  in
  base_proofs.(12) <- Some (!current_hash, output_hash_12, proof_12, vk_12) ;
  current_hash := output_hash_12 ;
  (* zkp13-16 *)
  let current_kzg = ref kzg_const in
  let all_g_values = ref [||] in
  let ate_loop_len = Proof_conversion.Plonk.Kzg_accumulator.ate_loop_len in
  let current_lines_hashes =
    ref (Array.create ~len:ate_loop_len Step.Field.Constant.zero)
  in
  for n = 13 to 16 do
    Printf.eprintf "  zkp%d...\n%!" n ;
    let w : Proof_conversion.Plonk.Requests.witness =
      { Proof_conversion.Plonk.Requests.empty_witness with
        kzg_acc = Some !current_kzg
      ; lines_hashes = Some !current_lines_hashes
      }
    in
    let output_hash, proof, vk =
      Proof_conversion.Plonk.Pickles_rules.compile_prove_and_export
        ~skip_verify:true ~n ~input_hash:!current_hash ~witness:w
    in
    let _, kzg_after, lh_after, gv, _ =
      Proof_conversion.Plonk.Pickles_rules.compile_and_prove_zkp_lines
        ~circuit_index:n ~input_hash:!current_hash ~witness:w
    in
    base_proofs.(n) <- Some (!current_hash, output_hash, proof, vk) ;
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
    let w : Proof_conversion.Plonk.Requests.witness =
      { Proof_conversion.Plonk.Requests.empty_witness with
        kzg_acc = Some !current_kzg
      ; g_chunk = Some g_chunk
      ; flat_hashes = Some flat_hashes
      }
    in
    let output_hash, proof, vk =
      Proof_conversion.Plonk.Pickles_rules.compile_prove_and_export
        ~skip_verify:true ~n ~input_hash:!current_hash ~witness:w
    in
    let _, kzg_after, _ =
      Proof_conversion.Plonk.Pickles_rules.compile_and_prove_zkp_f_accum
        ~circuit_index:n ~input_hash:!current_hash ~witness:w
    in
    base_proofs.(n) <- Some (!current_hash, output_hash, proof, vk) ;
    current_hash := output_hash ;
    current_kzg := kzg_after
  done ;
  (* zkp23 *)
  Printf.eprintf "  zkp23...\n%!" ;
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
      ~skip_verify:true ~n:23 ~input_hash:!current_hash ~witness:w23
  in
  base_proofs.(23) <- Some (!current_hash, output_hash_23, proof_23, vk_23) ;
  Printf.eprintf "All 24 base circuits proved.\n%!" ;
  (* === Tree compression === *)
  Printf.eprintf "Tree compression...\n%!" ;
  let layer1_tag, (module Layer1Proof), layer1_prove = TC.compile_layer1 () in
  ignore (module Layer1Proof : Pickles.Proof_intf) ;
  let _, cout23, _, _ = Option.value_exn base_proofs.(23) in
  let padded_proofs =
    Array.init 32 ~f:(fun i ->
        if i < 24 then
          let cin, cout, proof, vk = Option.value_exn base_proofs.(i) in
          (cin, cout, proof, vk, true)
        else
          let _, _, proof, vk = Option.value_exn base_proofs.(0) in
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
  let module WT = Proof_conversion.Groth16.Witness_tracker in
  let proof = Proof_conversion.Groth16.Proof_json.load_proof proof_path in
  let vk_raw = Proof_conversion.Groth16.Proof_json.load_vk vk_path in
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
        Proof_conversion.Groth16.Proof_json.load_aux_witness p
    | None ->
        (* Try default path, fall back to native computation *)
        let default_path =
          Filename.concat (Filename.dirname proof_path) "aux_witness.json"
        in
        if Stdlib.Sys.file_exists default_path then (
          Printf.eprintf "Loading aux witness from %s\n%!" default_path ;
          Proof_conversion.Groth16.Proof_json.load_aux_witness default_path )
        else (
          Printf.eprintf "Computing aux witness natively via Rust FFI...\n%!" ;
          Proof_conversion.Pairing_utils_bridge.groth16_aux_witness ~proof ~vk )
  in
  let tracker = WT.create ~proof ~vk ~aux in
  Proof_conversion.Groth16.Circuit_config.set_tracker tracker ;
  let vk_const = Proof_conversion.Groth16.Vk_constants.create vk in
  let b_lines = WT.get_all_b_lines tracker in
  (* Compute initial accumulator *)
  let n_total =
    Array.length Proof_conversion.Bn254.Bn254_params.ate_loop_count
  in
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
            ( Proof_conversion.Bn254.Fp6.Constant.zero
            , Proof_conversion.Bn254.Fp6.Constant.zero )
        }
    }
  in
  let initial_hash =
    Step.run_and_check_exn (fun () ->
        let acc =
          Step.exists Proof_conversion.Groth16.Accumulator.typ
            ~compute:(fun () -> initial_acc)
        in
        let h = Proof_conversion.Groth16.Accumulator.hash acc in
        fun () -> Step.As_prover.read_var h )
  in
  Printf.eprintf "Initial hash: %s\n%!"
    (Step.Field.Constant.to_string initial_hash) ;
  (* === Prove all 16 base circuits === *)
  Printf.eprintf "Proving 16 base circuits...\n%!" ;
  let num_circuits = Proof_conversion.Groth16.Circuits.num_circuits in
  let current_hash = ref initial_hash in
  let current_acc = ref initial_acc in
  let evolving_line_hashes =
    ref (Array.create ~len:n_total Step.Field.Constant.zero)
  in
  let all_g_values = ref [||] in
  let base_proofs :
      ( Step.Field.Constant.t
      * Step.Field.Constant.t
      * Pickles_types.Nat.N0.n Pickles.Proof.t
      * Pickles.Side_loaded.Verification_key.t )
      option
      array =
    Array.create ~len:num_circuits None
  in
  (* Circuits 0-6: ate loop with accumulator chaining *)
  for n = 0 to 6 do
    Printf.eprintf "  zkp%d...\n%!" n ;
    let witness : Proof_conversion.Groth16.Requests.witness =
      { Proof_conversion.Groth16.Requests.empty_witness with
        accumulator = Some !current_acc
      ; line_hashes = Some !evolving_line_hashes
      ; b_lines =
          Some
            (Array.map b_lines ~f:(fun (l : WT.Line.t) -> (l.lambda, l.neg_mu)))
      }
    in
    let output_hash, acc_after, lh_after, gv_after, proof, side_vk =
      Proof_conversion.Groth16.Pickles_rules.compile_prove_and_export_with_acc
        ~skip_verify:true ~vk:vk_const ~n ~input_hash:!current_hash ~witness
    in
    base_proofs.(n) <- Some (!current_hash, output_hash, proof, side_vk) ;
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
      Proof_conversion.Groth16.Fupdate_circuit.iterations_per_circuit.(idx)
    in
    let g_start =
      Proof_conversion.Groth16.Fupdate_circuit.g_start_per_circuit.(idx)
    in
    let all_lh = !evolving_line_hashes in
    let lhs = Array.sub all_lh ~pos:0 ~len:g_start in
    let g_chunk = Array.sub !all_g_values ~pos:g_start ~len:n_iters in
    let rhs_start = g_start + n_iters in
    let rhs =
      Array.sub all_lh ~pos:rhs_start ~len:(Array.length all_lh - rhs_start)
    in
    let witness : Proof_conversion.Groth16.Requests.witness =
      { Proof_conversion.Groth16.Requests.empty_witness with
        accumulator = Some !current_acc
      ; g_chunk = Some g_chunk
      ; lhs_hashes = Some lhs
      ; rhs_hashes = Some rhs
      }
    in
    (* Use compile_prove_and_export_with_acc for acc + VK, but don't
       update line_hashes or g_values (f-update doesn't change them). *)
    let output_hash, acc_after, _lh, _gv, proof, side_vk =
      Proof_conversion.Groth16.Pickles_rules.compile_prove_and_export_with_acc
        ~skip_verify:true ~vk:vk_const ~n ~input_hash:!current_hash ~witness
    in
    base_proofs.(n) <- Some (!current_hash, output_hash, proof, side_vk) ;
    current_hash := output_hash ;
    current_acc := acc_after
  done ;
  (* Circuit 13: final exponentiation *)
  Printf.eprintf "  zkp13...\n%!" ;
  let all_lh = !evolving_line_hashes in
  let lhs_13 = Array.sub all_lh ~pos:0 ~len:(n_total - 1) in
  let witness_13 : Proof_conversion.Groth16.Requests.witness =
    { Proof_conversion.Groth16.Requests.empty_witness with
      accumulator = Some !current_acc
    ; lhs_hashes = Some lhs_13
    ; final_g = Some !all_g_values.(Array.length !all_g_values - 1)
    }
  in
  let output_hash_13, proof_13, vk_13 =
    Proof_conversion.Groth16.Pickles_rules.compile_prove_and_export
      ~skip_verify:true ~vk:vk_const ~n:13 ~input_hash:!current_hash
      ~witness:witness_13
  in
  base_proofs.(13) <- Some (!current_hash, output_hash_13, proof_13, vk_13) ;
  current_hash := output_hash_13 ;
  (* Circuit 14: partial IC *)
  Printf.eprintf "  zkp14...\n%!" ;
  let n_pi = WT.num_public_inputs tracker in
  let pis = Array.init n_pi ~f:(fun i -> WT.get_public_input tracker i) in
  let witness_14 : Proof_conversion.Groth16.Requests.witness =
    { Proof_conversion.Groth16.Requests.empty_witness with
      public_inputs = Some pis
    }
  in
  let output_hash_14, proof_14, vk_14 =
    Proof_conversion.Groth16.Pickles_rules.compile_prove_and_export
      ~skip_verify:true ~vk:vk_const ~n:14 ~input_hash:!current_hash
      ~witness:witness_14
  in
  base_proofs.(14) <- Some (!current_hash, output_hash_14, proof_14, vk_14) ;
  current_hash := output_hash_14 ;
  (* Circuit 15: full IC *)
  Printf.eprintf "  zkp15...\n%!" ;
  let pis_15 = Array.init n_pi ~f:(fun i -> WT.get_public_input tracker i) in
  let pi = WT.get_pi tracker in
  let partial_acc = WT.get_partial_ic_acc tracker in
  let g1_to_const (p : WT.G1.t) : Proof_conversion.Bn254.G1.Constant.t =
    { x = p.x; y = p.y }
  in
  let witness_15 : Proof_conversion.Groth16.Requests.witness =
    { Proof_conversion.Groth16.Requests.empty_witness with
      public_inputs = Some pis_15
    ; pi_point = Some (g1_to_const pi)
    ; partial_ic_acc = Some (g1_to_const partial_acc)
    }
  in
  let output_hash_15, proof_15, vk_15 =
    Proof_conversion.Groth16.Pickles_rules.compile_prove_and_export
      ~skip_verify:true ~vk:vk_const ~n:15 ~input_hash:!current_hash
      ~witness:witness_15
  in
  base_proofs.(15) <- Some (!current_hash, output_hash_15, proof_15, vk_15) ;
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
        let cin_l, cout_l, proof_l, vk_l = Option.value_exn base_proofs.(li) in
        let cin_r, cout_r, proof_r, vk_r = Option.value_exn base_proofs.(ri) in
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

(** Parse input and write the initial state (hash_-1, plonk_state_-1 or
    groth16_state_-1).  For PLONK this is fast because it only needs the
    parsed accumulator — the expensive aux witness computation is deferred
    to [compute-aux-witness].  For Groth16 the aux witness is needed for the
    initial accumulator, so both are computed here. *)
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
      let acc_const =
        if is_sp1 then Proof_conversion.Plonk.Proof_json.load_sp1 input_path
        else
          let acc, _aux =
            Proof_conversion.Plonk.Proof_json.load_fixture_with_aux input_path
          in
          acc
      in
      let initial_hash =
        Proof_conversion.Plonk.Witness_tracker.hash_accumulator_const acc_const
      in
      W.write_hash ~workdir ~n:(-1) ~hash:initial_hash ;
      W.write_plonk_state ~workdir ~n:(-1) ~acc:acc_const
  | W.Groth16 _ ->
      let proof_path = Filename.concat workdir "proof.json" in
      let vk_path = Filename.concat workdir "vk.json" in
      let proof = Proof_conversion.Groth16.Proof_json.load_proof proof_path in
      let vk = Proof_conversion.Groth16.Proof_json.load_vk vk_path in
      let aux =
        Proof_conversion.Pairing_utils_bridge.groth16_aux_witness ~proof ~vk
      in
      Proof_conversion.Groth16.Proof_json.save_aux_witness
        (Filename.concat workdir "aux_witness.json")
        aux ;
      let module WT = Proof_conversion.Groth16.Witness_tracker in
      let tracker = WT.create ~proof ~vk ~aux in
      Proof_conversion.Groth16.Circuit_config.set_tracker tracker ;
      let n_total =
        Array.length Proof_conversion.Bn254.Bn254_params.ate_loop_count
      in
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
                ( Proof_conversion.Bn254.Fp6.Constant.zero
                , Proof_conversion.Bn254.Fp6.Constant.zero )
            }
        }
      in
      let initial_hash =
        Step.run_and_check_exn (fun () ->
            let acc =
              Step.exists Proof_conversion.Groth16.Accumulator.typ
                ~compute:(fun () -> initial_acc)
            in
            let h = Proof_conversion.Groth16.Accumulator.hash acc in
            fun () -> Step.As_prover.read_var h )
      in
      W.write_hash ~workdir ~n:(-1) ~hash:initial_hash ;
      let line_hashes = Array.create ~len:n_total Step.Field.Constant.zero in
      W.write_groth16_state ~workdir ~n:(-1) ~acc:initial_acc ~line_hashes
        ~g_values:[||] ) ;
  Printf.eprintf "Witness generated.\n%!"

(** Compute the PLONK aux witness (shift_power, c from Miller loop).
    This is the expensive part (~30s) that was previously bundled into
    generate-witness.  Split out so it can run in parallel with early
    compute-state / prove-zkp tasks; only compute-state 12 needs it. *)
let run_internal_compute_aux_witness ~workdir =
  Printf.eprintf "Computing aux witness in %s\n%!" workdir ;
  let system = W.detect_system ~workdir in
  ( match system with
  | W.Plonk _ ->
      let aux_file = Filename.concat workdir "aux_witness.json" in
      if Stdlib.Sys.file_exists aux_file then
        Printf.eprintf "Aux witness already exists, skipping.\n%!"
      else
        (* Read state 11 — contains kzg_cm_x/y and neg_fq_x/y from
           circuits 0-11.  This avoids re-running those circuits. *)
        let acc11 = W.read_plonk_state ~workdir ~n:11 in
        (* Extract KZG A/B points from state 11 via prepare_pairing_1
           (a few EC operations, fast). *)
        let a_x, a_y, neg_b_x, neg_b_y =
          Proof_conversion.Plonk.Witness_tracker.extract_kzg_points_from_state11
            acc11
        in
        Printf.eprintf "  KZG points extracted from state 11.\n%!" ;
        let mlo =
          Proof_conversion.Plonk.Witness_tracker.compute_mlo_from_points ~a_x
            ~a_y ~neg_b_x ~neg_b_y
        in
        Printf.eprintf "  Miller loop computed.\n%!" ;
        let w27 = Proof_conversion.Bn254.Bn254_params.w27 () in
        let g_aux =
          Proof_conversion.Pairing_utils_bridge.compute_aux_witness_with_w27 mlo
            w27
        in
        let aux : Proof_conversion.Plonk.Proof_json.aux_witness =
          { shift_power = Step.Field.Constant.of_int g_aux.shift_power
          ; c_fp12 = g_aux.c
          }
        in
        let aux_json =
          `Assoc
            [ ( "shift_power"
              , `String (Step.Field.Constant.to_string aux.shift_power) )
            ; ("c", Proof_conversion.Groth16.Proof_json.fp12_to_json aux.c_fp12)
            ]
        in
        Yojson.Safe.to_file aux_file aux_json
  | W.Groth16 _ ->
      () ) ;
  Printf.eprintf "Aux witness computed.\n%!"

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
      let ate_loop_len = Proof_conversion.Plonk.Kzg_accumulator.ate_loop_len in
      if n <= 11 then (
        (* Circuits 0-11: evolve Plonk_accumulator.
           Use fast path: inject acc as constants, skip Poseidon hashing,
           compute output hash natively after readback. *)
        let cur_acc = W.read_plonk_state ~workdir ~n:(n - 1) in
        let result = ref cur_acc in
        Step.run_unchecked (fun () ->
            let acc_var =
              Proof_conversion.Plonk.Circuits.zkp_fast_fns.(n) cur_acc
            in
            Step.as_prover (fun () ->
                result :=
                  Step.As_prover.read Proof_conversion.Plonk.Accumulator.typ
                    acc_var ) ) ;
        let ac = !result in
        let oh =
          Proof_conversion.Plonk.Witness_tracker.hash_accumulator_const ac
        in
        W.write_hash ~workdir ~n ~hash:oh ;
        W.write_plonk_state ~workdir ~n ~acc:ac )
      else if n = 12 then (
        (* Circuit 12: transition Plonk_accumulator → Kzg_accumulator.
           Fast path: inject acc + aux as constants, skip hashing. *)
        let cur_acc = W.read_plonk_state ~workdir ~n:11 in
        let aux_path = Filename.concat workdir "aux_witness.json" in
        let aux_json = Yojson.Safe.from_file aux_path in
        let shift_power =
          Step.Field.Constant.of_string
            Yojson.Safe.Util.(member "shift_power" aux_json |> to_string)
        in
        let c_fp12 =
          Proof_conversion.Groth16.Proof_json.fp12_of_json
            (Yojson.Safe.Util.member "c" aux_json)
        in
        let result12 : Proof_conversion.Plonk.Kzg_accumulator.t_const option ref
            =
          ref None
        in
        Step.run_unchecked (fun () ->
            let kzg =
              Proof_conversion.Plonk.Circuits.zkp12_fast cur_acc ~shift_power
                ~c_fp12
            in
            Step.as_prover (fun () ->
                result12 :=
                  Some
                    (Step.As_prover.read
                       Proof_conversion.Plonk.Kzg_accumulator.typ kzg ) ) ) ;
        let kzg12 = Option.value_exn !result12 in
        let oh12 =
          Proof_conversion.Plonk.Witness_tracker.hash_kzg_accumulator_const
            kzg12
        in
        W.write_hash ~workdir ~n:12 ~hash:oh12 ;
        W.write_plonk_kzg_state ~workdir ~n:12 ~kzg:kzg12
          ~lines_hashes:
            (Array.create ~len:ate_loop_len Step.Field.Constant.zero)
          ~g_values:[||] )
      else if n <= 16 then (
        (* Circuits 13-16: KZG line circuits.
           Fully native: no run_unchecked, pure Bignum_bigint arithmetic. *)
        let cur_kzg, cur_kzg_lh, cur_kzg_gv =
          W.read_plonk_kzg_state ~workdir ~n:(n - 1)
        in
        let result_kzg, result_lh, result_gv =
          Proof_conversion.Plonk.Circuits.zkp_lines_native ~circuit_index:n
            cur_kzg ~lines_hashes:cur_kzg_lh
        in
        let oh =
          Proof_conversion.Plonk.Witness_tracker.hash_kzg_accumulator_const
            result_kzg
        in
        W.write_hash ~workdir ~n ~hash:oh ;
        W.write_plonk_kzg_state ~workdir ~n ~kzg:result_kzg
          ~lines_hashes:result_lh
          ~g_values:(Array.append cur_kzg_gv result_gv) )
      else if n <= 22 then (
        (* Circuits 17-22: f-accumulation.
           Fully native: no run_unchecked, pure Bignum_bigint Fp12 arithmetic. *)
        let cur_kzg, _lh_prev, _gv_prev =
          W.read_plonk_kzg_state ~workdir ~n:(n - 1)
        in
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
        let result_kzg =
          Proof_conversion.Plonk.Circuits.zkp_f_accum_native ~circuit_index:n
            cur_kzg ~g_chunk_const:g_chunk
        in
        let oh =
          Proof_conversion.Plonk.Witness_tracker.hash_kzg_accumulator_const
            result_kzg
        in
        W.write_hash ~workdir ~n ~hash:oh ;
        W.write_plonk_kzg_state ~workdir ~n ~kzg:result_kzg
          ~lines_hashes:lines_hashes_snapshot ~g_values:g_values_snapshot )
      else (
        (* Circuit 23: final exponentiation.
           This circuit returns a hash of pi0/pi1, not the KZG accumulator.
           Keep the original approach for now (zkp23 needs the full circuit
           including hash verification for the pi output), but use constants
           for the KZG acc and subsidiary witnesses. *)
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
        let w23 : Proof_conversion.Plonk.Requests.witness =
          { Proof_conversion.Plonk.Requests.empty_witness with
            kzg_acc = Some cur_kzg
          ; lhs_hashes = Some lhs_hashes_23
          ; g_chunk = Some g_chunk_23
          }
        in
        let handler23 = Proof_conversion.Plonk.Requests.handler w23 in
        let result_hash23 = ref cur_hash in
        Step.run_unchecked (fun () ->
            Step.handle
              (fun () ->
                let input_var = Step.Field.constant cur_hash in
                let output_hash =
                  Proof_conversion.Plonk.Circuits.zkp23 input_var
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
      let proof = Proof_conversion.Groth16.Proof_json.load_proof proof_path in
      let vk = Proof_conversion.Groth16.Proof_json.load_vk vk_path in
      let vk_const = Proof_conversion.Groth16.Vk_constants.create vk in
      let aux =
        Proof_conversion.Groth16.Proof_json.load_aux_witness
          (Filename.concat workdir "aux_witness.json")
      in
      let module WT = Proof_conversion.Groth16.Witness_tracker in
      let tracker = WT.create ~proof ~vk ~aux in
      Proof_conversion.Groth16.Circuit_config.set_tracker tracker ;
      let n_total =
        Array.length Proof_conversion.Bn254.Bn254_params.ate_loop_count
      in
      let b_lines = WT.get_all_b_lines tracker in
      let cur_hash = W.read_hash ~workdir ~n:(n - 1) in
      let cur_acc, cur_lh, cur_gv = W.read_groth16_state ~workdir ~n:(n - 1) in
      let witness : Proof_conversion.Groth16.Requests.witness =
        if n <= 6 then
          { Proof_conversion.Groth16.Requests.empty_witness with
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
            Proof_conversion.Groth16.Fupdate_circuit.iterations_per_circuit.(idx)
          in
          let g_start =
            Proof_conversion.Groth16.Fupdate_circuit.g_start_per_circuit.(idx)
          in
          let lhs = Array.sub cur_lh ~pos:0 ~len:g_start in
          let g_chunk = Array.sub cur_gv ~pos:g_start ~len:n_iters in
          let rhs_start = g_start + n_iters in
          let rhs =
            Array.sub cur_lh ~pos:rhs_start
              ~len:(Array.length cur_lh - rhs_start)
          in
          { Proof_conversion.Groth16.Requests.empty_witness with
            accumulator = Some cur_acc
          ; g_chunk = Some g_chunk
          ; lhs_hashes = Some lhs
          ; rhs_hashes = Some rhs
          }
        else if n = 13 then
          { Proof_conversion.Groth16.Requests.empty_witness with
            accumulator = Some cur_acc
          ; lhs_hashes = Some (Array.sub cur_lh ~pos:0 ~len:(n_total - 1))
          ; final_g = Some cur_gv.(Array.length cur_gv - 1)
          }
        else if n = 14 then
          let n_pi = WT.num_public_inputs tracker in
          { Proof_conversion.Groth16.Requests.empty_witness with
            public_inputs =
              Some (Array.init n_pi ~f:(fun i -> WT.get_public_input tracker i))
          }
        else
          let n_pi = WT.num_public_inputs tracker in
          let pi = WT.get_pi tracker in
          let pa = WT.get_partial_ic_acc tracker in
          let g1c (p : WT.G1.t) : Proof_conversion.Bn254.G1.Constant.t =
            { x = p.x; y = p.y }
          in
          { Proof_conversion.Groth16.Requests.empty_witness with
            public_inputs =
              Some (Array.init n_pi ~f:(fun i -> WT.get_public_input tracker i))
          ; pi_point = Some (g1c pi)
          ; partial_ic_acc = Some (g1c pa)
          }
      in
      let handler = Proof_conversion.Groth16.Requests.handler witness in
      let result_hash = ref cur_hash in
      let result_acc = ref cur_acc in
      let result_lh = ref cur_lh in
      let result_gv = ref cur_gv in
      ( if n <= 12 then (
        let body =
          Proof_conversion.Groth16.Circuits.build_circuit_body_with_acc
            ~vk:vk_const ~circuit_index:n
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
                      Step.As_prover.read
                        Proof_conversion.Groth16.Accumulator.typ acc_var ;
                    result_lh :=
                      Step.As_prover.read
                        (Step.Typ.array ~length:n_total Step.Field.typ)
                        lh_var ;
                    res_gv :=
                      Array.map gv_arr ~f:(fun g ->
                          Step.As_prover.read Proof_conversion.Bn254.Fp12.typ g ) )
                )
              handler ) ;
        if n <= 6 then (
          result_lh := !result_lh ;
          result_gv := Array.append cur_gv !res_gv )
        else result_gv := cur_gv )
      else
        let body =
          Proof_conversion.Groth16.Circuits.build_circuit_body ~vk:vk_const
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
      W.write_groth16_state ~workdir ~n ~acc:!result_acc ~line_hashes:!result_lh
        ~g_values:!result_gv ) ;
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
      let ate_loop_len = Proof_conversion.Plonk.Kzg_accumulator.ate_loop_len in
      if n <= 11 then (
        (* PLONK verification circuits 0-11: Plonk_accumulator.
           State was already pre-computed by generate-witness; only need
           to compile, prove, and export the proof + VK. *)
        let acc = W.read_plonk_state ~workdir ~n:prev in
        let w : Proof_conversion.Plonk.Requests.witness =
          { Proof_conversion.Plonk.Requests.empty_witness with
            plonk_acc = Some acc
          }
        in
        let output_hash, proof_out, side_vk =
          Proof_conversion.Plonk.Pickles_rules.compile_prove_and_export
            ~skip_verify:true ~n ~input_hash ~witness:w
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
          Proof_conversion.Groth16.Proof_json.fp12_of_json
            (Yojson.Safe.Util.member "c" aux_json)
        in
        let w : Proof_conversion.Plonk.Requests.witness =
          { Proof_conversion.Plonk.Requests.empty_witness with
            plonk_acc = Some acc
          ; shift_power = Some shift_power
          ; c_fp12 = Some c_fp12
          }
        in
        let output_hash, proof_out, side_vk =
          Proof_conversion.Plonk.Pickles_rules.compile_prove_and_export
            ~skip_verify:true ~n:12 ~input_hash ~witness:w
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
        let w : Proof_conversion.Plonk.Requests.witness =
          { Proof_conversion.Plonk.Requests.empty_witness with
            kzg_acc = Some kzg
          ; lines_hashes = Some lines_hashes
          }
        in
        let output_hash, proof_out, side_vk =
          Proof_conversion.Plonk.Pickles_rules.compile_prove_and_export
            ~skip_verify:true ~n ~input_hash ~witness:w
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
        let w : Proof_conversion.Plonk.Requests.witness =
          { Proof_conversion.Plonk.Requests.empty_witness with
            kzg_acc = Some kzg
          ; g_chunk = Some g_chunk
          ; flat_hashes = Some flat_hashes
          }
        in
        let output_hash, proof_out, side_vk =
          Proof_conversion.Plonk.Pickles_rules.compile_prove_and_export
            ~skip_verify:true ~n ~input_hash ~witness:w
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
        let w : Proof_conversion.Plonk.Requests.witness =
          { Proof_conversion.Plonk.Requests.empty_witness with
            kzg_acc = Some kzg
          ; lhs_hashes = Some lhs_hashes
          ; g_chunk = Some g_chunk
          }
        in
        let output_hash, proof_out, side_vk =
          Proof_conversion.Plonk.Pickles_rules.compile_prove_and_export
            ~skip_verify:true ~n:23 ~input_hash ~witness:w
        in
        write_base_proof ~proof_out ~side_vk ;
        W.write_hash ~workdir ~n ~hash:output_hash ;
        (* Write final KZG state unchanged for collect-output *)
        W.write_plonk_kzg_state ~workdir ~n ~kzg ~lines_hashes ~g_values )
  | W.Groth16 _ ->
      let vk_path = Filename.concat workdir "vk.json" in
      let vk = Proof_conversion.Groth16.Proof_json.load_vk vk_path in
      let vk_const = Proof_conversion.Groth16.Vk_constants.create vk in
      let proof_path = Filename.concat workdir "proof.json" in
      let proof = Proof_conversion.Groth16.Proof_json.load_proof proof_path in
      let aux =
        Proof_conversion.Groth16.Proof_json.load_aux_witness
          (Filename.concat workdir "aux_witness.json")
      in
      let module WT = Proof_conversion.Groth16.Witness_tracker in
      let tracker = WT.create ~proof ~vk ~aux in
      Proof_conversion.Groth16.Circuit_config.set_tracker tracker ;
      let acc, line_hashes, g_values = W.read_groth16_state ~workdir ~n:prev in
      let b_lines = WT.get_all_b_lines tracker in
      if n <= 6 then (
        (* Ate loop circuit *)
        let witness : Proof_conversion.Groth16.Requests.witness =
          { Proof_conversion.Groth16.Requests.empty_witness with
            accumulator = Some acc
          ; line_hashes = Some line_hashes
          ; b_lines =
              Some
                (Array.map b_lines ~f:(fun (l : WT.Line.t) ->
                     (l.lambda, l.neg_mu) ) )
          }
        in
        let output_hash, acc_after, lh_after, gv_after, proof_out, side_vk =
          Proof_conversion.Groth16.Pickles_rules
          .compile_prove_and_export_with_acc ~skip_verify:true ~vk:vk_const ~n
            ~input_hash ~witness
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
          Proof_conversion.Groth16.Fupdate_circuit.iterations_per_circuit.(idx)
        in
        let g_start =
          Proof_conversion.Groth16.Fupdate_circuit.g_start_per_circuit.(idx)
        in
        let all_lh = line_hashes in
        let lhs = Array.sub all_lh ~pos:0 ~len:g_start in
        let g_chunk = Array.sub g_values ~pos:g_start ~len:n_iters in
        let rhs_start = g_start + n_iters in
        let rhs =
          Array.sub all_lh ~pos:rhs_start ~len:(Array.length all_lh - rhs_start)
        in
        let witness : Proof_conversion.Groth16.Requests.witness =
          { Proof_conversion.Groth16.Requests.empty_witness with
            accumulator = Some acc
          ; g_chunk = Some g_chunk
          ; lhs_hashes = Some lhs
          ; rhs_hashes = Some rhs
          }
        in
        let output_hash, acc_after, _lh, _gv, proof_out, side_vk =
          Proof_conversion.Groth16.Pickles_rules
          .compile_prove_and_export_with_acc ~skip_verify:true ~vk:vk_const ~n
            ~input_hash ~witness
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
          Array.length Proof_conversion.Bn254.Bn254_params.ate_loop_count
        in
        let witness : Proof_conversion.Groth16.Requests.witness =
          match n with
          | 13 ->
              let lhs_13 = Array.sub line_hashes ~pos:0 ~len:(n_total - 1) in
              { Proof_conversion.Groth16.Requests.empty_witness with
                accumulator = Some acc
              ; lhs_hashes = Some lhs_13
              ; final_g = Some g_values.(Array.length g_values - 1)
              }
          | 14 ->
              let n_pi = WT.num_public_inputs tracker in
              let pis =
                Array.init n_pi ~f:(fun i -> WT.get_public_input tracker i)
              in
              { Proof_conversion.Groth16.Requests.empty_witness with
                public_inputs = Some pis
              }
          | 15 ->
              let n_pi = WT.num_public_inputs tracker in
              let pis =
                Array.init n_pi ~f:(fun i -> WT.get_public_input tracker i)
              in
              let pi = WT.get_pi tracker in
              let partial_acc = WT.get_partial_ic_acc tracker in
              let g1c (p : WT.G1.t) : Proof_conversion.Bn254.G1.Constant.t =
                { x = p.x; y = p.y }
              in
              { Proof_conversion.Groth16.Requests.empty_witness with
                public_inputs = Some pis
              ; pi_point = Some (g1c pi)
              ; partial_ic_acc = Some (g1c partial_acc)
              }
          | _ ->
              Proof_conversion.Groth16.Requests.empty_witness
        in
        let output_hash, proof_out, side_vk =
          Proof_conversion.Groth16.Pickles_rules.compile_prove_and_export
            ~skip_verify:true ~vk:vk_const ~n ~input_hash ~witness
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
    with exn -> Core_unix.close socket ; raise exn ) ;
  Core_unix.listen socket ~backlog:16 ;
  let running = ref true in
  while !running do
    let client_fd, _addr = Core_unix.accept socket in
    let ic = Core_unix.in_channel_of_descr client_fd in
    let oc = Core_unix.out_channel_of_descr client_fd in
    ( try
        let line = In_channel.input_line_exn ic in
        let parts = String.split line ~on:' ' in
        match parts with
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
            Out_channel.flush oc
      with exn -> (
        let msg = String.tr (Exn.to_string exn) ~target:'\n' ~replacement:' ' in
        Printf.eprintf "Compress daemon error: %s\n%!" msg ;
        try
          Out_channel.output_string oc (sprintf "ERROR %s\n" msg) ;
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
  let cmd_line = sprintf "%s %d %d %d" workdir base_count layer index in
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
  try
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
    Core_unix.close socket

(* ==== Shared orchestration utilities ==== *)

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

(** A worker's advertised capability: which base circuits and compression
    levels it has compiled (from its [.circuits] manifest). [serves_base]
    answers whether base circuit [n] can be proved on this worker. *)
type worker_cap =
  { socket : string
  ; serves_base : int -> bool
  ; serves_layer1 : bool
  ; serves_node : bool
  ; serves_tip : bool
  }

(** What a task needs from a worker, derived from its inner command. The tip
    (root of the compression tree) is its own class so it can be pinned to a
    dedicated fat worker that proves it at full core width. *)
type task_req =
  | Any_worker
  | Base_circuit of int
  | Compress_layer1
  | Compress_node
  | Compress_tip

(** The top (root) layer of the compression tree for [base_count] leaves. The
    tree is built over the next power of two, so this is [log2] of that. *)
let max_compression_layer base_count =
  let rec next_pow2 x = if x >= base_count then x else next_pow2 (x * 2) in
  let padded = next_pow2 1 in
  let rec log2 x acc = if x <= 1 then acc else log2 (x / 2) (acc + 1) in
  log2 padded 0

(** How many of the top compression layers are routed to the dedicated tip
    worker(s) (configurable via [TIP_LAYERS]; default 1 = the root only). These
    are the low-parallelism layers where fat provers fill otherwise-idle cores. *)
let tip_layers =
  match Stdlib.Sys.getenv_opt "TIP_LAYERS" with
  | Some s -> ( try Int.of_string s with _ -> 1 )
  | None -> 1

(** Derive the capability a task's inner command requires. Witness/state
    tasks run on any worker; only proving and compression are circuit-bound. *)
let task_requirement cmd =
  match
    String.split cmd ~on:' ' |> List.filter ~f:(Fn.non String.is_empty)
  with
  | "prove-zkp" :: _workdir :: n :: _ ->
      Base_circuit (Int.of_string n)
  | "compress" :: _workdir :: base_count :: layer :: _ ->
      let l = Int.of_string layer in
      let ml = max_compression_layer (Int.of_string base_count) in
      if l = 1 then Compress_layer1
      else if l >= ml - tip_layers + 1 then Compress_tip
      else Compress_node
  | _ ->
      Any_worker

let worker_serves cap = function
  | Any_worker ->
      true
  | Base_circuit n ->
      cap.serves_base n
  | Compress_layer1 ->
      cap.serves_layer1
  | Compress_node ->
      cap.serves_node
  | Compress_tip ->
      cap.serves_tip

(** Run a DAG of tasks with bounded parallelism.
    When [~worker_dispatch] is provided, tasks are dispatched to workers
    from the pool.  Each task's [cmd] is the inner command (e.g.
    "prove-zkp /tmp/w 3"); the scheduler wraps it with the dispatch-to-worker
    invocation, choosing a free worker that has compiled the relevant circuit.
    Without [~worker_dispatch], tasks are forked as shell commands. *)
let run_dag ~parallelism ?(worker_dispatch : worker_cap array option)
    (tasks : dag_task array) =
  let n = Array.length tasks in
  if n = 0 then ()
  else if parallelism <= 1 then
    (* Sequential fallback *)
    match worker_dispatch with
    | None ->
        Array.iter tasks ~f:(fun t ->
            run_cmd t.cmd ;
            t.status <- Done )
    | Some workers ->
        let self = Filename.quote Sys.argv.(0) in
        let next_worker = ref 0 in
        Array.iter tasks ~f:(fun t ->
            let worker = workers.(!next_worker mod Array.length workers) in
            incr next_worker ;
            run_cmd
              (sprintf "%s internal dispatch-to-worker %s %s" self
                 (Filename.quote worker.socket)
                 (Filename.quote t.cmd) ) ;
            t.status <- Done )
  else
    (* Parallel mode *)
    let pid_to_task : (Pid.t, int) Hashtbl.t =
      Hashtbl.create (module Pid) ~size:parallelism
    in
    (* Worker pool: tracks which workers are free.
       Only used when worker_dispatch is Some. *)
    let free_workers : worker_cap list ref = ref [] in
    let pid_to_worker : (Pid.t, worker_cap) Hashtbl.t =
      Hashtbl.create (module Pid) ~size:parallelism
    in
    ( match worker_dispatch with
    | Some workers ->
        free_workers := Array.to_list workers
    | None ->
        () ) ;
    let running = ref 0 in
    let completed = ref 0 in
    let failures = ref [] in
    (* [BASE_FIRST]: hold back every compression task until all base proofs have
       started proving, so the prove-capacity gate is never shared between base
       proofs and the compression of already-finished shards. *)
    let base_first = Option.is_some (Stdlib.Sys.getenv_opt "BASE_FIRST") in
    let is_compress_task t = String.is_prefix t.cmd ~prefix:"compress" in
    let all_base_started () =
      not
        (Array.exists tasks ~f:(fun t ->
             String.is_prefix t.cmd ~prefix:"prove-zkp"
             && match t.status with Pending -> true | _ -> false ) )
    in
    let is_ready i =
      match tasks.(i).status with
      | Pending ->
          Array.for_all tasks.(i).deps ~f:(fun d ->
              match tasks.(d).status with Done -> true | _ -> false )
          && ( (not base_first)
             || (not (is_compress_task tasks.(i)))
             || all_base_started () )
      | _ ->
          false
    in
    let start_task i worker_used =
      let cmd =
        match worker_used with
        | None ->
            tasks.(i).cmd
        | Some worker ->
            let self = Filename.quote Sys.argv.(0) in
            sprintf "%s internal dispatch-to-worker %s %s" self
              (Filename.quote worker.socket)
              (Filename.quote tasks.(i).cmd)
      in
      Printf.eprintf "  #%d starting [%d/%d] $ %s\n%!" (i + 1) !completed n cmd ;
      match Core_unix.fork () with
      | `In_the_child ->
          let exit_code = Stdlib.Sys.command cmd in
          Stdlib.exit exit_code
      | `In_the_parent pid ->
          tasks.(i).status <- Running pid ;
          Hashtbl.set pid_to_task ~key:pid ~data:i ;
          Option.iter worker_used ~f:(fun w ->
              Hashtbl.set pid_to_worker ~key:pid ~data:w ) ;
          incr running
    in
    (* Highest-priority ready task satisfying [serves], or -1 if none. *)
    let best_task_for serves =
      let best = ref (-1) in
      let best_pri = ref Int.min_value in
      for i = 0 to n - 1 do
        if is_ready i && tasks.(i).priority > !best_pri && serves i then (
          best := i ;
          best_pri := tasks.(i).priority )
      done ;
      !best
    in
    (* Fill free capacity with work. With [worker_dispatch = None] there are no
       capability constraints, so each slot runs the next-highest-priority ready
       task. With workers, we assign worker-centrically: process the free
       workers least-flexible-first (fewest serveable ready tasks) and give each
       the highest-priority ready task it can serve. This keeps every worker on
       its best feasible work without a flexible worker grabbing the only task a
       specialist could run, and never stalls a worker that has work it can do. *)
    let fill_slots () =
      let again = ref true in
      while !again && !running < parallelism do
        again := false ;
        match worker_dispatch with
        | None ->
            let best = best_task_for (fun _ -> true) in
            if best >= 0 then (
              start_task best None ;
              again := true )
        | Some _ ->
            let serveable w i =
              worker_serves w (task_requirement tasks.(i).cmd)
            in
            let flexibility w =
              let c = ref 0 in
              for i = 0 to n - 1 do
                if is_ready i && serveable w i then incr c
              done ;
              !c
            in
            let ordered =
              List.sort !free_workers ~compare:(fun a b ->
                  Int.compare (flexibility a) (flexibility b) )
            in
            let rec pick = function
              | [] ->
                  ()
              | w :: rest -> (
                  match best_task_for (serveable w) with
                  | -1 ->
                      pick rest
                  | best ->
                      free_workers :=
                        List.filter !free_workers ~f:(fun x ->
                            not (String.equal x.socket w.socket) ) ;
                      start_task best (Some w) ;
                      again := true )
            in
            pick ordered
      done
    in
    fill_slots () ;
    (* Main loop: wait for any child, mark done, start new tasks *)
    while !running > 0 do
      (* Wait for any child *)
      let pid, status = Core_unix.wait `Any in
      match Hashtbl.find pid_to_task pid with
      | Some task_idx ->
          Hashtbl.remove pid_to_task pid ;
          (* Return worker to free pool *)
          ( match Hashtbl.find_and_remove pid_to_worker pid with
          | Some w ->
              free_workers := w :: !free_workers
          | None ->
              () ) ;
          decr running ;
          ( match status with
          | Ok () ->
              tasks.(task_idx).status <- Done ;
              incr completed ;
              Printf.eprintf "  #%d completed [%d/%d]\n%!" (task_idx + 1)
                !completed n
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
          ()
    done ;
    ( if not (List.is_empty !failures) then
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

(* ==== Unified prove daemon ==== *)

(** Prove base circuit [n] using a pre-compiled prover (PLONK).
    Reads state from workdir, writes proof + VK. *)
let do_prove_zkp_plonk ~provers ~workdir ~n ~skip_verify =
  Printf.eprintf "Daemon proving plonk zkp%d in %s\n%!" n workdir ;
  let prover, side_vk, proof_module = provers.(n) in
  let prev = n - 1 in
  let input_hash = W.read_hash ~workdir ~n:prev in
  let module P = Pickles.Proof.Make (Pickles_types.Nat.N0) in
  let write_base_proof ~proof_out =
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
  let ate_loop_len = Proof_conversion.Plonk.Kzg_accumulator.ate_loop_len in
  let w : Proof_conversion.Plonk.Requests.witness =
    if n <= 11 then
      let acc = W.read_plonk_state ~workdir ~n:prev in
      { Proof_conversion.Plonk.Requests.empty_witness with
        plonk_acc = Some acc
      }
    else if n = 12 then
      let acc = W.read_plonk_state ~workdir ~n:prev in
      let aux_path = Filename.concat workdir "aux_witness.json" in
      let aux_json = Yojson.Safe.from_file aux_path in
      let shift_power =
        Step.Field.Constant.of_string
          Yojson.Safe.Util.(member "shift_power" aux_json |> to_string)
      in
      let c_fp12 =
        Proof_conversion.Groth16.Proof_json.fp12_of_json
          (Yojson.Safe.Util.member "c" aux_json)
      in
      { Proof_conversion.Plonk.Requests.empty_witness with
        plonk_acc = Some acc
      ; shift_power = Some shift_power
      ; c_fp12 = Some c_fp12
      }
    else if n <= 16 then
      let kzg, lines_hashes, _gv = W.read_plonk_kzg_state ~workdir ~n:prev in
      { Proof_conversion.Plonk.Requests.empty_witness with
        kzg_acc = Some kzg
      ; lines_hashes = Some lines_hashes
      }
    else if n <= 22 then
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
      { Proof_conversion.Plonk.Requests.empty_witness with
        kzg_acc = Some kzg
      ; g_chunk = Some g_chunk
      ; flat_hashes = Some (Array.append lhs_h rhs_h)
      }
    else (
      assert (n = 23) ;
      let kzg, lines_hashes, g_values =
        W.read_plonk_kzg_state ~workdir ~n:prev
      in
      let lhs_hashes = Array.sub lines_hashes ~pos:0 ~len:(ate_loop_len - 1) in
      let g_chunk = [| g_values.(ate_loop_len - 1) |] in
      { Proof_conversion.Plonk.Requests.empty_witness with
        kzg_acc = Some kzg
      ; lhs_hashes = Some lhs_hashes
      ; g_chunk = Some g_chunk
      } )
  in
  let output_hash, proof_out =
    Proof_conversion.Plonk.Pickles_rules.prove_with_compiled ~n ~prover
      ~proof_module ~skip_verify ~input_hash ~witness:w
  in
  write_base_proof ~proof_out ;
  W.write_hash ~workdir ~n ~hash:output_hash ;
  Printf.eprintf "Daemon proved plonk zkp%d.\n%!" n

(** Prove base circuit [n] using a pre-compiled prover (Groth16).
    Reads state from workdir, writes proof + VK. *)
let do_prove_zkp_groth16 ~provers ~workdir ~n ~skip_verify =
  Printf.eprintf "Daemon proving groth16 zkp%d in %s\n%!" n workdir ;
  let prover, side_vk, proof_module = provers.(n) in
  let prev = n - 1 in
  let input_hash = W.read_hash ~workdir ~n:prev in
  let vk_path = Filename.concat workdir "vk.json" in
  let vk = Proof_conversion.Groth16.Proof_json.load_vk vk_path in
  let proof_path = Filename.concat workdir "proof.json" in
  let proof = Proof_conversion.Groth16.Proof_json.load_proof proof_path in
  let aux =
    Proof_conversion.Groth16.Proof_json.load_aux_witness
      (Filename.concat workdir "aux_witness.json")
  in
  let module WT = Proof_conversion.Groth16.Witness_tracker in
  let tracker = WT.create ~proof ~vk ~aux in
  Proof_conversion.Groth16.Circuit_config.set_tracker tracker ;
  let acc, line_hashes, g_values = W.read_groth16_state ~workdir ~n:prev in
  let b_lines = WT.get_all_b_lines tracker in
  let n_total =
    Array.length Proof_conversion.Bn254.Bn254_params.ate_loop_count
  in
  let w : Proof_conversion.Groth16.Requests.witness =
    if n <= 6 then
      { Proof_conversion.Groth16.Requests.empty_witness with
        accumulator = Some acc
      ; line_hashes = Some line_hashes
      ; b_lines =
          Some
            (Array.map b_lines ~f:(fun (l : WT.Line.t) -> (l.lambda, l.neg_mu)))
      }
    else if n <= 12 then
      let idx = n - 7 in
      let n_iters =
        Proof_conversion.Groth16.Fupdate_circuit.iterations_per_circuit.(idx)
      in
      let g_start =
        Proof_conversion.Groth16.Fupdate_circuit.g_start_per_circuit.(idx)
      in
      let lhs = Array.sub line_hashes ~pos:0 ~len:g_start in
      let g_chunk = Array.sub g_values ~pos:g_start ~len:n_iters in
      let rhs_start = g_start + n_iters in
      let rhs =
        Array.sub line_hashes ~pos:rhs_start
          ~len:(Array.length line_hashes - rhs_start)
      in
      { Proof_conversion.Groth16.Requests.empty_witness with
        accumulator = Some acc
      ; g_chunk = Some g_chunk
      ; lhs_hashes = Some lhs
      ; rhs_hashes = Some rhs
      }
    else if n = 13 then
      let lhs_13 = Array.sub line_hashes ~pos:0 ~len:(n_total - 1) in
      { Proof_conversion.Groth16.Requests.empty_witness with
        accumulator = Some acc
      ; lhs_hashes = Some lhs_13
      ; final_g = Some g_values.(Array.length g_values - 1)
      }
    else if n = 14 then
      let n_pi = WT.num_public_inputs tracker in
      { Proof_conversion.Groth16.Requests.empty_witness with
        public_inputs =
          Some (Array.init n_pi ~f:(fun i -> WT.get_public_input tracker i))
      }
    else
      let n_pi = WT.num_public_inputs tracker in
      let pi = WT.get_pi tracker in
      let partial_acc = WT.get_partial_ic_acc tracker in
      let g1c (p : WT.G1.t) : Proof_conversion.Bn254.G1.Constant.t =
        { x = p.x; y = p.y }
      in
      { Proof_conversion.Groth16.Requests.empty_witness with
        public_inputs =
          Some (Array.init n_pi ~f:(fun i -> WT.get_public_input tracker i))
      ; pi_point = Some (g1c pi)
      ; partial_ic_acc = Some (g1c partial_acc)
      }
  in
  let output_hash, proof_out =
    Proof_conversion.Groth16.Pickles_rules.prove_with_compiled ~n ~prover
      ~proof_module ~skip_verify ~input_hash ~witness:w
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
  Printf.eprintf "Daemon proved groth16 zkp%d.\n%!" n

(** Parse a --circuits spec like "0-11,layer1,node" or "all".
    Returns (base_circuit_set option, compile_layer1, compile_node).
    None for base set means compile all base circuits. *)
let parse_circuits_spec ~base_count spec =
  if String.equal spec "all" then (None, true, true, true)
  else
    let base_set = Hash_set.create (module Int) in
    let layer1 = ref false in
    let node = ref false in
    let tip = ref false in
    let parts = String.split spec ~on:',' in
    List.iter parts ~f:(fun part ->
        let part = String.strip part in
        if String.equal part "layer1" then layer1 := true
        else if String.equal part "node" then node := true
        else if String.equal part "tip" then tip := true
        else if String.equal part "compress" then (
          layer1 := true ;
          node := true ;
          tip := true )
        else
          match String.split part ~on:'-' with
          | [ a; b ] ->
              let lo = Int.of_string a in
              let hi = Int.of_string b in
              for i = lo to hi do
                if i >= 0 && i < base_count then Hash_set.add base_set i
              done
          | [ a ] ->
              let n = Int.of_string a in
              if n >= 0 && n < base_count then Hash_set.add base_set n
          | _ ->
              failwith (sprintf "Bad --circuits component: %s" part) ) ;
    let base =
      if
        Hash_set.is_empty base_set && (not !layer1) && (not !node)
        && not !tip
      then None
      else Some base_set
    in
    (base, !layer1, !node, !tip)

(** Unified prove daemon: compiles circuits at startup (optionally a subset),
    then serves prove-zkp, compress, compute-state, generate-witness, and
    compute-aux-witness requests over a Unix domain socket.
    Circuits not pre-compiled are compiled on demand (slower but saves RAM). *)
let run_internal_prove_daemon ~socket_path ~system ~vk_path ~circuits_spec
    ~skip_verify =
  Prove_gate_native.setup ~socket_path ;
  Printf.eprintf "Prove daemon: compiling circuits for %s...\n%!" system ;
  let base_count =
    match system with "plonk" -> 24 | "groth16" -> 16 | _ -> assert false
  in
  let base_set, compile_layer1_flag, compile_node_flag =
    match circuits_spec with
    | Some spec ->
        let base, layer1, node, tip = parse_circuits_spec ~base_count spec in
        (* A tip-only worker still needs the node circuit compiled to prove the
           root merge (the tip uses the same circuit as other node layers). *)
        (base, layer1, node || tip)
    | None ->
        (None, true, true)
  in
  let should_compile_base n =
    match base_set with None -> true | Some s -> Hash_set.mem s n
  in
  (* Compile base circuits — None for circuits not in the set *)
  let base_provers =
    match system with
    | "plonk" ->
        Array.init base_count ~f:(fun n ->
            if should_compile_base n then (
              Printf.eprintf "  Compiling plonk circuit %d/%d...\n%!" (n + 1)
                base_count ;
              Some (Proof_conversion.Plonk.Pickles_rules.compile_circuit ~n) )
            else (
              Printf.eprintf "  Skipping plonk circuit %d/%d (on-demand)\n%!"
                (n + 1) base_count ;
              None ) )
    | "groth16" ->
        let vk =
          Proof_conversion.Groth16.Proof_json.load_vk
            (Option.value_exn vk_path
               ~message:"Groth16 prove-daemon requires --vk-path" )
        in
        let vk_const = Proof_conversion.Groth16.Vk_constants.create vk in
        Array.init base_count ~f:(fun n ->
            if should_compile_base n then (
              Printf.eprintf "  Compiling groth16 circuit %d/%d...\n%!" (n + 1)
                base_count ;
              Some
                (Proof_conversion.Groth16.Pickles_rules.compile_circuit
                   ~vk:vk_const ~n ) )
            else (
              Printf.eprintf "  Skipping groth16 circuit %d/%d (on-demand)\n%!"
                (n + 1) base_count ;
              None ) )
    | _ ->
        assert false
  in
  Printf.eprintf "Prove daemon: base circuits compiled.\n%!" ;
  (* Compile compression circuits (optionally) *)
  let layer1_compiled =
    if compile_layer1_flag then (
      let tag, (module Layer1Proof_), prove = TC.compile_layer1 () in
      let vk =
        Promise.block_on_async_exn (fun () ->
            Pickles.Side_loaded.Verification_key.of_compiled_promise tag )
      in
      Printf.eprintf "Prove daemon: layer1 compiled.\n%!" ;
      Some (prove, vk) )
    else (
      Printf.eprintf "Prove daemon: layer1 skipped (on-demand).\n%!" ;
      None )
  in
  let node_compiled =
    if compile_node_flag then (
      let tag, (module NodeProof_), prove = TC.compile_node () in
      let vk =
        Promise.block_on_async_exn (fun () ->
            Pickles.Side_loaded.Verification_key.of_compiled_promise tag )
      in
      Printf.eprintf "Prove daemon: node compiled.\n%!" ;
      Some (prove, vk) )
    else (
      Printf.eprintf "Prove daemon: node skipped (on-demand).\n%!" ;
      None )
  in
  Printf.eprintf "Prove daemon: compilation finished.\n%!" ;
  (* Advertise which circuits this worker can serve, so the dispatcher only
     routes a prove/compress task to a worker that has compiled the relevant
     circuit. Written before the readiness marker so a consumer that observes
     [.ready] can rely on [.circuits] already being present. *)
  Out_channel.write_all
    (socket_path ^ ".circuits")
    ~data:(Option.value circuits_spec ~default:"all") ;
  (* Write readiness marker *)
  Out_channel.write_all (socket_path ^ ".ready") ~data:"ready\n" ;
  (* Listen on socket *)
  let socket =
    Core_unix.socket ~domain:PF_UNIX ~kind:SOCK_STREAM ~protocol:0 ()
  in
  ( try Core_unix.bind socket ~addr:(ADDR_UNIX socket_path)
    with exn -> Core_unix.close socket ; raise exn ) ;
  Core_unix.listen socket ~backlog:16 ;
  Printf.eprintf "Prove daemon: listening on %s\n%!" socket_path ;
  let running = ref true in
  while !running do
    let client_fd, _addr = Core_unix.accept socket in
    let ic = Core_unix.in_channel_of_descr client_fd in
    let oc = Core_unix.out_channel_of_descr client_fd in
    ( try
        let line = In_channel.input_line_exn ic in
        let parts = String.split line ~on:' ' in
        match parts with
        | [ "shutdown" ] ->
            Out_channel.output_string oc "OK\n" ;
            Out_channel.flush oc ;
            running := false
        | [ "prove-zkp"; workdir; n_str ] ->
            let n = Int.of_string n_str in
            ( match base_provers.(n) with
            | Some (prover, side_vk, proof_module) -> (
                (* Use pre-compiled prover *)
                let provers_for_n =
                  (* Build a single-use array with the compiled prover at
                     index n — do_prove_zkp only accesses provers.(n). *)
                  let a =
                    Array.create ~len:(n + 1) (prover, side_vk, proof_module)
                  in
                  a
                in
                match system with
                | "plonk" ->
                    do_prove_zkp_plonk ~provers:provers_for_n ~workdir ~n
                      ~skip_verify
                | "groth16" ->
                    do_prove_zkp_groth16 ~provers:provers_for_n ~workdir ~n
                      ~skip_verify
                | _ ->
                    assert false )
            | None ->
                (* Circuit not pre-compiled — compile on demand *)
                Printf.eprintf
                  "  prove-zkp %d: not pre-compiled, compiling on demand\n%!" n ;
                run_internal_prove_zkp ~workdir ~n ) ;
            Out_channel.output_string oc "OK\n" ;
            Out_channel.flush oc
        | [ "compress"; workdir; base_count_s; layer_s; index_s ] ->
            (* Get compression provers — compile on demand if needed *)
            let layer1_prove, layer1_vk =
              match layer1_compiled with
              | Some (p, v) ->
                  (p, v)
              | None ->
                  Printf.eprintf
                    "  compress: layer1 not pre-compiled, compiling on demand\n\
                     %!" ;
                  let tag, (module L1P_), prove = TC.compile_layer1 () in
                  let vk =
                    Promise.block_on_async_exn (fun () ->
                        Pickles.Side_loaded.Verification_key.of_compiled_promise
                          tag )
                  in
                  (prove, vk)
            in
            let node_prove, node_vk =
              match node_compiled with
              | Some (p, v) ->
                  (p, v)
              | None ->
                  Printf.eprintf
                    "  compress: node not pre-compiled, compiling on demand\n%!" ;
                  let tag, (module NP_), prove = TC.compile_node () in
                  let vk =
                    Promise.block_on_async_exn (fun () ->
                        Pickles.Side_loaded.Verification_key.of_compiled_promise
                          tag )
                  in
                  (prove, vk)
            in
            do_compress ~layer1_prove ~layer1_vk ~node_prove ~node_vk ~workdir
              ~base_count:(Int.of_string base_count_s)
              ~layer:(Int.of_string layer_s) ~index:(Int.of_string index_s) ;
            Out_channel.output_string oc "OK\n" ;
            Out_channel.flush oc
        | [ "compute-state"; workdir; n_str ] ->
            run_internal_compute_state ~workdir ~n:(Int.of_string n_str) ;
            Out_channel.output_string oc "OK\n" ;
            Out_channel.flush oc
        | [ "compute-aux-witness"; workdir ] ->
            run_internal_compute_aux_witness ~workdir ;
            Out_channel.output_string oc "OK\n" ;
            Out_channel.flush oc
        | [ "generate-witness"; workdir ] ->
            run_internal_generate_witness ~workdir ;
            Out_channel.output_string oc "OK\n" ;
            Out_channel.flush oc
        | _ ->
            Out_channel.output_string oc
              (sprintf "ERROR bad command: %s\n" line) ;
            Out_channel.flush oc
      with exn -> (
        let msg = String.tr (Exn.to_string exn) ~target:'\n' ~replacement:' ' in
        Printf.eprintf "Prove daemon error: %s\n%!" msg ;
        try
          Out_channel.output_string oc (sprintf "ERROR %s\n" msg) ;
          Out_channel.flush oc
        with _ -> () ) ) ;
    Core_unix.close client_fd
  done ;
  Core_unix.close socket ;
  (try Stdlib.Sys.remove (socket_path ^ ".ready") with _ -> ()) ;
  (try Stdlib.Sys.remove (socket_path ^ ".circuits") with _ -> ()) ;
  Printf.eprintf "Prove daemon: shutdown.\n%!"

(** Send a command to a worker daemon via Unix socket.
    Connects with retry, sends the command, waits for OK. *)
let run_internal_dispatch_to_worker ~socket_path ~command =
  let socket =
    Core_unix.socket ~domain:PF_UNIX ~kind:SOCK_STREAM ~protocol:0 ()
  in
  let rec connect_retry attempts =
    try Core_unix.connect socket ~addr:(ADDR_UNIX socket_path)
    with Core_unix.Unix_error ((ENOENT | ECONNREFUSED), _, _) ->
      if attempts <= 0 then
        failwith
          (sprintf "dispatch-to-worker: could not connect to %s" socket_path)
      else (
        ignore (Core_unix.nanosleep 0.2 : float) ;
        connect_retry (attempts - 1) )
  in
  connect_retry 3000 (* 10 minutes for initial compilation *) ;
  let oc = Core_unix.out_channel_of_descr socket in
  let ic = Core_unix.in_channel_of_descr socket in
  Out_channel.output_string oc (command ^ "\n") ;
  Out_channel.flush oc ;
  let response = In_channel.input_line_exn ic in
  Core_unix.close socket ;
  if not (String.is_prefix response ~prefix:"OK") then
    failwith (sprintf "dispatch-to-worker failed: %s" response)

(** Discover worker sockets in a directory. *)
let discover_workers ~base_count ~socket_dir =
  let entries = Stdlib.Sys.readdir socket_dir in
  let sockets =
    Array.filter entries ~f:(fun name ->
        String.is_suffix name ~suffix:".sock"
        && not (String.is_suffix name ~suffix:".ready") )
  in
  Array.sort sockets ~compare:String.compare ;
  Array.map sockets ~f:(fun name ->
      let socket = Filename.concat socket_dir name in
      (* Read the worker's advertised circuit set; a missing manifest (e.g. an
         older worker) is treated as "all" so it can serve anything. *)
      let spec =
        let manifest = socket ^ ".circuits" in
        if Stdlib.Sys.file_exists manifest then
          String.strip (In_channel.read_all manifest)
        else "all"
      in
      let base_set, layer1, node, tip = parse_circuits_spec ~base_count spec in
      { socket
      ; serves_base =
          (fun n ->
            match base_set with None -> true | Some s -> Hash_set.mem s n )
      ; serves_layer1 = layer1
      ; serves_node = node
      ; serves_tip = tip
      } )

(** Run a proof conversion using pre-started worker daemons.
    Same DAG structure as [run_parallel_pipeline] but dispatches to
    workers via socket instead of forking subprocesses. *)
let run_daemonised_pipeline ~cache_dir:_ ~worker_sockets ~system ~base_count
    ~max_layer ~input_path ~vk_path =
  let n_workers = Array.length worker_sockets in
  if n_workers = 0 then failwith "No workers found" ;
  Printf.eprintf "Daemonised pipeline: %d workers, system=%s\n%!" n_workers
    system ;
  (* Create temp working directory *)
  let workdir =
    let base = Filename.temp_dir_name in
    let name =
      sprintf "nori-%s-%d" system (Core_unix.getpid () |> Pid.to_int)
    in
    Filename.concat base name
  in
  Printf.eprintf "Working directory: %s\n%!" workdir ;
  (* init-workdir (local, fast) *)
  let self = Filename.quote Sys.argv.(0) in
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
  (* Build DAG — same structure as parallel pipeline but dispatching
     to workers. *)
  let padded_count =
    let rec next_pow2 x = if x >= base_count then x else next_pow2 (x * 2) in
    next_pow2 1
  in
  if padded_count > base_count then
    Printf.eprintf "Padding %d → %d for binary tree\n%!" base_count padded_count ;
  let compression_counts =
    Array.init max_layer ~f:(fun i ->
        let layer = i + 1 in
        let prev_count =
          if layer = 1 then padded_count
          else padded_count / Int.pow 2 (layer - 1)
        in
        prev_count / 2 )
  in
  let total_compression = Array.fold compression_counts ~init:0 ~f:( + ) in
  let total_tasks = 2 + base_count + base_count + total_compression in
  let gw_idx = 0 in
  let aux_idx = 1 in
  let cs_start = 2 in
  let prove_start = 2 + base_count in
  let compress_start = 2 + (2 * base_count) in
  let aux_needed_at = match system with "plonk" -> Some 12 | _ -> None in
  Printf.eprintf "Building DAG: %d tasks, dispatching to %d workers\n%!"
    total_tasks n_workers ;
  let tasks =
    Array.create ~len:total_tasks
      { cmd = ""; deps = [||]; priority = 0; status = Pending }
  in
  (* Tasks store inner commands (no worker assignment).
     The DAG scheduler assigns workers dynamically via ~worker_dispatch. *)
  tasks.(gw_idx) <-
    { cmd = sprintf "generate-witness %s" workdir
    ; deps = [||]
    ; priority = 1
    ; status = Pending
    } ;
  let aux_deps_d =
    match system with "plonk" -> [| cs_start + 11 |] | _ -> [| gw_idx |]
  in
  tasks.(aux_idx) <-
    { cmd = sprintf "compute-aux-witness %s" workdir
    ; deps = aux_deps_d
    ; priority = 1
    ; status = Pending
    } ;
  for n = 0 to base_count - 1 do
    let deps =
      if n = 0 then [| gw_idx |]
      else
        match aux_needed_at with
        | Some k when n = k ->
            [| cs_start + n - 1; aux_idx |]
        | _ ->
            [| cs_start + n - 1 |]
    in
    tasks.(cs_start + n) <-
      { cmd = sprintf "compute-state %s %d" workdir n
      ; deps
      ; priority = 2
      ; status = Pending
      }
  done ;
  for n = 0 to base_count - 1 do
    tasks.(prove_start + n) <-
      { cmd = sprintf "prove-zkp %s %d" workdir n
      ; deps = [| cs_start + n |]
      ; priority = 1
      ; status = Pending
      }
  done ;
  (* Compression tasks *)
  let layer_start = Array.create ~len:(max_layer + 1) 0 in
  layer_start.(0) <- prove_start ;
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
        { cmd = sprintf "compress %s %d %d %d" workdir base_count layer index
        ; deps
        ; priority = 0
        ; status = Pending
        } ;
      incr task_idx
    done
  done ;
  assert (!task_idx = total_tasks) ;
  run_dag ~parallelism:n_workers ~worker_dispatch:worker_sockets tasks ;
  (* Collect output (local) *)
  run_cmd
    (sprintf "%s internal collect-output %s" self (Filename.quote workdir)) ;
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

(** Start N worker daemons. *)
let run_start_workers ~system ~count ~socket_dir ~vk_path ~circuits_spec
    ~skip_verify ~background ~start_index =
  Core_unix.mkdir_p socket_dir ;
  (* The on-disk worker index, so several start-workers invocations can share
     one socket directory (e.g. heterogeneous shards holding disjoint circuit
     sets) without clobbering each other's sockets. *)
  let widx i = start_index + i in
  let pids =
    Array.init count ~f:(fun i ->
        let socket_path =
          Filename.concat socket_dir (sprintf "worker.%d.sock" (widx i))
        in
        (* Clean up stale socket/ready files *)
        (try Stdlib.Sys.remove socket_path with _ -> ()) ;
        (try Stdlib.Sys.remove (socket_path ^ ".ready") with _ -> ()) ;
        (try Stdlib.Sys.remove (socket_path ^ ".circuits") with _ -> ()) ;
        match Core_unix.fork () with
        | `In_the_child ->
            run_internal_prove_daemon ~socket_path ~system ~vk_path
              ~circuits_spec ~skip_verify ;
            Stdlib.exit 0
        | `In_the_parent pid ->
            Printf.eprintf "  Worker %d started (pid %d)\n%!" (widx i)
              (Pid.to_int pid) ;
            pid )
  in
  (* Wait for all workers to be ready *)
  let all_ready () =
    Array.for_all
      (Array.init count ~f:(fun i ->
           Stdlib.Sys.file_exists
             (Filename.concat socket_dir
                (sprintf "worker.%d.sock.ready" (widx i)) ) ) )
      ~f:Fn.id
  in
  Printf.eprintf "Waiting for %d workers to compile circuits...\n%!" count ;
  while not (all_ready ()) do
    ignore (Core_unix.nanosleep 1.0 : float)
  done ;
  Printf.eprintf "All %d workers ready in %s\n%!" count socket_dir ;
  if background then
    (* Print PIDs and exit *)
    Array.iteri pids ~f:(fun i pid ->
        Printf.eprintf "  worker.%d: pid %d, socket %s\n%!" (widx i)
          (Pid.to_int pid)
          (Filename.concat socket_dir (sprintf "worker.%d.sock" (widx i))) )
  else
    (* Foreground: wait for SIGINT, then shut down *)
    let interrupted = ref false in
    let handle_signal _ = interrupted := true in
    Stdlib.Sys.set_signal Stdlib.Sys.sigint (Signal_handle handle_signal) ;
    Stdlib.Sys.set_signal Stdlib.Sys.sigterm (Signal_handle handle_signal) ;
    Printf.eprintf "Workers running. Press Ctrl-C to stop.\n%!" ;
    while not !interrupted do
      ignore (Core_unix.nanosleep 1.0 : float)
    done ;
    Printf.eprintf "Shutting down workers...\n%!" ;
    Array.iteri
      (Array.init count ~f:(fun i ->
           Filename.concat socket_dir (sprintf "worker.%d.sock" (widx i)) ) )
      ~f:(fun _i sp -> shutdown_compress_daemon ~socket_path:sp) ;
    Array.iter pids ~f:(fun pid ->
        try ignore (Core_unix.waitpid pid : Core.Unix.Exit_or_signal.t)
        with _ -> () ) ;
    Printf.eprintf "All workers shut down.\n%!"

(** Stop all workers in a socket directory. *)
let run_stop_workers ~socket_dir =
  let entries = Stdlib.Sys.readdir socket_dir in
  Array.iter entries ~f:(fun name ->
      if
        String.is_suffix name ~suffix:".sock"
        && not (String.is_suffix name ~suffix:".sock.ready")
      then (
        Printf.eprintf "Stopping %s...\n%!" name ;
        shutdown_compress_daemon ~socket_path:(Filename.concat socket_dir name)
        ) ) ;
  Printf.eprintf "All workers stopped.\n%!"

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
let run_parallel_pipeline ~cache_dir ~parallelism ~compress_parallelism ~system
    ~base_count ~max_layer ~input_path ~vk_path =
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
  (* Fork compression daemons early so circuit compilation overlaps with
     witness generation.  Each daemon compiles both circuits independently
     and listens on its own Unix socket. *)
  let n_daemons = compress_parallelism in
  let socket_paths =
    Array.init n_daemons ~f:(fun i ->
        Filename.concat workdir (sprintf "compress.%d.sock" i) )
  in
  let daemon_pids =
    Array.map socket_paths ~f:(fun socket_path ->
        match Core_unix.fork () with
        | `In_the_child ->
            run_internal_compress_daemon ~socket_path ;
            Stdlib.exit 0
        | `In_the_parent pid ->
            pid )
  in
  Printf.eprintf "Started %d compress daemon(s), compiling in background\n%!"
    n_daemons ;
  (* Build the DAG.  generate-witness (fast: parse input, write initial
     state) and compute-aux-witness (slow: Miller loop for PLONK aux)
     are separate tasks so that compute-state 0..11 can start as soon as
     generate-witness finishes, while the expensive aux computation runs
     in parallel.  Only compute-state 12 needs the aux witness.

     Task layout (indices):
       0                                    : generate-witness
       1                                    : compute-aux-witness
       2 .. base_count+1                    : compute-state 0..N-1
       base_count+2 .. 2*base_count+1       : prove-zkp 0..N-1
       2*base_count+2 ..                    : compression tasks

     Dependencies:
       generate-witness      : (none)
       compute-aux-witness   : compute-state 11  (reads KZG points from state 11)
       compute-state 0       : generate-witness
       compute-state n>0     : compute-state n-1
       compute-state 12      : compute-aux-witness  (which transitively includes compute-state 11)
       prove-zkp n           : compute-state n
       compress layer=1, i   : prove-zkp 2i, prove-zkp 2i+1
       compress layer>1, i   : compress prev_layer 2i, compress prev_layer 2i+1 *)
  let padded_count =
    let rec next_pow2 x = if x >= base_count then x else next_pow2 (x * 2) in
    next_pow2 1
  in
  if padded_count > base_count then
    Printf.eprintf "Padding %d → %d for binary tree\n%!" base_count padded_count ;
  let compression_counts =
    Array.init max_layer ~f:(fun i ->
        let layer = i + 1 in
        let prev_count =
          if layer = 1 then padded_count
          else padded_count / Int.pow 2 (layer - 1)
        in
        prev_count / 2 )
  in
  let total_compression = Array.fold compression_counts ~init:0 ~f:( + ) in
  (* gw + aux + compute-state + prove-zkp + compression *)
  let total_tasks = 2 + base_count + base_count + total_compression in
  let gw_idx = 0 in
  (* generate-witness *)
  let aux_idx = 1 in
  (* compute-aux-witness *)
  let cs_start = 2 in
  (* compute-state tasks *)
  let prove_start = 2 + base_count in
  (* prove-zkp tasks *)
  let compress_start = 2 + (2 * base_count) in
  (* compression tasks *)
  (* For PLONK, compute-state 12 is the transition circuit that needs
     aux_witness.json.  For Groth16, aux is computed inside generate-witness
     so no extra dependency is needed. *)
  let aux_needed_at = match system with "plonk" -> Some 12 | _ -> None in
  Printf.eprintf
    "Building DAG: 1 generate-witness + 1 compute-aux-witness + %d \
     compute-state + %d prove-zkp + %d compression = %d tasks (parallelism=%d)\n\
     %!"
    base_count base_count total_compression total_tasks parallelism ;
  let tasks =
    Array.create ~len:total_tasks
      { cmd = ""; deps = [||]; priority = 0; status = Pending }
  in
  (* generate-witness: high priority, no deps — fast for PLONK (just
     parse + write initial state), runs in parallel with daemon compile *)
  tasks.(gw_idx) <-
    { cmd =
        sprintf "%s internal generate-witness %s" self (Filename.quote workdir)
    ; deps = [||]
    ; priority = 1
    ; status = Pending
    } ;
  (* compute-aux-witness: depends on compute-state 11 (PLONK) so it can
     read the accumulated KZG points instead of re-running circuits 0-11.
     For Groth16, aux is computed in generate-witness so this is a no-op. *)
  let aux_deps =
    match system with "plonk" -> [| cs_start + 11 |] | _ -> [| gw_idx |]
  in
  tasks.(aux_idx) <-
    { cmd =
        sprintf "%s internal compute-aux-witness %s" self
          (Filename.quote workdir)
    ; deps = aux_deps
    ; priority = 1
    ; status = Pending
    } ;
  (* compute-state tasks: sequential chain, high priority — gates all
     proving so must not be starved by leaf proofs.
     compute-state 0 depends on generate-witness.
     compute-state at aux_needed_at also depends on compute-aux-witness. *)
  for n = 0 to base_count - 1 do
    let deps =
      if n = 0 then [| gw_idx |]
      else
        match aux_needed_at with
        | Some k when n = k ->
            [| cs_start + n - 1; aux_idx |]
        | _ ->
            [| cs_start + n - 1 |]
    in
    tasks.(cs_start + n) <-
      { cmd =
          sprintf "%s internal compute-state %s %d" self
            (Filename.quote workdir) n
      ; deps
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
  layer_start.(0) <- prove_start ;
  (* layer 0 = prove-zkp tasks *)
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
      let compress_task_num = !task_idx - compress_start in
      let daemon_idx = compress_task_num % n_daemons in
      tasks.(!task_idx) <-
        { cmd =
            sprintf "%s internal compress-via-daemon %s %s %d %d %d" self
              (Filename.quote socket_paths.(daemon_idx))
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
  (* Shut down all compression daemons *)
  Array.iter socket_paths ~f:(fun sp ->
      shutdown_compress_daemon ~socket_path:sp ) ;
  Array.iter daemon_pids ~f:(fun pid ->
      try
        match Core_unix.waitpid pid with
        | Ok () ->
            ()
        | Error _ ->
            Printf.eprintf "Warning: compress daemon %d exited abnormally.\n%!"
              (Pid.to_int pid)
      with Core_unix.Unix_error (ECHILD, _, _) ->
        (* Already reaped by the DAG scheduler's wait(`Any) *)
        () ) ;
  Printf.eprintf "All compress daemons shut down.\n%!" ;
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
  (* Extract options before command dispatch *)
  let argv = Array.to_list Sys.argv in
  let cache_dir, parallelism, compress_parallelism, argv =
    let rec extract ~cd ~par ~cpar acc = function
      | "--cache-dir" :: dir :: rest ->
          extract ~cd:(Some dir) ~par ~cpar acc rest
      | "--parallelism" :: n :: rest ->
          extract ~cd ~par:(Some (Int.of_string n)) ~cpar acc rest
      | "--compression-parallelism" :: n :: rest ->
          extract ~cd ~par ~cpar:(Some (Int.of_string n)) acc rest
      | x :: rest ->
          extract ~cd ~par ~cpar (x :: acc) rest
      | [] ->
          (cd, par, cpar, List.rev acc)
    in
    extract ~cd:None ~par:None ~cpar:None [] argv
  in
  let parallelism = Option.value parallelism ~default:1 in
  let compress_parallelism = Option.value compress_parallelism ~default:1 in
  ( match cache_dir with
  | Some dir ->
      Printf.eprintf "Using cache directory: %s\n%!" dir ;
      let () = Key_cache_native.linkme in
      Core_unix.mkdir_p dir ;
      Proof_conversion.Circuit_kit.Cache_config.set_cache_dir dir
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
      run_parallel_pipeline ~cache_dir ~parallelism ~compress_parallelism
        ~system:"plonk" ~base_count:24 ~max_layer:5 ~input_path ~vk_path:None
  | [| _; "risc0ToGroth16Parallel"; proof_path; vk_path |] ->
      run_parallel_pipeline ~cache_dir ~parallelism ~compress_parallelism
        ~system:"groth16" ~base_count:16 ~max_layer:4 ~input_path:proof_path
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
  | [| _; "internal"; "compute-aux-witness"; workdir |] ->
      run_internal_compute_aux_witness ~workdir
  | [| _; "internal"; "compute-state"; workdir; n_str |] ->
      run_internal_compute_state ~workdir ~n:(Int.of_string n_str)
  | [| _; "internal"; "prove-zkp"; workdir; n_str |] ->
      run_internal_prove_zkp ~workdir ~n:(Int.of_string n_str)
  | [| _; "internal"; "compress"; workdir; base_count; layer; index |] ->
      run_internal_compress ~workdir ~base_count:(Int.of_string base_count)
        ~layer:(Int.of_string layer) ~index:(Int.of_string index)
  | [| _; "internal"; "compress-daemon"; socket_path |] ->
      run_internal_compress_daemon ~socket_path
  | [| _
     ; "internal"
     ; "compress-via-daemon"
     ; socket_path
     ; workdir
     ; base_count
     ; layer
     ; index
    |] ->
      run_internal_compress_via_daemon ~socket_path ~workdir
        ~base_count:(Int.of_string base_count) ~layer:(Int.of_string layer)
        ~index:(Int.of_string index)
  | [| _; "internal"; "collect-output"; workdir |] ->
      run_internal_collect_output ~workdir
  | [| _; "internal"; "prove-daemon"; socket_path; "--system"; system |] ->
      run_internal_prove_daemon ~socket_path ~system ~vk_path:None
        ~circuits_spec:None ~skip_verify:false
  | [| _
     ; "internal"
     ; "prove-daemon"
     ; socket_path
     ; "--system"
     ; system
     ; "--vk-path"
     ; vk_p
    |] ->
      run_internal_prove_daemon ~socket_path ~system ~vk_path:(Some vk_p)
        ~circuits_spec:None ~skip_verify:false
  | [| _; "internal"; "dispatch-to-worker"; socket_path; command |] ->
      run_internal_dispatch_to_worker ~socket_path ~command
  | _
    when Array.length argv >= 2 && String.equal argv.(1) "sp1ToPlonkDaemonised"
    ->
      let input_path = argv.(2) in
      let worker_sockets =
        let workers_dir = ref "" in
        Array.iter argv ~f:(fun arg ->
            if String.is_prefix arg ~prefix:"--workers=" then
              workers_dir := String.chop_prefix_exn arg ~prefix:"--workers="
            else if String.equal !workers_dir "" && String.equal arg "--workers"
            then ()
            else () ) ;
        (* Look for --workers in argv *)
        let rec find_workers = function
          | "--workers" :: dir :: _ ->
              dir
          | _ :: rest ->
              find_workers rest
          | [] ->
              failwith "Missing --workers <socket-dir>"
        in
        let dir = find_workers (Array.to_list argv) in
        discover_workers ~base_count:24 ~socket_dir:dir
      in
      run_daemonised_pipeline ~cache_dir ~worker_sockets ~system:"plonk"
        ~base_count:24 ~max_layer:5 ~input_path ~vk_path:None
  | _
    when Array.length argv >= 3
         && String.equal argv.(1) "risc0ToGroth16Daemonised" ->
      let proof_path = argv.(2) in
      let vk_p = argv.(3) in
      let worker_sockets =
        let rec find_workers = function
          | "--workers" :: dir :: _ ->
              dir
          | _ :: rest ->
              find_workers rest
          | [] ->
              failwith "Missing --workers <socket-dir>"
        in
        let dir = find_workers (Array.to_list argv) in
        discover_workers ~base_count:16 ~socket_dir:dir
      in
      run_daemonised_pipeline ~cache_dir ~worker_sockets ~system:"groth16"
        ~base_count:16 ~max_layer:4 ~input_path:proof_path ~vk_path:(Some vk_p)
  | _ when Array.length argv >= 2 && String.equal argv.(1) "start-workers" ->
      let args = Array.to_list argv in
      let rec parse ~system ~count ~socket_dir ~vk_p ~circuits ~sv ~bg ~si =
        function
        | "--system" :: s :: rest ->
            parse ~system:(Some s) ~count ~socket_dir ~vk_p ~circuits ~sv ~bg ~si
              rest
        | "--count" :: n :: rest ->
            parse ~system
              ~count:(Some (Int.of_string n))
              ~socket_dir ~vk_p ~circuits ~sv ~bg ~si rest
        | "--socket-dir" :: d :: rest ->
            parse ~system ~count ~socket_dir:(Some d) ~vk_p ~circuits ~sv ~bg ~si
              rest
        | "--vk-path" :: p :: rest ->
            parse ~system ~count ~socket_dir ~vk_p:(Some p) ~circuits ~sv ~bg ~si
              rest
        | "--circuits" :: c :: rest ->
            parse ~system ~count ~socket_dir ~vk_p ~circuits:(Some c) ~sv ~bg ~si
              rest
        | "--start-index" :: n :: rest ->
            parse ~system ~count ~socket_dir ~vk_p ~circuits ~sv ~bg
              ~si:(Int.of_string n) rest
        | "--background" :: rest ->
            parse ~system ~count ~socket_dir ~vk_p ~circuits ~sv ~bg:true ~si
              rest
        | "--skip-verify" :: rest ->
            parse ~system ~count ~socket_dir ~vk_p ~circuits ~sv:true ~bg ~si
              rest
        | _ :: rest ->
            parse ~system ~count ~socket_dir ~vk_p ~circuits ~sv ~bg ~si rest
        | [] ->
            (system, count, socket_dir, vk_p, circuits, sv, bg, si)
      in
      let ( system
          , count
          , socket_dir
          , vk_p
          , circuits_spec
          , skip_verify
          , background
          , start_index ) =
        parse ~system:None ~count:None ~socket_dir:None ~vk_p:None
          ~circuits:None ~sv:false ~bg:false ~si:0 args
      in
      let system =
        Option.value_exn system ~message:"start-workers requires --system"
      in
      let count =
        Option.value_exn count ~message:"start-workers requires --count"
      in
      let socket_dir =
        Option.value_exn socket_dir
          ~message:"start-workers requires --socket-dir"
      in
      run_start_workers ~system ~count ~socket_dir ~vk_path:vk_p ~circuits_spec
        ~skip_verify ~background ~start_index
  | _ when Array.length argv >= 2 && String.equal argv.(1) "stop-workers" ->
      let rec find_socket_dir = function
        | "--socket-dir" :: d :: _ ->
            d
        | _ :: rest ->
            find_socket_dir rest
        | [] ->
            failwith "stop-workers requires --socket-dir"
      in
      let socket_dir = find_socket_dir (Array.to_list argv) in
      run_stop_workers ~socket_dir
  | _ ->
      Printf.eprintf
        "Usage: nori-proof-converter [options] <command> [args...]\n\n" ;
      Printf.eprintf "Conversion commands:\n" ;
      Printf.eprintf "  sp1ToPlonk <input.json> [aux.json]\n" ;
      Printf.eprintf "  risc0ToGroth16 <proof.json> <vk.json>\n\n" ;
      Printf.eprintf "Parallel commands:\n" ;
      Printf.eprintf "  sp1ToPlonkParallel <input.json>\n" ;
      Printf.eprintf "  risc0ToGroth16Parallel <proof.json> <vk.json>\n\n" ;
      Printf.eprintf "Daemonised commands:\n" ;
      Printf.eprintf
        "  sp1ToPlonkDaemonised <input.json> --workers <socket-dir>\n" ;
      Printf.eprintf
        "  risc0ToGroth16Daemonised <proof.json> <vk.json> --workers \
         <socket-dir>\n\n" ;
      Printf.eprintf "Worker management:\n" ;
      Printf.eprintf
        "  start-workers --system <system> --count <n> --socket-dir <dir>\n\
        \                [--vk-path <path>] [--circuits <spec>] [--background]\n\
        \                [--skip-verify] [--start-index <n>]\n" ;
      Printf.eprintf "  stop-workers --socket-dir <dir>\n\n" ;
      Printf.eprintf "Internal commands (for staged/parallel execution):\n" ;
      Printf.eprintf "  internal init-workdir <workdir> plonk <input.json>\n" ;
      Printf.eprintf
        "  internal init-workdir <workdir> groth16 <proof.json> <vk.json>\n" ;
      Printf.eprintf "  internal generate-witness <workdir>\n" ;
      Printf.eprintf "  internal compute-aux-witness <workdir>\n" ;
      Printf.eprintf "  internal compute-state <workdir> <n>\n" ;
      Printf.eprintf "  internal prove-zkp <workdir> <n>\n" ;
      Printf.eprintf
        "  internal compress <workdir> <base_count> <layer> <index>\n" ;
      Printf.eprintf "  internal compress-daemon <socket_path>\n" ;
      Printf.eprintf
        "  internal compress-via-daemon <socket_path> <workdir> <base_count> \
         <layer> <index>\n" ;
      Printf.eprintf "  internal collect-output <workdir>\n" ;
      Printf.eprintf
        "  internal prove-daemon <socket_path> --system <system> [--vk-path \
         <path>]\n" ;
      Printf.eprintf "  internal dispatch-to-worker <socket_path> <command>\n\n" ;
      Printf.eprintf "Options:\n" ;
      Printf.eprintf
        "  --cache-dir <dir>     Cache proving keys to disk for reuse\n" ;
      Printf.eprintf
        "  --parallelism <n>     Max parallel processes (default: 1)\n" ;
      Printf.eprintf
        "  --compression-parallelism <n>\n\
        \                        Number of compression daemons (default: 1)\n\n" ;
      Printf.eprintf "Environment variables:\n" ;
      Printf.eprintf
        "  RAYON_NUM_THREADS     Limit the number of cores each worker uses\n" ;
      exit 1
