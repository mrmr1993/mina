(** Compare: tracker f vs circuit-chained f after 64 iterations. *)
open Core_kernel
module Step = Pickles.Impls.Step
module WT = Proof_conversion.Witness_tracker

let () =
  Printf.eprintf "=== Compare tracker f vs circuit-chained f ===\n%!" ;
  let proof = Proof_conversion.Proof_json.load_proof "/tmp/groth16_test/proof.json" in
  let vk = Proof_conversion.Proof_json.load_vk "/tmp/groth16_test/vk.json" in
  let aux = Proof_conversion.Proof_json.load_aux_witness "/tmp/groth16_test/aux_witness.json" in
  let tracker = WT.create ~proof ~vk ~aux in
  Proof_conversion.Circuit_config.set_tracker tracker ;
  let vk_const = Proof_conversion.Vk_constants.create vk in
  let n_total = Array.length Proof_conversion.Bn254_params.ate_loop_count in
  let initial_g_digest =
    let zeros = Array.create ~len:n_total Step.Field.Constant.zero in
    Random_oracle.hash zeros
  in
  let initial_acc = WT.get_accumulator_constant tracker in
  let initial_acc =
    { initial_acc with
      state =
        { g_digest = initial_g_digest
        ; t_point = initial_acc.proof.b
        ; f = Proof_conversion.Fp12.Constant.one
        }
    }
  in
  let initial_hash =
    Step.run_and_check_exn (fun () ->
        let acc = Step.exists Proof_conversion.Accumulator.typ ~compute:(fun () -> initial_acc) in
        let h = Proof_conversion.Accumulator.hash acc in
        fun () -> Step.As_prover.read_var h )
  in
  let b_lines = WT.get_all_b_lines tracker in
  let evolving_lh = ref (Array.create ~len:n_total Step.Field.Constant.zero) in
  let all_g_values = ref [||] in
  let current_hash = ref initial_hash in
  let current_acc = ref initial_acc in
  for n = 0 to 12 do
    Printf.eprintf "  Circuit %d...\n%!" n ;
    let witness : Proof_conversion.Groth16_requests.witness =
      if n <= 6 then
        { Proof_conversion.Groth16_requests.empty_witness with
          accumulator = Some !current_acc
        ; line_hashes = Some !evolving_lh
        ; b_lines = Some (Array.map b_lines ~f:(fun (l : WT.Line.t) -> (l.lambda, l.neg_mu)))
        }
      else
        let idx = n - 7 in
        let n_iters = Proof_conversion.Fupdate_circuit.iterations_per_circuit.(idx) in
        let g_start = Proof_conversion.Fupdate_circuit.g_start_per_circuit.(idx) in
        let all_lh = !evolving_lh in
        let lhs = Array.sub all_lh ~pos:0 ~len:g_start in
        let g_chunk = Array.sub !all_g_values ~pos:g_start ~len:n_iters in
        let rhs_start = g_start + n_iters in
        let rhs = Array.sub all_lh ~pos:rhs_start ~len:(Array.length all_lh - rhs_start) in
        { Proof_conversion.Groth16_requests.empty_witness with
          accumulator = Some !current_acc
        ; g_chunk = Some g_chunk
        ; lhs_hashes = Some lhs
        ; rhs_hashes = Some rhs
        }
    in
    let output_hash, acc_after, lh_after, gv_after, _proof =
      Proof_conversion.Pickles_rules.compile_and_prove_one_with_acc
        ~vk:vk_const ~n ~input_hash:!current_hash ~witness
    in
    current_hash := output_hash ;
    current_acc := acc_after ;
    if n <= 6 then (
      evolving_lh := lh_after ;
      all_g_values := Array.append !all_g_values gv_after )
  done ;
  let f_chained = !current_acc.state.f in
  let f_tracker = WT.get_f tracker in
  let print_fp12_first name (fp12 : Proof_conversion.Fp12.Constant.t) =
    let c0, _ = fp12 in
    let c00, _, _ = c0 in
    Printf.eprintf "  %s c0.c0 = (%s, %s)\n%!" name
      (Bignum_bigint.to_string (fst c00))
      (Bignum_bigint.to_string (snd c00))
  in
  Printf.eprintf "f values after 64 iterations:\n%!" ;
  print_fp12_first "chained (circuits)" f_chained ;
  print_fp12_first "tracker (out-of-circuit)" f_tracker ;
  if Bignum_bigint.(fst (let a, _, _ = fst f_chained in a) =
                    fst (let a, _, _ = fst f_tracker in a)) then
    Printf.eprintf "f values MATCH (unexpected given tracker g values differ)\n%!"
  else
    Printf.eprintf "f values DIFFER (expected since g values differ)\n%!" ;
  ignore vk_const ;
  Printf.eprintf "Done.\n%!"
