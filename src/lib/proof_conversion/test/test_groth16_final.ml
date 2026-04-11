(** Test: compare single f-update iteration inline vs through Accumulator round-trip. *)
open Core_kernel
module Step = Pickles.Impls.Step

let () =
  Printf.eprintf "=== Single f-update iteration round-trip test ===\n%!" ;
  let proof = Proof_conversion.Proof_json.load_proof "/tmp/groth16_test/proof.json" in
  let vk = Proof_conversion.Proof_json.load_vk "/tmp/groth16_test/vk.json" in
  let aux = Proof_conversion.Proof_json.load_aux_witness "/tmp/groth16_test/aux_witness.json" in
  let tracker = Proof_conversion.Witness_tracker.create ~proof ~vk ~aux in
  let c_inv = Proof_conversion.Witness_tracker.Fp12.inverse aux.c in
  let g0 = Proof_conversion.Witness_tracker.get_g tracker 0 in
  let ate = Proof_conversion.Bn254_params.ate_loop_count in
  (* Compute f after 1 iteration out-of-circuit *)
  let expected =
    let f = Proof_conversion.Witness_tracker.Fp12.square c_inv in
    let f = Proof_conversion.Witness_tracker.Fp12.mul f g0 in
    if ate.(1) = 1 then Proof_conversion.Witness_tracker.Fp12.mul f c_inv
    else if ate.(1) = -1 then Proof_conversion.Witness_tracker.Fp12.mul f aux.c
    else f
  in
  (* Compute f after 1 iteration in-circuit, then read back *)
  let actual =
    Step.run_and_check_exn (fun () ->
        let ci = Step.exists Proof_conversion.Fp12.typ ~compute:(fun () -> c_inv) in
        let g = Step.exists Proof_conversion.Fp12.typ ~compute:(fun () -> g0) in
        let c = Step.exists Proof_conversion.Fp12.typ ~compute:(fun () -> aux.c) in
        let f = Proof_conversion.Fp12.mul (Proof_conversion.Fp12.square ci) g in
        let f =
          if ate.(1) = 1 then Proof_conversion.Fp12.mul f ci
          else if ate.(1) = -1 then Proof_conversion.Fp12.mul f c
          else f
        in
        fun () -> Step.As_prover.read Proof_conversion.Fp12.typ f )
  in
  let e0, _ = expected in
  let a0, _ = actual in
  let e00, _, _ = e0 in
  let a00, _, _ = a0 in
  Printf.eprintf "  Expected c0.c0 = (%s, %s)\n%!"
    (Bignum_bigint.to_string (fst e00)) (Bignum_bigint.to_string (snd e00)) ;
  Printf.eprintf "  Actual   c0.c0 = (%s, %s)\n%!"
    (Bignum_bigint.to_string (fst a00)) (Bignum_bigint.to_string (snd a00)) ;
  if Bignum_bigint.(fst e00 = fst a00 && snd e00 = snd a00) then
    Printf.eprintf "  MATCH\n%!"
  else
    Printf.eprintf "  MISMATCH\n%!" ;
  (* Now round-trip through Accumulator.typ *)
  let acc_const = Proof_conversion.Witness_tracker.get_accumulator_constant tracker in
  let acc_with_f =
    { acc_const with
      state = { acc_const.state with f = expected }
    }
  in
  let rt_f =
    Step.run_and_check_exn (fun () ->
        let acc = Step.exists Proof_conversion.Accumulator.typ ~compute:(fun () -> acc_with_f) in
        fun () -> Step.As_prover.read Proof_conversion.Fp12.typ acc.state.f )
  in
  let rt0, _ = rt_f in
  let rt00, _, _ = rt0 in
  Printf.eprintf "  RT       c0.c0 = (%s, %s)\n%!"
    (Bignum_bigint.to_string (fst rt00)) (Bignum_bigint.to_string (snd rt00)) ;
  if Bignum_bigint.(fst e00 = fst rt00 && snd e00 = snd rt00) then
    Printf.eprintf "  Accumulator round-trip: MATCH\n%!"
  else
    Printf.eprintf "  Accumulator round-trip: MISMATCH\n%!" ;
  Printf.eprintf "Done.\n%!"
