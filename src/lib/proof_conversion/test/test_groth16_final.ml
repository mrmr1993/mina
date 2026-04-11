(** Test: Fp12 round-trip through Groth16 Accumulator typ. *)
open Core_kernel
module Step = Pickles.Impls.Step
module WT = Proof_conversion.Witness_tracker

let () =
  let proof = Proof_conversion.Proof_json.load_proof "/tmp/groth16_test/proof.json" in
  let vk = Proof_conversion.Proof_json.load_vk "/tmp/groth16_test/vk.json" in
  let aux = Proof_conversion.Proof_json.load_aux_witness "/tmp/groth16_test/aux_witness.json" in
  let tracker = WT.create ~proof ~vk ~aux in
  Proof_conversion.Circuit_config.set_tracker tracker ;
  let vk_const = Proof_conversion.Vk_constants.create vk in
  ignore vk_const ;
  (* Get initial accumulator with a specific f value *)
  let initial_acc = WT.get_accumulator_constant tracker in
  let n_total = Array.length Proof_conversion.Bn254_params.ate_loop_count in
  let initial_g_digest =
    let zeros = Array.create ~len:n_total Step.Field.Constant.zero in
    Random_oracle.hash zeros
  in
  let test_f = aux.c in  (* Use c as a non-trivial test value *)
  let acc_with_f =
    { initial_acc with
      state =
        { g_digest = initial_g_digest
        ; t_point = initial_acc.proof.b
        ; f = test_f
        }
    }
  in
  (* Round-trip through Accumulator.typ *)
  Printf.eprintf "Testing Fp12 round-trip through Accumulator.typ...\n%!" ;
  let f_after_roundtrip =
    Step.run_and_check_exn (fun () ->
        let acc =
          Step.exists Proof_conversion.Accumulator.typ ~compute:(fun () ->
              acc_with_f )
        in
        fun () ->
          let f_read = Step.As_prover.read Proof_conversion.Fp12.typ acc.state.f in
          f_read )
  in
  let f0, _ = test_f in
  let f0_rt, _ = f_after_roundtrip in
  let (f00, _), _, _ = f0 in
  let (f00_rt, _), _, _ = f0_rt in
  let f00_0, f00_1 = f00 in
  let f00_rt_0, f00_rt_1 = f00_rt in
  Printf.eprintf "  Original f c0.c0 = (%s, %s)\n%!"
    (Bignum_bigint.to_string f00_0) (Bignum_bigint.to_string f00_1) ;
  Printf.eprintf "  Round-tripped    = (%s, %s)\n%!"
    (Bignum_bigint.to_string f00_rt_0) (Bignum_bigint.to_string f00_rt_1) ;
  if Bignum_bigint.(f00_0 = f00_rt_0 && f00_1 = f00_rt_1) then
    Printf.eprintf "  Round-trip: MATCH\n%!"
  else
    Printf.eprintf "  Round-trip: MISMATCH\n%!" ;
  Printf.eprintf "Done.\n%!"
