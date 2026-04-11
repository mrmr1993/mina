(** Test: verify c * inverse(c) = 1 for the Groth16 aux witness. *)
open Core_kernel
module Step = Pickles.Impls.Step
module WT = Proof_conversion.Witness_tracker

let () =
  let proof = Proof_conversion.Proof_json.load_proof "/tmp/groth16_test/proof.json" in
  let vk = Proof_conversion.Proof_json.load_vk "/tmp/groth16_test/vk.json" in
  let aux = Proof_conversion.Proof_json.load_aux_witness "/tmp/groth16_test/aux_witness.json" in
  let tracker = WT.create ~proof ~vk ~aux in
  let c = tracker |> ignore ; aux.c in
  let c0, _ = c in
  let c00, _, _ = c0 in
  let c00_0, c00_1 = c00 in
  Printf.eprintf "c.c0.c0 = (%s, %s)\n%!"
    (Bignum_bigint.to_string c00_0)
    (Bignum_bigint.to_string c00_1) ;
  (* Compute inverse out-of-circuit *)
  let c_inv = WT.Fp12.inverse c in
  let product = WT.Fp12.mul c c_inv in
  let one = WT.Fp12.one in
  let p0, _ = product in
  let o0, _ = one in
  let (p00, p01), _, _ = p0 in
  let (o00, o01), _, _ = o0 in
  Printf.eprintf "c * c_inv c0.c0 = (%s, %s)\n%!"
    (Bignum_bigint.to_string p00) (Bignum_bigint.to_string p01) ;
  Printf.eprintf "expected c0.c0  = (%s, %s)\n%!"
    (Bignum_bigint.to_string o00) (Bignum_bigint.to_string o01) ;
  if Bignum_bigint.(p00 = o00 && p01 = o01) then
    Printf.eprintf "c * c_inv = 1 (first component): OK\n%!"
  else
    Printf.eprintf "c * c_inv ≠ 1: MISMATCH\n%!" ;
  (* Now test in-circuit *)
  Printf.eprintf "Testing in-circuit...\n%!" ;
  ( try
      Step.run_and_check_exn (fun () ->
          let c_var =
            Step.exists Proof_conversion.Fp12.typ ~compute:(fun () -> c)
          in
          let c_inv_var =
            Step.exists Proof_conversion.Fp12.typ ~compute:(fun () -> c_inv)
          in
          let prod = Proof_conversion.Fp12.mul c_var c_inv_var in
          Proof_conversion.Fp12.assert_one prod ;
          fun () -> Printf.eprintf "In-circuit c * c_inv = 1: OK\n%!" )
    with exn ->
      Printf.eprintf "In-circuit FAILED: %s\n%!" (Exn.to_string exn) ) ;
  Printf.eprintf "Done.\n%!"
