(** Compare Rust MLO with nori's MLO. *)
open Core_kernel

module BI = Bignum_bigint

let () =
  let proof =
    Proof_conversion.Proof_json.load_proof "/tmp/groth16_test/proof.json"
  in
  let vk = Proof_conversion.Proof_json.load_vk "/tmp/groth16_test/vk.json" in
  Printf.eprintf
    "Computing native aux witness (Rust MLO will be printed to stderr)...\n%!" ;
  let native_aux =
    Proof_conversion.Pairing_utils_bridge.groth16_aux_witness ~proof ~vk
  in
  Printf.eprintf "Native: shift_power = %d\n%!" native_aux.shift_power ;
  let ((ng00, _), _, _), _ = native_aux.c in
  Printf.eprintf "Native: c.g00 = %s\n%!" (BI.to_string ng00) ;
  Printf.eprintf
    "Expected nori MLO g00 = \
     16093833120062609384555815001435312305948181912477252726143335865310703416461\n\
     %!" ;
  Printf.eprintf "Done.\n%!"
