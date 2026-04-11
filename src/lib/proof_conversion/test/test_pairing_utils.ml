(** Compare native Rust aux witness (OCaml MLO + VK w27) with JSON fixture. *)
open Core_kernel

module BI = Bignum_bigint

let () =
  let proof =
    Proof_conversion.Proof_json.load_proof "/tmp/groth16_test/proof.json"
  in
  let vk = Proof_conversion.Proof_json.load_vk "/tmp/groth16_test/vk.json" in
  Printf.eprintf
    "Computing native aux witness (OCaml MLO + Rust eth_root)...\n%!" ;
  let native =
    Proof_conversion.Pairing_utils_bridge.groth16_aux_witness ~proof ~vk
  in
  Printf.eprintf "Native: shift_power=%d\n%!" native.shift_power ;
  let json =
    Proof_conversion.Proof_json.load_aux_witness
      "/tmp/groth16_test/aux_witness.json"
  in
  Printf.eprintf "JSON:   shift_power=%d\n%!" json.shift_power ;
  Printf.eprintf "shift match: %b\n%!" (native.shift_power = json.shift_power) ;
  let ((ng00, _), _, _), _ = native.c in
  let ((jg00, _), _, _), _ = json.c in
  Printf.eprintf "c.g00 match: %b\n%!" (BI.equal ng00 jg00) ;
  if not (BI.equal ng00 jg00) then (
    Printf.eprintf "  native: %s\n%!" (BI.to_string ng00) ;
    Printf.eprintf "  json:   %s\n%!" (BI.to_string jg00) ) ;
  Printf.eprintf "Done.\n%!"
