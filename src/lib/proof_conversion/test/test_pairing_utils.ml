(** Test pairing-utils FFI with real Groth16 proof data. *)
open Core_kernel

module BI = Bignum_bigint

let () =
  Printf.eprintf "Testing pairing-utils FFI with real proof data...\n%!" ;
  let proof =
    Proof_conversion.Proof_json.load_proof "/tmp/groth16_test/proof.json"
  in
  let vk = Proof_conversion.Proof_json.load_vk "/tmp/groth16_test/vk.json" in
  Printf.eprintf "Computing MLO from proof + VK...\n%!" ;
  let mlo = Proof_conversion.Witness_tracker.compute_mlo ~proof ~vk in
  Printf.eprintf "MLO computed.\n%!" ;
  (* Dump first few fields of the MLO *)
  let (g0, g1, _g2), (_h0, _h1, _h2) = mlo in
  let g00, g01 = g0 in
  let g10, g11 = g1 in
  Printf.eprintf "MLO.g00 = %s\n%!" (BI.to_string g00) ;
  Printf.eprintf "MLO.g01 = %s\n%!" (BI.to_string g01) ;
  Printf.eprintf "MLO.g10 = %s\n%!" (BI.to_string g10) ;
  Printf.eprintf "MLO.g11 = %s\n%!" (BI.to_string g11) ;
  (* Also dump the pipe-delimited string *)
  let pipe = Proof_conversion.Pairing_utils_stubs.fp12_to_pipe mlo in
  Printf.eprintf "Pipe length: %d\n%!" (String.length pipe) ;
  Printf.eprintf "First 200 chars: %s\n%!" (String.prefix pipe 200) ;
  Printf.eprintf "Done.\n%!"
