(** Test pairing-utils FFI: dump g_values and MLO for comparison with nori. *)
open Core_kernel

module BI = Bignum_bigint
module WT = Proof_conversion.Witness_tracker

let print_fp12 label ((g0, g1, g2), (h0, h1, h2)) =
  let s (a, b) = sprintf "(%s, %s)" (BI.to_string a) (BI.to_string b) in
  Printf.eprintf "%s: g0=%s g1=%s g2=%s h0=%s h1=%s h2=%s\n%!" label (s g0)
    (s g1) (s g2) (s h0) (s h1) (s h2)

let () =
  let proof =
    Proof_conversion.Proof_json.load_proof "/tmp/groth16_test/proof.json"
  in
  let vk = Proof_conversion.Proof_json.load_vk "/tmp/groth16_test/vk.json" in
  let aux =
    Proof_conversion.Proof_json.load_aux_witness
      "/tmp/groth16_test/aux_witness.json"
  in
  let tracker = WT.create ~proof ~vk ~aux in
  let g_values = WT.get_g_values tracker in
  Printf.eprintf "g_values count: %d\n%!" (Array.length g_values) ;
  (* Dump first 3 g values *)
  for i = 0 to min 2 (Array.length g_values - 1) do
    print_fp12 (sprintf "g[%d]" i) g_values.(i)
  done ;
  (* Compute MLO using the formula *)
  let mlo = WT.compute_mlo ~proof ~vk in
  print_fp12 "mlo" mlo ;
  (* Also show alpha_beta *)
  print_fp12 "alpha_beta" vk.alpha_beta ;
  Printf.eprintf "Done.\n%!"
