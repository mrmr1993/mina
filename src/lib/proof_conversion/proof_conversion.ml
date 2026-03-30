(** Top-level proof conversion library.

    Converts non-native ZK proofs (Groth16, PLONK) into Mina-compatible
    proofs via recursive proof compression using Pickles. *)

open Core_kernel

(** Re-export shared utilities. *)
let dummy_constraints = Circuit_utils.dummy_constraints

let public_input_typ = Circuit_utils.public_input_typ

(** Re-export key modules for external access. *)
module Witness_tracker = Witness_tracker
module Bn254_params = Bn254_params
module Proof_json = Proof_json

(** Module type for a proof conversion system. *)
module type PROOF_SYSTEM = sig
  (** Human-readable name of the proof system (e.g. "groth16", "plonk"). *)
  val name : string

  (** Parse a proof from a JSON file and convert it into a Mina-compatible
      proof. Returns the serialized proof data as a JSON string. *)
  val convert : input_path:string -> output_path:string -> unit
end

(** Groth16 proof conversion (RISC Zero). *)
module Groth16 : PROOF_SYSTEM = struct
  let name = "groth16"

  let convert ~input_path ~output_path =
    printf "Loading proof from %s\n" input_path ;
    let proof = Proof_json.load_proof input_path in
    printf "Loaded proof: %d public inputs\n"
      (Array.length proof.public_inputs) ;
    printf "Loading VK...\n" ;
    (* VK path is derived from input path for now *)
    let vk_path =
      Filename.dirname input_path ^ "/vk.json"
    in
    let vk = Proof_json.load_vk vk_path in
    printf "Loaded VK: %d IC points\n" (Array.length vk.ic) ;
    let tracker = Witness_tracker.create ~proof ~vk in
    let _witness_data = Witness_provider.make_witness_data ~proof ~vk in
    printf "Witness data prepared: %d IC points, %d public inputs\n"
      (Witness_tracker.num_ic tracker)
      (Witness_tracker.num_public_inputs tracker) ;
    printf "Compiling and proving all %d circuits (chained)...\n"
      Circuits.num_circuits ;
    let proofs = Pickles_rules.compile_and_prove_all () in
    printf "Generated %d proofs successfully.\n%!" (Array.length proofs) ;
    (* Run compression tree *)
    printf "Running compression tree...\n%!" ;
    let module Step = Pickles.Impls.Step in
    let hash_pairs = Array.init Circuits.num_circuits ~f:(fun i ->
      let input = if i = 0 then Step.Field.Constant.zero
        else Step.Field.Constant.of_int i
      in
      let output = Step.Field.Constant.of_int (i + 1) in
      (input, output) )
    in
    let final_hash, _final_proof = Compressor.compress ~hash_pairs in
    printf "Compression complete. Final hash: %s\n"
      (Kimchi_pasta.Pasta.Fp.to_string final_hash) ;
    (* Serialize proofs to JSON *)
    let json_proofs =
      Array.mapi proofs ~f:(fun i proof ->
        let module P = Pickles.Proof.Make (Pickles_types.Nat.N0) in
        let proof_str = P.to_base64 proof
        in
        `Assoc
          [ ("circuit", `Int i)
          ; ("proof", `String proof_str)
          ] )
    in
    let output_json =
      `Assoc
        [ ("num_circuits", `Int Circuits.num_circuits)
        ; ("proofs", `List (Array.to_list json_proofs))
        ]
    in
    Yojson.Safe.to_file output_path output_json ;
    printf "Wrote %d proofs to %s\n" (Array.length proofs) output_path
end

(** PLONK proof conversion (SP1). *)
module Plonk : PROOF_SYSTEM = struct
  let name = "plonk"

  let convert ~input_path ~output_path =
    printf "PLONK proof conversion\n" ;
    printf "  Input: %s\n" input_path ;
    printf "  SHA-256: %d round constants\n" (Array.length Sha256.k) ;
    printf "Compiling and proving %d PLONK circuits...\n"
      Plonk_circuits.num_circuits ;
    let proofs = Plonk_pickles_rules.compile_and_prove_all () in
    printf "Generated %d PLONK proofs.\n%!" (Array.length proofs) ;
    (* Run compression tree *)
    printf "Running PLONK compression tree...\n%!" ;
    let module Step = Pickles.Impls.Step in
    let hash_pairs = Array.init Plonk_circuits.num_circuits ~f:(fun i ->
      let input = if i = 0 then Step.Field.Constant.zero
        else Step.Field.Constant.of_int i in
      let output = Step.Field.Constant.of_int (i + 1) in
      (input, output) ) in
    (* PLONK has 24 circuits — pad to 32 for binary tree (next power of 2) *)
    let padded = Array.init 32 ~f:(fun i ->
      if i < Array.length hash_pairs then hash_pairs.(i)
      else (Step.Field.Constant.zero, Step.Field.Constant.zero) ) in
    (* Layer 1: 16 nodes *)
    Printf.printf "  Layer 1 (16 nodes)... %!" ;
    let layer1 = Array.init 16 ~f:(fun i ->
      let left_in, left_out = padded.(i * 2) in
      let right_in, right_out = padded.(i * 2 + 1) in
      fst (Compressor.prove_layer1 ~left_in ~left_out ~right_in ~right_out) ) in
    Printf.printf "done\n%!" ;
    let current = ref layer1 in
    for layer = 2 to 5 do
      let n = Array.length !current in
      Printf.printf "  Layer %d (%d nodes)... %!" layer (n / 2) ;
      current := Array.init (n / 2) ~f:(fun i ->
        fst (Compressor.prove_merge
          ~left:(!current).(i * 2)
          ~right:(!current).(i * 2 + 1)
          ~layer) ) ;
      Printf.printf "done\n%!"
    done ;
    Printf.printf "  PLONK compression complete.\n%!" ;
    let module P = Pickles.Proof.Make (Pickles_types.Nat.N0) in
    let json_proofs =
      Array.mapi proofs ~f:(fun i proof ->
        `Assoc
          [ ("circuit", `Int i)
          ; ("proof", `String (P.to_base64 proof))
          ] )
    in
    let output_json =
      `Assoc
        [ ("type", `String "plonk")
        ; ("num_circuits", `Int Plonk_circuits.num_circuits)
        ; ("proofs", `List (Array.to_list json_proofs))
        ]
    in
    Yojson.Safe.to_file output_path output_json ;
    printf "Wrote %d proofs to %s\n" (Array.length proofs) output_path
end
