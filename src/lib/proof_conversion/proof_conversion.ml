(** Top-level proof conversion library.

    Converts non-native ZK proofs (Groth16, PLONK) into Mina-compatible
    proofs via recursive proof compression using Pickles. *)

open Core_kernel

(** Re-export key modules for external access. *)
module Witness_tracker = Witness_tracker

module Bn254_params = Bn254_params
module Proof_json = Proof_json
module Vk_constants = Vk_constants
module Circuit_info = Circuit_info
module Plonk_circuits = Plonk_circuits
module Plonk_proof_json = Plonk_proof_json
module Plonk_requests = Plonk_requests
module Plonk_pickles_rules = Plonk_pickles_rules
module Plonk_witness_tracker = Plonk_witness_tracker
module Groth16_requests = Groth16_requests
module Pickles_rules = Pickles_rules
module Circuit_utils = Circuit_utils
module Circuits = Circuits

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
    let proof = Proof_json.load_proof input_path in
    let vk_path = Filename.dirname input_path ^ "/vk.json" in
    let vk = Proof_json.load_vk vk_path in
    let aux_path = Filename.dirname input_path ^ "/aux_witness.json" in
    let aux = Proof_json.load_aux_witness aux_path in
    let tracker = Witness_tracker.create ~proof ~vk ~aux in
    Circuit_config.set_tracker tracker ;
    let vk_const = Vk_constants.create vk in
    let witnesses =
      Array.init Circuits.num_circuits ~f:(fun _n ->
          (* TODO: populate witnesses from tracker data *)
          Groth16_requests.empty_witness )
    in
    let proofs =
      Pickles_rules.compile_and_prove_all ~vk:vk_const ~witnesses
    in
    (* TODO: hash_pairs should use actual proof output hashes, not synthetic
       values. Currently the compression tree operates on dummy data. *)
    let module Step = Pickles.Impls.Step in
    let hash_pairs =
      Array.init Circuits.num_circuits ~f:(fun i ->
          let input =
            if i = 0 then Step.Field.Constant.zero
            else Step.Field.Constant.of_int i
          in
          let output = Step.Field.Constant.of_int (i + 1) in
          (input, output) )
    in
    let _final_hash, _final_proof = Compressor.compress ~hash_pairs in
    (* Serialize proofs to JSON *)
    let json_proofs =
      Array.mapi proofs ~f:(fun i proof ->
          let module P = Pickles.Proof.Make (Pickles_types.Nat.N0) in
          let proof_str = P.to_base64 proof in
          `Assoc [ ("circuit", `Int i); ("proof", `String proof_str) ] )
    in
    let output_json =
      `Assoc
        [ ("num_circuits", `Int Circuits.num_circuits)
        ; ("proofs", `List (Array.to_list json_proofs))
        ]
    in
    Yojson.Safe.to_file output_path output_json
end

(** PLONK proof conversion (SP1). *)
module Plonk : PROOF_SYSTEM = struct
  let name = "plonk"

  let convert ~input_path:_ ~output_path =
    let witnesses =
      Array.init Plonk_circuits.num_circuits ~f:(fun _n ->
          (* TODO: populate witnesses from actual proof data *)
          Plonk_requests.empty_witness )
    in
    let proofs = Plonk_pickles_rules.compile_and_prove_all ~witnesses in
    (* TODO: hash_pairs should use actual proof output hashes. The compression
       tree below duplicates Compressor.compress logic — generalize compress
       to handle arbitrary power-of-2 sizes. *)
    let module Step = Pickles.Impls.Step in
    let hash_pairs =
      Array.init Plonk_circuits.num_circuits ~f:(fun i ->
          let input =
            if i = 0 then Step.Field.Constant.zero
            else Step.Field.Constant.of_int i
          in
          let output = Step.Field.Constant.of_int (i + 1) in
          (input, output) )
    in
    (* PLONK has 24 circuits — pad to 32 for binary tree (next power of 2) *)
    let padded =
      Array.init 32 ~f:(fun i ->
          if i < Array.length hash_pairs then hash_pairs.(i)
          else (Step.Field.Constant.zero, Step.Field.Constant.zero) )
    in
    (* Layer 1: 16 nodes *)
    let layer1 =
      Array.init 16 ~f:(fun i ->
          let left_in, left_out = padded.(i * 2) in
          let right_in, right_out = padded.((i * 2) + 1) in
          fst (Compressor.prove_layer1 ~left_in ~left_out ~right_in ~right_out) )
    in
    let current = ref layer1 in
    for layer = 2 to 5 do
      let n = Array.length !current in
      current :=
        Array.init (n / 2) ~f:(fun i ->
            fst
              (Compressor.prove_merge
                 ~left:!current.(i * 2)
                 ~right:!current.((i * 2) + 1)
                 ~layer ) )
    done ;
    let module P = Pickles.Proof.Make (Pickles_types.Nat.N0) in
    let json_proofs =
      Array.mapi proofs ~f:(fun i proof ->
          `Assoc [ ("circuit", `Int i); ("proof", `String (P.to_base64 proof)) ] )
    in
    let output_json =
      `Assoc
        [ ("type", `String "plonk")
        ; ("num_circuits", `Int Plonk_circuits.num_circuits)
        ; ("proofs", `List (Array.to_list json_proofs))
        ]
    in
    Yojson.Safe.to_file output_path output_json
end
