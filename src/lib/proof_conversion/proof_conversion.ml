(** Top-level proof conversion library.

    Converts non-native ZK proofs (Groth16, PLONK) into Mina-compatible
    proofs via recursive proof compression using Pickles. *)

open Core_kernel

(** Re-export shared utilities. *)
let dummy_constraints = Circuit_utils.dummy_constraints

let public_input_typ = Circuit_utils.public_input_typ

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
    let _tracker = Witness_tracker.create ~proof ~vk in
    let _witness_data = Witness_provider.make_witness_data ~proof ~vk in
    printf "Witness data prepared\n" ;
    printf "Compiling and proving all %d circuits (chained)...\n"
      Circuits.num_circuits ;
    let proofs = Pickles_rules.compile_and_prove_all () in
    printf "Generated %d proofs successfully.\n" (Array.length proofs) ;
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

(** PLONK proof conversion (SP1). Not yet implemented. *)
module Plonk : PROOF_SYSTEM = struct
  let name = "plonk"

  let convert ~input_path:_ ~output_path:_ =
    failwith "PLONK proof conversion not yet implemented"
end
