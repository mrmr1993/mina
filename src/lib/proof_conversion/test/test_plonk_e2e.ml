(** End-to-end test: parse SP1 proof, prove zkp0, export for nori verification. *)

open Core_kernel
module Step = Pickles.Impls.Step

let () =
  let fixture_path = "src/lib/proof_conversion/test/plonk_e2e_fixture.json" in
  Printf.eprintf "Loading fixture from %s...\n%!" fixture_path ;
  let acc_const = Proof_conversion.Plonk_proof_json.load_fixture fixture_path in
  (* Compute input hash = Poseidon.hashPacked(Accumulator, initial_acc) *)
  let input_hash =
    Proof_conversion.Plonk_witness_tracker.hash_accumulator_const acc_const
  in
  Printf.eprintf "Input hash: %s\n%!"
    (Step.Field.Constant.to_string input_hash) ;
  (* Create witness for zkp0: the initial accumulator *)
  let witness : Proof_conversion.Plonk_requests.witness =
    { Proof_conversion.Plonk_requests.empty_witness with
      plonk_acc = Some acc_const
    }
  in
  Printf.eprintf "Compiling and proving zkp0...\n%!" ;
  let output_hash, proof, vk =
    Proof_conversion.Plonk_pickles_rules.compile_prove_and_export ~n:0
      ~input_hash ~witness
  in
  Printf.eprintf "zkp0 proved successfully!\n%!" ;
  Printf.eprintf "Output hash: %s\n%!"
    (Step.Field.Constant.to_string output_hash) ;
  (* Export proof as JsonProof *)
  let module P = Pickles.Proof.Make (Pickles_types.Nat.N0) in
  let proof_base64 = P.to_base64 proof in
  let vk_base64 =
    Pickles.Side_loaded.Verification_key.to_base64 vk
  in
  let json_proof =
    `Assoc
      [ ("publicInput", `List [ `String (Step.Field.Constant.to_string input_hash) ])
      ; ("publicOutput", `List [ `String (Step.Field.Constant.to_string output_hash) ])
      ; ("maxProofsVerified", `Int 0)
      ; ("proof", `String proof_base64)
      ]
  in
  let json_vk =
    `Assoc
      [ ("data", `String vk_base64)
      ; ("hash", `String "")  (* hash computed by o1js *)
      ]
  in
  let output_path = "src/lib/proof_conversion/test/zkp0_proof.json" in
  let vk_path = "src/lib/proof_conversion/test/zkp0_vk.json" in
  Yojson.Safe.to_file output_path json_proof ;
  Yojson.Safe.to_file vk_path json_vk ;
  Printf.eprintf "Proof written to %s\n%!" output_path ;
  Printf.eprintf "VK written to %s\n%!" vk_path ;
  Printf.eprintf "Done.\n%!"
