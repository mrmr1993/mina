(** Top-level proof conversion library.

    Converts non-native ZK proofs (Groth16, PLONK) into Mina-compatible
    proofs via recursive proof compression using Pickles. *)

open Core_kernel

(** Re-export key modules for external access. *)
module Compressor = Proof_conversion_groth16.Compressor
module Witness_tracker = Proof_conversion_groth16.Witness_tracker

module Bn254_params = Proof_conversion_bn254.Bn254_params
module Proof_json = Proof_conversion_groth16.Proof_json
module Vk_constants = Proof_conversion_groth16.Vk_constants
module Circuit_info = Proof_conversion_groth16.Circuit_info
module Plonk_circuits = Proof_conversion_plonk.Plonk_circuits
module Plonk_proof_json = Proof_conversion_plonk.Plonk_proof_json
module Plonk_requests = Proof_conversion_plonk.Plonk_requests
module Plonk_pickles_rules = Proof_conversion_plonk.Plonk_pickles_rules
module Plonk_witness_tracker = Proof_conversion_plonk.Plonk_witness_tracker
module Groth16_requests = Proof_conversion_groth16.Groth16_requests
module Pickles_rules = Proof_conversion_groth16.Pickles_rules
module Circuit_utils = Proof_conversion_circuit_kit.Circuit_utils
module Circuits = Proof_conversion_groth16.Circuits
module Kzg_accumulator = Proof_conversion_plonk.Kzg_accumulator
module Tree_compressor = Proof_conversion_compressor.Tree_compressor
module G1 = Proof_conversion_bn254.G1
module G2 = Proof_conversion_bn254.G2
module Fp6 = Proof_conversion_bn254.Fp6
module Fp12 = Proof_conversion_bn254.Fp12
module Circuit_config = Proof_conversion_groth16.Circuit_config
module Accumulator = Proof_conversion_groth16.Accumulator
module Ate_circuit = Proof_conversion_groth16.Ate_circuit
module Fupdate_circuit = Proof_conversion_groth16.Fupdate_circuit
module Pairing_utils_bridge = Proof_conversion_pairing_utils_bridge.Pairing_utils_bridge
module Cache_config = Proof_conversion_circuit_kit.Cache_config
module Workdir = Workdir
module Plonk_accumulator = Proof_conversion_plonk.Plonk_accumulator

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
    let dir = Filename.dirname input_path in
    let proof = Proof_json.load_proof input_path in
    (* Look for VK and aux witness: check explicit env vars, then conventions *)
    let vk_path =
      match Sys.getenv_opt "GROTH16_VK_PATH" with
      | Some p ->
          p
      | None ->
          dir ^ "/vk.json"
    in
    let vk = Proof_json.load_vk vk_path in
    let aux_path =
      match Sys.getenv_opt "GROTH16_AUX_PATH" with
      | Some p ->
          p
      | None ->
          dir ^ "/aux_witness.json"
    in
    let aux = Proof_json.load_aux_witness aux_path in
    let tracker = Witness_tracker.create ~proof ~vk ~aux in
    Circuit_config.set_tracker tracker ;
    let vk_const = Vk_constants.create vk in
    let module Step = Pickles.Impls.Step in
    (* Pre-compute static witness data from tracker *)
    let line_hashes = Witness_tracker.get_line_hashes tracker in
    let b_lines = Witness_tracker.get_all_b_lines tracker in
    (* Get initial accumulator constant.
       The tracker's g_digest is the FINAL value after compute_miller_loop.
       For circuit 0, we need the INITIAL g_digest = hash(zeros). *)
    let initial_acc =
      let acc = Witness_tracker.get_accumulator_constant tracker in
      (* Overwrite g_digest with hash(zeros) for the initial state *)
      let initial_g_digest =
        let n = Array.length Bn254_params.ate_loop_count in
        let zeros = Array.create ~len:n Step.Field.Constant.zero in
        Random_oracle.hash zeros
      in
      { acc with
        state =
          { g_digest = initial_g_digest
          ; t_point = acc.proof.b (* Initial t_point = B *)
          ; f =
              (Fp6.Constant.zero, Fp6.Constant.zero)
              (* f starts as zero, matching nori *)
          }
      }
    in
    (* Evolving line_hashes: starts as zeros, filled by each ate circuit.
       After each circuit proves, update the entries it computed. *)
    let n_total = Array.length Bn254_params.ate_loop_count in
    let evolving_line_hashes =
      ref (Array.create ~len:n_total Step.Field.Constant.zero)
    in
    let all_g_values = ref [||] in
    (* Compute initial hash *)
    let initial_hash =
      Step.run_and_check_exn (fun () ->
          let acc =
            Step.exists Accumulator.typ ~compute:(fun () -> initial_acc)
          in
          let h = Accumulator.hash acc in
          fun () -> Step.As_prover.read_var h )
    in
    (* Chain circuits 0-12 via auxiliary_output *)
    let current_hash = ref initial_hash in
    let current_acc = ref initial_acc in
    let hash_pairs =
      Array.create ~len:Circuits.num_circuits
        (Step.Field.Constant.zero, Step.Field.Constant.zero)
    in
    let proofs =
      Array.create ~len:Circuits.num_circuits
        (Obj.magic () : Pickles_types.Nat.N0.n Pickles.Proof.t)
    in
    let fp_to_field h =
      Step.Field.Constant.of_string (Kimchi_pasta.Pasta.Fp.to_string h)
    in
    let _line_hashes_field = Array.map line_hashes ~f:fp_to_field in
    (* Chain circuits 0-12 via auxiliary_output *)
    for n = 0 to 12 do
      let witness : Groth16_requests.witness =
        if n <= 6 then
          (* Ate loop circuits: need accumulator, line_hashes, b_lines.
             line_hashes evolves: circuit N has entries for ranges 0..N-1
             filled, and zeros for the rest. Build from tracker data. *)
          { Groth16_requests.empty_witness with
            accumulator = Some !current_acc
          ; line_hashes = Some !evolving_line_hashes
          ; b_lines =
              Some
                (Array.map b_lines ~f:(fun (l : Witness_tracker.Line.t) ->
                     (l.lambda, l.neg_mu) ) )
          }
        else
          (* f-update circuits: need accumulator, g_chunk, lhs/rhs hashes *)
          let idx = n - 7 in
          let n_iters = Fupdate_circuit.iterations_per_circuit.(idx) in
          let g_start = Fupdate_circuit.g_start_per_circuit.(idx) in
          (* Use circuit-computed g_values and line_hashes from aux output *)
          let all_lh = !evolving_line_hashes in
          let lhs = Array.sub all_lh ~pos:0 ~len:g_start in
          let g_chunk = Array.sub !all_g_values ~pos:g_start ~len:n_iters in
          let rhs_start = g_start + n_iters in
          let rhs =
            Array.sub all_lh ~pos:rhs_start
              ~len:(Array.length all_lh - rhs_start)
          in
          { Groth16_requests.empty_witness with
            accumulator = Some !current_acc
          ; g_chunk = Some g_chunk
          ; lhs_hashes = Some lhs
          ; rhs_hashes = Some rhs
          }
      in
      let input_hash = !current_hash in
      let output_hash, acc_after, lh_after, gv_after, proof =
        Pickles_rules.compile_and_prove_one_with_acc ~vk:vk_const ~n ~input_hash
          ~witness
      in
      hash_pairs.(n) <- (input_hash, output_hash) ;
      proofs.(n) <- proof ;
      current_hash := output_hash ;
      current_acc := acc_after ;
      (* Use line_hashes and g_values from auxiliary output *)
      if n <= 6 then (
        evolving_line_hashes := lh_after ;
        all_g_values := Array.append !all_g_values gv_after )
    done ;
    (* Circuits 13-15: use regular proving with specific witnesses *)
    for n = 13 to Circuits.num_circuits - 1 do
      let witness =
        match n with
        | 13 ->
            (* Final exponentiation: needs accumulator + lhs_hashes + final_g *)
            let all_lh = !evolving_line_hashes in
            let n_total = Array.length Bn254_params.ate_loop_count in
            let lhs = Array.sub all_lh ~pos:0 ~len:(n_total - 1) in
            { Groth16_requests.empty_witness with
              accumulator = Some !current_acc
            ; lhs_hashes = Some lhs
            ; final_g = Some !all_g_values.(Array.length !all_g_values - 1)
            }
        | 14 ->
            (* Partial IC: needs public inputs *)
            let n_pi = Witness_tracker.num_public_inputs tracker in
            let pis =
              Array.init n_pi ~f:(fun i ->
                  Witness_tracker.get_public_input tracker i )
            in
            { Groth16_requests.empty_witness with public_inputs = Some pis }
        | 15 ->
            (* Full IC: needs pi_point, partial_ic_acc, public inputs *)
            let n_pi = Witness_tracker.num_public_inputs tracker in
            let pis =
              Array.init n_pi ~f:(fun i ->
                  Witness_tracker.get_public_input tracker i )
            in
            let pi = Witness_tracker.get_pi tracker in
            let partial_acc = Witness_tracker.get_partial_ic_acc tracker in
            let g1_to_const (p : Witness_tracker.G1.t) : G1.Constant.t =
              { x = p.x; y = p.y }
            in
            { Groth16_requests.empty_witness with
              public_inputs = Some pis
            ; pi_point = Some (g1_to_const pi)
            ; partial_ic_acc = Some (g1_to_const partial_acc)
            }
        | _ ->
            Groth16_requests.empty_witness
      in
      let input_hash = !current_hash in
      let output_hash, proof =
        Pickles_rules.compile_and_prove_one ~vk:vk_const ~n ~input_hash ~witness
      in
      hash_pairs.(n) <- (input_hash, output_hash) ;
      proofs.(n) <- proof ;
      current_hash := output_hash
    done ;
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
