(** Top-level proof conversion library.

    Converts non-native ZK proofs (Groth16, PLONK) into Mina-compatible
    proofs via recursive proof compression using Pickles.

    The library is split into focused sub-libraries, each re-exported here
    as a namespace. Multi-module sub-libraries are exposed as their own
    namespace ([Bn254], [Circuit_kit], [Groth16], [Plonk]); single-module
    sub-libraries are exposed directly ([Tree_compressor], [Workdir],
    [Pairing_utils_bridge]). *)

open Core_kernel

(** BN254 curve primitives: tower fields, curve points, pairing lines. *)
module Bn254 = Proof_conversion_bn254

(** Shared circuit-kit helpers ([Circuit_utils], [Cache_config]). *)
module Circuit_kit = Proof_conversion_circuit_kit

(** Groth16 (Risc0/SP1) proof-conversion circuits and witness tracker. *)
module Groth16 = Proof_conversion_groth16

(** PLONK (SP1) proof-conversion circuits, transcript, and KZG. *)
module Plonk = Proof_conversion_plonk

(** Binary-tree proof-compression circuits. *)
module Tree_compressor = Proof_conversion_compressor.Tree_compressor

(** Staged working-directory orchestration. *)
module Workdir = Proof_conversion_workdir.Workdir

(** OCaml wrapper around the Rust pairing-utils FFI. *)
module Pairing_utils_bridge =
  Proof_conversion_pairing_utils_bridge.Pairing_utils_bridge

(** Module type for a proof conversion system. *)
module type PROOF_SYSTEM = sig
  (** Human-readable name of the proof system (e.g. "groth16", "plonk"). *)
  val name : string

  (** Parse a proof from a JSON file and convert it into a Mina-compatible
      proof. Returns the serialized proof data as a JSON string. *)
  val convert : input_path:string -> output_path:string -> unit
end

(** End-to-end conversion pipelines, one per supported proof system. *)
module Convert = struct
  (** Groth16 proof conversion (RISC Zero). *)
  module Groth16 : PROOF_SYSTEM = struct
    open Proof_conversion_bn254
    open Proof_conversion_groth16

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
      let proofs : Pickles_types.Nat.N0.n Pickles.Proof.t option array =
        Array.create ~len:Circuits.num_circuits None
      in
      let fp_to_field h =
        Step.Field.Constant.of_string (Kimchi_pasta.Pasta.Fp.to_string h)
      in
      let _line_hashes_field = Array.map line_hashes ~f:fp_to_field in
      (* Chain circuits 0-12 via auxiliary_output *)
      for n = 0 to 12 do
        let witness : Requests.witness =
          if n <= 6 then
            (* Ate loop circuits: need accumulator, line_hashes, b_lines.
               line_hashes evolves: circuit N has entries for ranges 0..N-1
               filled, and zeros for the rest. Build from tracker data. *)
            { Requests.empty_witness with
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
            { Requests.empty_witness with
              accumulator = Some !current_acc
            ; g_chunk = Some g_chunk
            ; lhs_hashes = Some lhs
            ; rhs_hashes = Some rhs
            }
        in
        let input_hash = !current_hash in
        let output_hash, acc_after, lh_after, gv_after, proof =
          Pickles_rules.compile_and_prove_one_with_acc ~vk:vk_const ~n
            ~input_hash ~witness
        in
        hash_pairs.(n) <- (input_hash, output_hash) ;
        proofs.(n) <- Some proof ;
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
              { Requests.empty_witness with
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
              { Requests.empty_witness with public_inputs = Some pis }
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
              { Requests.empty_witness with
                public_inputs = Some pis
              ; pi_point = Some (g1_to_const pi)
              ; partial_ic_acc = Some (g1_to_const partial_acc)
              }
          | _ ->
              Requests.empty_witness
        in
        let input_hash = !current_hash in
        let output_hash, proof =
          Pickles_rules.compile_and_prove_one ~vk:vk_const ~n ~input_hash
            ~witness
        in
        hash_pairs.(n) <- (input_hash, output_hash) ;
        proofs.(n) <- Some proof ;
        current_hash := output_hash
      done ;
      (* Serialize proofs to JSON *)
      let json_proofs =
        Array.mapi proofs ~f:(fun i proof ->
            let module P = Pickles.Proof.Make (Pickles_types.Nat.N0) in
            let proof_str = P.to_base64 (Option.value_exn proof) in
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
end
