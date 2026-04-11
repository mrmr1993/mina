(** Dump witnesses for Groth16 circuit 0 (first ate circuit) for comparison. *)
open Core_kernel

module Step = Pickles.Impls.Step
module WT = Proof_conversion.Witness_tracker

let () =
  Printf.eprintf "=== Dumping Groth16 circuit 0 witness ===\n%!" ;
  let proof =
    Proof_conversion.Proof_json.load_proof "/tmp/groth16_test/proof.json"
  in
  let vk = Proof_conversion.Proof_json.load_vk "/tmp/groth16_test/vk.json" in
  let aux =
    Proof_conversion.Proof_json.load_aux_witness
      "/tmp/groth16_test/aux_witness.json"
  in
  let tracker = WT.create ~proof ~vk ~aux in
  Proof_conversion.Circuit_config.set_tracker tracker ;
  let vk_const = Proof_conversion.Vk_constants.create vk in
  let n_total = Array.length Proof_conversion.Bn254_params.ate_loop_count in
  let initial_g_digest =
    let zeros = Array.create ~len:n_total Step.Field.Constant.zero in
    Random_oracle.hash zeros
  in
  let initial_acc = WT.get_accumulator_constant tracker in
  let initial_acc =
    { initial_acc with
      state =
        { g_digest = initial_g_digest
        ; t_point = initial_acc.proof.b
        ; f = Proof_conversion.Fp12.Constant.one
        }
    }
  in
  let initial_hash =
    Step.run_and_check_exn (fun () ->
        let acc =
          Step.exists Proof_conversion.Accumulator.typ ~compute:(fun () ->
              initial_acc )
        in
        let h = Proof_conversion.Accumulator.hash acc in
        fun () -> Step.As_prover.read_var h )
  in
  let b_lines = WT.get_all_b_lines tracker in
  (* Disable constraint evaluation so circuit 0 proving succeeds even with DUMP *)
  Snarky_backendless.Snark0.set_eval_constraints false ;
  let witness : Proof_conversion.Groth16_requests.witness =
    { Proof_conversion.Groth16_requests.empty_witness with
      accumulator = Some initial_acc
    ; line_hashes = Some (Array.create ~len:n_total Step.Field.Constant.zero)
    ; b_lines =
        Some (Array.map b_lines ~f:(fun (l : WT.Line.t) -> (l.lambda, l.neg_mu)))
    }
  in
  Printf.eprintf "Proving circuit 0 with DUMP_WITNESS...\n%!" ;
  let output_hash, _proof =
    Proof_conversion.Pickles_rules.compile_and_prove_one ~vk:vk_const ~n:0
      ~input_hash:initial_hash ~witness
  in
  Printf.eprintf "Circuit 0 proved. Output: %s\n%!"
    (Step.Field.Constant.to_string output_hash) ;
  Printf.eprintf "Witness dumped to DUMP_WITNESS path.\n%!" ;
  ignore vk_const ;
  Printf.eprintf "Done.\n%!"
