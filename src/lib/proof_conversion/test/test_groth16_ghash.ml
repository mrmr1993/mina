(** Test: compare tracker g_value hashes with circuit-computed line_hashes. *)
open Core_kernel

module Step = Pickles.Impls.Step
module WT = Proof_conversion.Groth16.Witness_tracker

let () =
  let proof =
    Proof_conversion.Groth16.Proof_json.load_proof "/tmp/groth16_test/proof.json"
  in
  let vk = Proof_conversion.Groth16.Proof_json.load_vk "/tmp/groth16_test/vk.json" in
  let aux =
    Proof_conversion.Groth16.Proof_json.load_aux_witness
      "/tmp/groth16_test/aux_witness.json"
  in
  let tracker = WT.create ~proof ~vk ~aux in
  Proof_conversion.Groth16.Circuit_config.set_tracker tracker ;
  let vk_const = Proof_conversion.Groth16.Vk_constants.create vk in
  (* Get initial accumulator *)
  let initial_acc = WT.get_accumulator_constant tracker in
  let n_total = Array.length Proof_conversion.Bn254.Bn254_params.ate_loop_count in
  let initial_g_digest =
    let zeros = Array.create ~len:n_total Step.Field.Constant.zero in
    Random_oracle.hash zeros
  in
  let initial_acc =
    { initial_acc with
      state =
        { g_digest = initial_g_digest
        ; t_point = initial_acc.proof.b
        ; f = Proof_conversion.Bn254.Fp12.Constant.one
        }
    }
  in
  (* Prove circuit 0 with acc chaining to get circuit-computed line_hashes *)
  let fp_to_field h =
    Step.Field.Constant.of_string (Kimchi_pasta.Pasta.Fp.to_string h)
  in
  let _line_hashes = WT.get_line_hashes tracker in
  let b_lines = WT.get_all_b_lines tracker in
  let witness : Proof_conversion.Groth16.Requests.witness =
    { Proof_conversion.Groth16.Requests.empty_witness with
      accumulator = Some initial_acc
    ; line_hashes = Some (Array.create ~len:n_total Step.Field.Constant.zero)
    ; b_lines =
        Some (Array.map b_lines ~f:(fun (l : WT.Line.t) -> (l.lambda, l.neg_mu)))
    }
  in
  let initial_hash =
    Step.run_and_check_exn (fun () ->
        let acc =
          Step.exists Proof_conversion.Groth16.Accumulator.typ ~compute:(fun () ->
              initial_acc )
        in
        let h = Proof_conversion.Groth16.Accumulator.hash acc in
        fun () -> Step.As_prover.read_var h )
  in
  Printf.eprintf "Proving circuit 0 to get line_hashes...\n%!" ;
  let _, _, lh_from_circuit, _, _ =
    Proof_conversion.Groth16.Pickles_rules.compile_and_prove_one_with_acc ~vk:vk_const
      ~n:0 ~input_hash:initial_hash ~witness
  in
  Printf.eprintf "Circuit 0 proved.\n%!" ;
  (* Compare circuit line_hashes entries with tracker g_value hashes *)
  let g_values = WT.get_g_values tracker in
  let ranges = Proof_conversion.Groth16.Ate_circuit.circuit_ranges in
  let begin_idx, end_idx = ranges.(0) in
  Printf.eprintf "Circuit 0 range: [%d, %d)\n%!" begin_idx end_idx ;
  let mismatches = ref 0 in
  for i = begin_idx to end_idx - 1 do
    let idx = i - 1 in
    let circuit_hash = lh_from_circuit.(idx) in
    let tracker_hash =
      fp_to_field (WT.hash_fp12_out_of_circuit g_values.(idx))
    in
    if not (Step.Field.Constant.equal circuit_hash tracker_hash) then (
      Printf.eprintf "  MISMATCH at idx %d: circuit=%s tracker=%s\n%!" idx
        (Step.Field.Constant.to_string circuit_hash)
        (Step.Field.Constant.to_string tracker_hash) ;
      incr mismatches )
  done ;
  if !mismatches = 0 then
    Printf.eprintf "All %d g_value hashes match!\n%!" (end_idx - begin_idx)
  else Printf.eprintf "%d mismatches found.\n%!" !mismatches ;
  Printf.eprintf "Done.\n%!"
