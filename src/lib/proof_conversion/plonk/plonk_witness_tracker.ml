(** Out-of-circuit computation for PLONK proof conversion witnesses.

    Computes values needed by the prover (e.g., Poseidon hashes of
    accumulator state) without circuit constraints. *)

open! Core_kernel
module Step = Pickles.Impls.Step

(** Compute the Poseidon hash of an accumulator constant, matching
    in-circuit hash_packed. Uses run_and_check to evaluate the
    circuit-level hash on constant inputs. *)
let hash_accumulator_const (acc_const : Plonk_accumulator.t_const) :
    Step.Field.Constant.t =
  Step.run_and_check_exn (fun () ->
      let acc =
        Step.exists Plonk_accumulator.typ ~compute:(fun () -> acc_const)
      in
      let h = Plonk_accumulator.hash_packed acc in
      fun () -> Step.As_prover.read_var h )

(** Run a circuit via run_unchecked with a witness handler.
    Returns the output hash. *)
let run_circuit_unchecked ~(n : int) ~(input_hash : Step.Field.Constant.t)
    ~(witness : Plonk_requests.witness) : Step.Field.Constant.t =
  let handler = Plonk_requests.handler witness in
  Step.run_unchecked (fun () ->
      Step.handle
        (fun () ->
          let body = Plonk_circuits.circuit_body n in
          let input_var = Step.Field.constant input_hash in
          let output_var = body input_var in
          Step.As_prover.read_var output_var )
        handler )

(** Run circuits 0-11 unchecked to evolve the PLONK accumulator,
    then extract KZG A/B points from circuit 12 and compute the
    Miller loop output via Rust FFI. Returns the Fp12 MLO. *)
let compute_kzg_mlo (initial_acc : Plonk_accumulator.t_const) : Fp12.Constant.t
    =
  let module FF = Snarky_foreign_field.Foreign_field in
  (* Disable constraint evaluation for speed *)
  Snarky_backendless.Snark0.set_eval_constraints false ;
  (* Run circuits 0-11 to evolve the accumulator *)
  let current_hash = ref (hash_accumulator_const initial_acc) in
  let current_acc = ref initial_acc in
  let zkp_fns =
    Plonk_circuits.
      [| zkp0
       ; zkp1
       ; zkp2
       ; zkp3
       ; zkp4
       ; zkp5
       ; zkp6
       ; zkp7
       ; zkp8
       ; zkp9
       ; zkp10
       ; zkp11
      |]
  in
  for n = 0 to 11 do
    Printf.eprintf "  Running zkp%d unchecked...\n%!" n ;
    let witness : Plonk_requests.witness =
      { Plonk_requests.empty_witness with plonk_acc = Some !current_acc }
    in
    let handler = Plonk_requests.handler witness in
    let result = ref (Step.Field.Constant.zero, !current_acc) in
    Step.run_unchecked (fun () ->
        Step.handle
          (fun () ->
            let input_var = Step.Field.constant !current_hash in
            let output_hash, acc = zkp_fns.(n) input_var in
            Step.as_prover (fun () ->
                let oh = Step.As_prover.read_var output_hash in
                let acc_const = Step.As_prover.read Plonk_accumulator.typ acc in
                result := (oh, acc_const) ) )
          handler ) ;
    let output_hash, new_acc = !result in
    current_hash := output_hash ;
    current_acc := new_acc
  done ;
  (* Run circuit 12's logic unchecked to get KZG A/B points.
     c/shift_power don't affect A/B computation. *)
  let witness : Plonk_requests.witness =
    { Plonk_requests.empty_witness with
      plonk_acc = Some !current_acc
    ; shift_power = Some Step.Field.Constant.zero
    ; c_fp12 = Some Fp12.Constant.one
    }
  in
  let handler = Plonk_requests.handler witness in
  let module BI = Bignum_bigint in
  let kzg_result = ref (BI.zero, BI.zero, BI.zero, BI.zero) in
  Step.run_unchecked (fun () ->
      Step.handle
        (fun () ->
          let _output_hash, kzg =
            Plonk_circuits.zkp12 (Step.Field.constant !current_hash)
          in
          Step.as_prover (fun () ->
              let read_fpa f =
                Step.As_prover.read (FF.FpA.typ ~f:Bn254_params.p) f
              in
              let ax = read_fpa kzg.proof.a_x in
              let ay = read_fpa kzg.proof.a_y in
              let nbx = read_fpa kzg.proof.neg_b_x in
              let nby = read_fpa kzg.proof.neg_b_y in
              kzg_result := (ax, ay, nbx, nby) ) )
        handler ) ;
  let a_x, a_y, neg_b_x, neg_b_y = !kzg_result in
  Snarky_backendless.Snark0.set_eval_constraints true ;
  (* FpA reads as Field3.Constant.t = Bignum_bigint.t directly *)
  Pairing_utils_bridge.compute_kzg_mlo ~a_x ~a_y ~neg_b_x ~neg_b_y
