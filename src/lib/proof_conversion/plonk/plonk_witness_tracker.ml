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
