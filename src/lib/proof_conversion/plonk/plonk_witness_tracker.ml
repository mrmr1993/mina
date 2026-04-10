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
