(** f-update circuit body shared by zkp7-12.

    Each circuit performs cyclotomic squarings on [f], multiplying in
    the [g] values from line accumulation and conditionally multiplying
    by [c] or [c_inv] based on the ate-loop count bits. *)

module Step = Pickles.Impls.Step

(** Ate-loop iterations processed per f-update circuit. *)
val iterations_per_circuit : int array

(** Cumulative g-start offsets per f-update circuit. *)
val g_start_per_circuit : int array

(** Build the f-update circuit body for [circuit_index] (7-12);
    returns the output hash. *)
val build : circuit_index:int -> Step.Field.t -> Step.Field.t

(** As {!build} but also returns the updated accumulator for
    aux-output chaining. *)
val build_with_acc :
  circuit_index:int -> Step.Field.t -> Step.Field.t * Accumulator.Circuit.t
