(** Shared in-circuit utilities used across the proof-conversion
    sub-libraries. *)

module Step = Pickles.Impls.Step

(** [public_input_typ n] is the [Typ.t] for a public input of [n] field
    elements, matching o1js's [public_input_typ]
    ([Typ.array ~length:n Field.typ]). *)
val public_input_typ :
  int -> (Step.Field.t array, Step.Field.Constant.t array) Step.Typ.t

(** Boolean AND matching o1js's gate placement and reduction order.
    Compound arguments are pre-sealed so the gate sequence is
    independent of R1CS reduction order. *)
val boolean_and : Step.Boolean.var -> Step.Boolean.var -> Step.Boolean.var

(** Boolean OR matching o1js's gate placement and reduction order. *)
val boolean_or : Step.Boolean.var -> Step.Boolean.var -> Step.Boolean.var

(** Emit a [Zero] gate with coefficients [[id; 1; 2; 3; 4; 5; 6]] — a
    marker for bisecting gate-sequence divergence against the reference
    implementation. *)
val marker : int -> unit

(** Wrap a [Typ.t]'s [check] so that it emits a [before] marker gate
    before, and an [after] marker gate after, the original checks. *)
val mark_typ :
  int -> int -> ('var, 'value) Step.Typ.t -> ('var, 'value) Step.Typ.t

(** Replicate o1js's [dummy_constraints]: emit one instance of each EC
    gate type so the Kimchi prover always sees them. *)
val dummy_constraints : unit -> unit

(** [provable_switch typ bools values] selects the element of [values]
    whose corresponding [bools] entry is true. Exactly one [bools]
    entry must be true — not enforced here, the caller is responsible.
    Matches nori's [Provable.switch]. *)
val provable_switch :
  ('var, _) Step.Typ.t -> Step.Field.t array -> 'var array -> 'var
