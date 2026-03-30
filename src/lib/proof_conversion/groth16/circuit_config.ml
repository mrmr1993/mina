(** Global configuration for Groth16 circuit bodies.

    Set by the proof conversion pipeline before circuit compilation.
    The circuits access this data through closure capture. *)

(** Optional witness tracker — set when processing real proof data. *)
let tracker : Witness_tracker.t option ref = ref None

(** Set the tracker for circuit witness access. *)
let set_tracker t = tracker := Some t

(** Get the tracker, or None if running without real data. *)
let get_tracker () = !tracker
