(** Global configuration for Groth16 circuit bodies.

    Set by the proof-conversion pipeline before circuit compilation; the
    circuits read it through closure capture. *)

(** Optional witness tracker — set when processing real proof data. *)
val tracker : Witness_tracker.t option ref

(** Set the tracker for circuit witness access. *)
val set_tracker : Witness_tracker.t -> unit

(** Get the tracker. Fails if no tracker has been set — only valid
    inside [exists ~compute] closures during proving. *)
val get_tracker : unit -> Witness_tracker.t
