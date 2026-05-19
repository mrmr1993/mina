(** Global configuration for Groth16 circuit bodies.

    Set by the proof conversion pipeline before circuit compilation.
    The circuits access this data through closure capture. *)

open! Core_kernel

(** Optional witness tracker — set when processing real proof data. *)
let tracker : Witness_tracker.t option ref = ref None

(** Set the tracker for circuit witness access. *)
let set_tracker t = tracker := Some t

(** Get the tracker. Fails if called without a tracker set —
    this should only be called from within [exists ~compute] closures
    during proving, where a tracker is always present. *)
let get_tracker () =
  match !tracker with
  | Some t ->
      t
  | None ->
      failwith "Circuit_config.get_tracker: no tracker set"
