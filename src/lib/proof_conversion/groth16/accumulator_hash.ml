(** Poseidon hashing of accumulator state for circuit chaining.

    Each circuit witnesses the full accumulator, hashes it to produce
    the public input, runs its computation, then hashes the updated
    accumulator to produce the public output. *)

open! Core_kernel
module Step = Pickles.Impls.Step
module FF = Snarky_foreign_field.Foreign_field
module Sponge = Pickles.Step_main_inputs.Sponge

(** Hash a list of field elements using Poseidon sponge.
    Uses Poseidon.update (batch absorb) matching o1js Poseidon.hash(). *)
let poseidon_hash (fields : Step.Field.t array) : Step.Field.t =
  let sponge = Sponge.create Pickles.Step_main_inputs.sponge_params in
  Array.iter fields ~f:(fun x -> Sponge.absorb sponge (`Field x)) ;
  Sponge.squeeze_field sponge

(** Hash a list of Field3 values using Poseidon.
    Each Field3 contributes 3 field elements (its limbs). *)
let hash_field3_list (xs : FF.Field3.t list) : Step.Field.t =
  let fields = List.concat_map xs ~f:(fun (l0, l1, l2) -> [ l0; l1; l2 ]) in
  poseidon_hash (Array.of_list fields)

(** Hash an Fp12 value (12 Fp2 components = 36 field elements). *)
let hash_fp12 (x : Fp12.Circuit.t) : Step.Field.t =
  hash_field3_list
    [ x.c0.c0.c0
    ; x.c0.c0.c1
    ; x.c0.c1.c0
    ; x.c0.c1.c1
    ; x.c0.c2.c0
    ; x.c0.c2.c1
    ; x.c1.c0.c0
    ; x.c1.c0.c1
    ; x.c1.c1.c0
    ; x.c1.c1.c1
    ; x.c1.c2.c0
    ; x.c1.c2.c1
    ]

(** Combine multiple hashes into a single hash. *)
let combine_hashes (hashes : Step.Field.t list) : Step.Field.t =
  poseidon_hash (Array.of_list hashes)
