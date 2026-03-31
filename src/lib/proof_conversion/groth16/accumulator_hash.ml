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

(** Hash an Fp12 value using packed Poseidon, matching
    o1js Poseidon.hashPacked(Fp12, x).
    Each Field3 limb (88 bits) is a packed entry; two pack into one field. *)
let hash_fp12 (x : Fp12.Circuit.t) : Step.Field.t =
  let l = 88 in
  let field3_packed (f3 : FF.Field3.t) =
    let l0, l1, l2 = f3 in
    [| (l0, l); (l1, l); (l2, l) |]
  in
  let fp2_packed (fp2 : Fp2.Circuit.t) =
    Array.concat
      [ field3_packed (FF.FpA.to_field3 fp2.c0)
      ; field3_packed (FF.FpA.to_field3 fp2.c1)
      ]
  in
  let fp6_packed (fp6 : Fp6.Circuit.t) =
    Array.concat [ fp2_packed fp6.c0; fp2_packed fp6.c1; fp2_packed fp6.c2 ]
  in
  let packeds = Array.concat [ fp6_packed x.c0; fp6_packed x.c1 ] in
  let input : Step.Field.t Random_oracle_input.Chunked.t =
    { field_elements = [||]; packeds }
  in
  let packed_fields = Random_oracle.Checked.pack_input input in
  Random_oracle.Checked.hash packed_fields

(** Combine multiple hashes into a single hash. *)
let combine_hashes (hashes : Step.Field.t list) : Step.Field.t =
  poseidon_hash (Array.of_list hashes)
