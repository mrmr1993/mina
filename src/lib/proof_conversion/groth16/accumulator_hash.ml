(** Poseidon hashing of accumulator state for circuit chaining.

    Each circuit witnesses the full accumulator, hashes it to produce
    the public input, runs its computation, then hashes the updated
    accumulator to produce the public output. *)

open! Core_kernel
module Step = Pickles.Impls.Step
module FF = Snarky_foreign_field.Foreign_field
module Sponge = Pickles.Step_main_inputs.Sponge

(** Hash a list of field elements using Poseidon sponge. *)
let poseidon_hash (fields : Step.Field.t array) : Step.Field.t =
  let sponge = Sponge.create Pickles.Step_main_inputs.sponge_params in
  Array.iter fields ~f:(fun x -> Sponge.absorb sponge (`Field x)) ;
  Sponge.squeeze_field sponge

(** Hash a list of Field3 values using Poseidon.
    Each Field3 contributes 3 field elements (its limbs). *)
let hash_field3_list (xs : FF.Field3.t list) : Step.Field.t =
  let fields =
    List.concat_map xs ~f:(fun (l0, l1, l2) ->
        [ FF.Limb.to_field l0; FF.Limb.to_field l1; FF.Limb.to_field l2 ] )
  in
  poseidon_hash (Array.of_list fields)

(** Hash an Fp12 value using packed Poseidon.
    Each Field3 limb (88 bits) is a packed entry; two pack into one field. *)
let hash_fp12 (x : Fp12.Circuit.t) : Step.Field.t =
  let l = 88 in
  let field3_packed (f3 : FF.Field3.t) =
    let l0, l1, l2 = f3 in
    [| (FF.Limb.to_field l0, l)
     ; (FF.Limb.to_field l1, l)
     ; (FF.Limb.to_field l2, l)
    |]
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

(** Native Poseidon hash of a constant Fp12 value, matching
    [hash_fp12] but without circuit overhead. *)
let hash_fp12_const (x : Fp12.Constant.t) : Step.Field.Constant.t =
  let module FF = Snarky_foreign_field.Foreign_field in
  let l = 88 in
  let to_field bi = FF.bignum_to_field_const bi in
  let bi_to_limbs bi =
    let open Bignum_bigint in
    let l0 = bi % FF.two_to_limb in
    let l1 = bi / FF.two_to_limb % FF.two_to_limb in
    let l2 = bi / FF.two_to_2limb in
    [| (to_field l0, l); (to_field l1, l); (to_field l2, l) |]
  in
  let fp2_packed ((c0, c1) : Fp2.Constant.t) =
    Array.concat [ bi_to_limbs c0; bi_to_limbs c1 ]
  in
  let fp6_packed ((c0, c1, c2) : Fp6.Constant.t) =
    Array.concat [ fp2_packed c0; fp2_packed c1; fp2_packed c2 ]
  in
  let g, h = x in
  let packeds = Array.concat [ fp6_packed g; fp6_packed h ] in
  let input : Step.Field.Constant.t Random_oracle_input.Chunked.t =
    { field_elements = [||]; packeds }
  in
  let packed = Random_oracle.pack_input input in
  Random_oracle.hash packed

(** Native Poseidon hash of a constant field array, matching
    [poseidon_hash] but on constants. *)
let poseidon_hash_const (fields : Step.Field.Constant.t array) :
    Step.Field.Constant.t =
  Random_oracle.hash fields
