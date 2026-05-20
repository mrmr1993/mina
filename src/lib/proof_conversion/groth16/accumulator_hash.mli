(** Poseidon hashing of accumulator state for circuit chaining.

    Each circuit hashes the witnessed accumulator to its public input,
    runs its computation, and hashes the updated accumulator to its
    public output. *)

open Proof_conversion_bn254
module Step = Pickles.Impls.Step
module FF = Snarky_foreign_field.Foreign_field

(** Hash a field-element array using the Poseidon sponge. *)
val poseidon_hash : Step.Field.t array -> Step.Field.t

(** Hash a list of Field3 values (3 field elements each). *)
val hash_field3_list : FF.Field3.t list -> Step.Field.t

(** Hash an Fp12 value using packed Poseidon. *)
val hash_fp12 : Fp12.Circuit.t -> Step.Field.t

(** Combine multiple hashes into a single hash. *)
val combine_hashes : Step.Field.t list -> Step.Field.t

(** Native Poseidon hash of a constant Fp12 value, matching
    {!hash_fp12} without circuit overhead. *)
val hash_fp12_const : Fp12.Constant.t -> Step.Field.Constant.t

(** Native Poseidon hash of a constant field array. *)
val poseidon_hash_const : Step.Field.Constant.t array -> Step.Field.Constant.t
