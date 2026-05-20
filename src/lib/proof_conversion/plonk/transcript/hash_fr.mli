(** BSB22-PLONK hash-to-field: hash two BN254 base-field elements to a
    scalar-field element.

    Matches nori's [HashFr] (3 SHA-256 hashes + XOR + bit manipulation). *)

module FF = Snarky_foreign_field.Foreign_field
module Step = Pickles.Impls.Step

(** BN254 scalar field modulus. *)
val r : Bignum_bigint.t

(** Range-check a Field3 below [r] and reinterpret it as canonical FrA. *)
val assert_canonical_fr : FF.Field3.t -> FF.FpA.t

val mul_fr : FF.FpA.t -> FF.FpA.t -> FF.FpA.t

val add_fr : FF.FpA.t -> FF.FpA.t -> FF.FpA.t

val hash_fr_len_in_bytes : int array

val hash_fr_size_domain : int array

(** "BSB22-Plonk" in ASCII. *)
val bsb22_plonk : int array

(** XOR two 32-byte SHA outputs byte-by-byte. *)
val xor_sha_outputs :
  Step.Field.t array -> Step.Field.t array -> Step.Field.t array

(** Convert the lower 128 bits of a SHA digest to FrA. *)
val shr128 : Step.Field.t array -> FF.FpA.t

(** Shift left by 128 mod r. *)
val shl_128_mod_r : Step.Field.t array -> FF.FpA.t

(** BSB22-PLONK hash of two BN254 Fp elements to an Fr element. *)
val hash : FF.FpA.t -> FF.FpA.t -> FF.FpA.t
