(** Convert a SHA-256 digest to a BN254 scalar field element.

    Matches nori's [shaToFr]: the 256-bit digest is read big-endian and
    the top 2 bits are folded in via conditional modular additions. *)

module FF = Snarky_foreign_field.Foreign_field
module Step = Pickles.Impls.Step

(** [2^254 mod r]. *)
val two_254_mod_r : Bignum_bigint.t

(** [2^255 mod r]. *)
val two_255_mod_r : Bignum_bigint.t

(** Convert a 32-byte SHA-256 digest to a canonical BN254 scalar. *)
val sha_to_fr : Step.Field.t array -> FF.FpA.t
