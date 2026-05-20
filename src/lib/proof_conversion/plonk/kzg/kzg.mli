(** KZG (Kate-Zaverucha-Goldberg) commitment verification.

    Verifies polynomial opening proofs via the BN254 pairing. In the
    recursive circuit the pairing is accumulated rather than verified
    directly. *)

open Proof_conversion_bn254
module FF = Snarky_foreign_field.Foreign_field

(** KZG proof accumulator state. *)
module Accumulator : sig
  type t =
    { a : G1.Circuit.t
    ; neg_b : G1.Circuit.t
    ; shift_power : Pickles.Impls.Step.Field.t
    ; c : Fp12.Circuit.t
    ; c_inv : Fp12.Circuit.t
    }
end

(** KZG state carried through the Miller loop. *)
module State : sig
  type t = { f : Fp12.Circuit.t; lines_digest : Pickles.Impls.Step.Field.t }
end

(** Batch KZG opening: combine multiple opening proofs into a single
    pairing check via a random linear combination. *)
val batch_opening :
     commitments:G1.Circuit.t array
  -> evaluations:FF.Field3.t array
  -> random:FF.Field3.t
  -> G1.Circuit.t * FF.Field3.t
