(** Fp2 = Fp[u] / (u^2 + 1) arithmetic over the BN254 base field.

    Elements are pairs [(c0, c1)] representing [c0 + c1 * u] with
    [u^2 = -1]. *)

module FF = Snarky_foreign_field.Foreign_field
module FpA = FF.FpA

module Constant : sig
  type t = FF.Bignum_bigint.t * FF.Bignum_bigint.t

  val zero : t

  val one : t
end

module Circuit : sig
  type t = { c0 : FpA.t; c1 : FpA.t }

  (** Witnessing applies MRC + weakBound to each component. *)
  val typ : (t, Constant.t) Pickles.Impls.Step.Typ.t
end

val of_constant : Constant.t -> Circuit.t

(** Convert an unreduced pair to an Fp2 circuit value. *)
val from_unreduced : FF.FpU.t -> FF.FpU.t -> Circuit.t

val add : Circuit.t -> Circuit.t -> Circuit.t

val sub : Circuit.t -> Circuit.t -> Circuit.t

(** Batched sum/difference of multiple Fp2 values via a single
    [FF.sum] chain per component. *)
val sum : Circuit.t list -> FF.sign list -> Circuit.t

val neg : Circuit.t -> Circuit.t

val conjugate : Circuit.t -> Circuit.t

val mul : Circuit.t -> Circuit.t -> Circuit.t

val square : Circuit.t -> Circuit.t

(** Multiply by an Fp scalar (already reduced to [FpA.t]). *)
val mul_by_fp : Circuit.t -> FpA.t -> Circuit.t

val inverse : Circuit.t -> Circuit.t

(** Frobenius endomorphism on Fp2 (= conjugation). *)
val frobenius : Circuit.t -> Circuit.t

val assert_equal : Circuit.t -> Circuit.t -> unit
