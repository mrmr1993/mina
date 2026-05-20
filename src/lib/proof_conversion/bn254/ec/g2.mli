(** G2 affine point operations on BN254. *)

module Constant : sig
  type t = { x : Fp2.Constant.t; y : Fp2.Constant.t }
end

module Circuit : sig
  type t = { x : Fp2.Circuit.t; y : Fp2.Circuit.t }

  val typ : (t, Constant.t) Pickles.Impls.Step.Typ.t
end

val of_constant : Constant.t -> Circuit.t

val negate : Circuit.t -> Circuit.t

(** Affine addition of two distinct non-zero G2 points. *)
val add_nonzero : Circuit.t -> Circuit.t -> Circuit.t

(** Frobenius endomorphism on G2. *)
val frobenius : Circuit.t -> Circuit.t

(** [-gamma_1s.(2)], the pre-negated constant used by
    {!negative_frobenius}. *)
val neg_gamma_1s_2 : Fp2.Constant.t

(** Negative Frobenius endomorphism on G2. *)
val negative_frobenius : Circuit.t -> Circuit.t

(** Point doubling from a known tangent-line slope. *)
val double_from_line : Circuit.t -> lambda:Fp2.Circuit.t -> Circuit.t

(** Point addition from a known line slope. *)
val add_from_line : Circuit.t -> lambda:Fp2.Circuit.t -> Circuit.t -> Circuit.t
