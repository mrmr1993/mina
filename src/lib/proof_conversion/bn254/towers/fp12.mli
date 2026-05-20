(** Fp12 = Fp6[w] / (w^2 - v) arithmetic over BN254.

    Elements are pairs [(c0, c1)] representing [c0 + c1*w] with [w^2 = v].
    This is the target field of the BN254 pairing. *)

module Constant : sig
  type t = Fp6.Constant.t * Fp6.Constant.t

  val one : t
end

module Circuit : sig
  type t = { c0 : Fp6.Circuit.t; c1 : Fp6.Circuit.t }

  val typ : (t, Constant.t) Pickles.Impls.Step.Typ.t
end

val of_constant : Constant.t -> Circuit.t

val add : Circuit.t -> Circuit.t -> Circuit.t

val sub : Circuit.t -> Circuit.t -> Circuit.t

val neg : Circuit.t -> Circuit.t

(** Karatsuba multiplication. *)
val mul : Circuit.t -> Circuit.t -> Circuit.t

(** Chung-Hasan SQ2 squaring. *)
val square : Circuit.t -> Circuit.t

(** Conjugate: [(a0 + a1*w)* = a0 - a1*w]. *)
val conjugate : Circuit.t -> Circuit.t

(** Unitary inverse (for cyclotomic-subgroup elements): equals
    [conjugate]. *)
val unitary_inverse : Circuit.t -> Circuit.t

(** Full Fp12 inverse. *)
val inverse : Circuit.t -> Circuit.t

(** Sparse multiplication; the RHS has the sparse line structure. *)
val sparse_mul : Circuit.t -> Circuit.t -> Circuit.t

val assert_equal : Circuit.t -> Circuit.t -> unit

val one : Circuit.t

val assert_one : Circuit.t -> unit

(** [Typ.t] for Fp12 with range checks on each FpA component. *)
val typ : (Circuit.t, Constant.t) Pickles.Impls.Step.Typ.t

(** Witness an Fp12 value using {!typ}. *)
val witness : unit -> Circuit.t

(** Cyclotomic squaring (currently general squaring). *)
val cyclotomic_square : Circuit.t -> Circuit.t

(** Frobenius endomorphism [f^p]. *)
val frobenius_pow_p : Circuit.t -> Circuit.t

(** Frobenius endomorphism squared [f^(p^2)]. *)
val frobenius_pow_p_squared : Circuit.t -> Circuit.t

(** Frobenius endomorphism cubed [f^(p^3)]. *)
val frobenius_pow_p_cubed : Circuit.t -> Circuit.t

(** Cyclotomic exponentiation by a small NAF-form exponent. *)
val cyclotomic_pow : Circuit.t -> exp:int array -> Circuit.t
