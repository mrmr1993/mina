(** Native constant Fp2/Fp6/Fp12 arithmetic over the BN254 base field.

    Operates on [Bignum_bigint.t] tuples using plain modular arithmetic —
    no snarky overhead, no constraints. Used to compute witness values
    without the circuit machinery. *)

(** BN254 base field modulus. *)
val p : Bignum_bigint.t

val fp_add : Bignum_bigint.t -> Bignum_bigint.t -> Bignum_bigint.t

val fp_sub : Bignum_bigint.t -> Bignum_bigint.t -> Bignum_bigint.t

val fp_mul : Bignum_bigint.t -> Bignum_bigint.t -> Bignum_bigint.t

val fp_neg : Bignum_bigint.t -> Bignum_bigint.t

(** Modular inverse via extended GCD. *)
val fp_inv : Bignum_bigint.t -> Bignum_bigint.t

module Fp2 : sig
  type t = Bignum_bigint.t * Bignum_bigint.t

  val zero : t

  val one : t

  val add : t -> t -> t

  val sub : t -> t -> t

  val neg : t -> t

  val conjugate : t -> t

  val mul : t -> t -> t

  val inv : t -> t

  val mul_by_fp : t -> Bignum_bigint.t -> t

  (** Multiply by the non-residue [xi = 9 + u]. *)
  val mul_by_non_residue : t -> t
end

module Fp6 : sig
  type t = Fp2.t * Fp2.t * Fp2.t

  val zero : t

  val one : t

  val add : t -> t -> t

  val sub : t -> t -> t

  val neg : t -> t

  (** [v * (c0, c1, c2) = (xi*c2, c0, c1)]. *)
  val mul_by_v : t -> t

  val mul_by_non_residue : Fp2.t -> Fp2.t

  val mul_by_fp2 : t -> Fp2.t -> t

  val mul_by_fp : t -> Bignum_bigint.t -> t

  val mul : t -> t -> t

  (** Multiply by a sparse Fp6 element [(b0, b1, 0)]. *)
  val mul_by_sparse : t -> t -> t

  val inv : t -> t
end

module Fp12 : sig
  type t = Fp6.t * Fp6.t

  val one : t

  val mul : t -> t -> t

  val square : t -> t

  val conjugate : t -> t

  val inverse : t -> t

  val sparse_mul : t -> t -> t

  val frobenius_pow_p : t -> t

  val frobenius_pow_p_squared : t -> t

  val frobenius_pow_p_cubed : t -> t
end

(** Native line evaluation for pairing computation. *)
module Lines : sig
  type affine_cache = { x_over_y : Bignum_bigint.t; y_inv : Bignum_bigint.t }

  val make_affine_cache : x:Bignum_bigint.t -> y:Bignum_bigint.t -> affine_cache

  (** Evaluate a line into a sparse Fp12. *)
  val psi : lambda:Fp2.t -> neg_mu:Fp2.t -> affine_cache -> Fp12.t
end
