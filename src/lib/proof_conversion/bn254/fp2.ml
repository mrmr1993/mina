(** Fp2 = Fp[u] / (u^2 + 1) arithmetic over BN254 base field.

    Elements are pairs (c0, c1) representing c0 + c1 * u where u^2 = -1. *)

open Snarky_foreign_field.Foreign_field

let p = Bn254_params.p

(** Fp2 element as a pair of Field3 values. *)
module Circuit = struct
  type t = { c0 : Field3.t; c1 : Field3.t }
end

(** Constant Fp2 element as bignum pairs. *)
module Constant = struct
  type t = Bignum_bigint.t * Bignum_bigint.t

  let zero : t = (Bignum_bigint.zero, Bignum_bigint.zero)

  let one : t = (Bignum_bigint.one, Bignum_bigint.zero)
end

let of_constant ((c0, c1) : Constant.t) : Circuit.t =
  { c0 = Field3.of_constant c0; c1 = Field3.of_constant c1 }

(** Addition: (a0+a1*u) + (b0+b1*u) = (a0+b0) + (a1+b1)*u *)
let add (a : Circuit.t) (b : Circuit.t) : Circuit.t =
  { c0 = add a.c0 b.c0 ~f:p; c1 = add a.c1 b.c1 ~f:p }

(** Subtraction. *)
let sub (a : Circuit.t) (b : Circuit.t) : Circuit.t =
  { c0 = sub a.c0 b.c0 ~f:p; c1 = sub a.c1 b.c1 ~f:p }

(** Negation. *)
let neg (a : Circuit.t) : Circuit.t =
  { c0 = negate a.c0 ~f:p; c1 = negate a.c1 ~f:p }

(** Conjugate: (a0 + a1*u)* = a0 - a1*u *)
let conjugate (a : Circuit.t) : Circuit.t =
  { c0 = a.c0; c1 = negate a.c1 ~f:p }

(** Multiplication: (a0+a1*u)(b0+b1*u) = (a0*b0 - a1*b1) + (a0*b1 + a1*b0)*u
    Uses the Karatsuba-like trick:
      c0 = a0*b0 - a1*b1
      c1 = (a0+a1)*(b0+b1) - a0*b0 - a1*b1 *)
let mul (a : Circuit.t) (b : Circuit.t) : Circuit.t =
  let v0 = mul a.c0 b.c0 ~f:p in
  let v1 = mul a.c1 b.c1 ~f:p in
  let c0 = sub v0 v1 ~f:p in
  let a01 = add a.c0 a.c1 ~f:p in
  let b01 = add b.c0 b.c1 ~f:p in
  let t = mul a01 b01 ~f:p in
  let c1 = sub (sub t v0 ~f:p) v1 ~f:p in
  { c0; c1 }

(** Squaring: (a0+a1*u)^2 = (a0+a1)(a0-a1) + 2*a0*a1*u *)
let square (a : Circuit.t) : Circuit.t =
  let sum_ = add a.c0 a.c1 ~f:p in
  let diff = sub a.c0 a.c1 ~f:p in
  let c0 = mul sum_ diff ~f:p in
  let prod = mul a.c0 a.c1 ~f:p in
  let c1 = add prod prod ~f:p in
  { c0; c1 }

(** Multiply Fp2 element by an Fp scalar. *)
let mul_by_fp (a : Circuit.t) (s : Field3.t) : Circuit.t =
  { c0 = mul a.c0 s ~f:p; c1 = mul a.c1 s ~f:p }

(** Inverse: (a0+a1*u)^{-1} = (a0-a1*u) / (a0^2+a1^2) *)
let inverse (a : Circuit.t) : Circuit.t =
  let a0_sq = mul a.c0 a.c0 ~f:p in
  let a1_sq = mul a.c1 a.c1 ~f:p in
  let norm = add a0_sq a1_sq ~f:p in
  let norm_inv = inv norm ~f:p in
  { c0 = mul a.c0 norm_inv ~f:p
  ; c1 = negate (mul a.c1 norm_inv ~f:p) ~f:p
  }

(** Frobenius endomorphism: conjugation for Fp2 over BN254.
    phi(a0 + a1*u) = a0 - a1*u (since u^p = -u for BN254). *)
let frobenius (a : Circuit.t) : Circuit.t = conjugate a

(** Assert two Fp2 elements are equal. *)
let assert_equal (a : Circuit.t) (b : Circuit.t) : unit =
  assert_equal a.c0 b.c0 ;
  assert_equal a.c1 b.c1
