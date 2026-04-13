(** Native constant Fp2/Fp6/Fp12 arithmetic over BN254 base field.

    These functions operate on [Bignum_bigint.t] tuples (the Constant types)
    using simple modular arithmetic.  No snarky overhead, no constraints,
    no variable allocation.  Used by [compute-state] to bypass the circuit
    machinery when only the witness values are needed. *)

open! Core_kernel
module BI = Bignum_bigint

let p = Bn254_params.p

(* ==== Fp (mod p) ==== *)

let fp_add a b = BI.((a + b) % p)

let fp_sub a b = BI.((a - b + p) % p)

let fp_mul a b = BI.((a * b) % p)

let fp_neg a = if BI.(equal a zero) then BI.zero else BI.(p - a)

let fp_inv a =
  (* Extended GCD to compute modular inverse *)
  let rec ext_gcd a b =
    if BI.(equal b zero) then (a, BI.one, BI.zero)
    else
      let q = BI.(a / b) in
      let g, x, y = ext_gcd b BI.(a % b) in
      (g, y, BI.(x - (q * y)))
  in
  let _g, x, _y = ext_gcd a p in
  BI.((x % p + p) % p)

(* ==== Fp2 = Fp[u] / (u^2 + 1) ==== *)

module Fp2 = struct
  type t = BI.t * BI.t

  let zero : t = (BI.zero, BI.zero)

  let one : t = (BI.one, BI.zero)

  let add ((a0, a1) : t) ((b0, b1) : t) : t = (fp_add a0 b0, fp_add a1 b1)

  let sub ((a0, a1) : t) ((b0, b1) : t) : t = (fp_sub a0 b0, fp_sub a1 b1)

  let neg ((a0, a1) : t) : t = (fp_neg a0, fp_neg a1)

  let conjugate ((a0, a1) : t) : t = (a0, fp_neg a1)

  (** (a0+a1*u)(b0+b1*u) = (a0*b0 - a1*b1) + (a0*b1 + a1*b0)*u *)
  let mul ((a0, a1) : t) ((b0, b1) : t) : t =
    let c0 = fp_sub (fp_mul a0 b0) (fp_mul a1 b1) in
    let c1 = fp_add (fp_mul a0 b1) (fp_mul a1 b0) in
    (c0, c1)

  let inv ((a0, a1) : t) : t =
    let norm = fp_add (fp_mul a0 a0) (fp_mul a1 a1) in
    let inv_norm = fp_inv norm in
    (fp_mul a0 inv_norm, fp_neg (fp_mul a1 inv_norm))

  let mul_by_fp ((a0, a1) : t) (s : BI.t) : t = (fp_mul a0 s, fp_mul a1 s)

  (** Multiply by non-residue xi = 9 + u *)
  let mul_by_non_residue ((a0, a1) : t) : t =
    let nine = BI.of_int 9 in
    (* (a0+a1*u)(9+u) = (9*a0 - a1) + (a0 + 9*a1)*u *)
    (fp_sub (fp_mul a0 nine) a1, fp_add a0 (fp_mul a1 nine))
end

(* ==== Fp6 = Fp2[v] / (v^3 - xi) ==== *)

module Fp6 = struct
  type t = Fp2.t * Fp2.t * Fp2.t

  let zero : t = (Fp2.zero, Fp2.zero, Fp2.zero)

  let one : t = (Fp2.one, Fp2.zero, Fp2.zero)

  let add ((a0, a1, a2) : t) ((b0, b1, b2) : t) : t =
    (Fp2.add a0 b0, Fp2.add a1 b1, Fp2.add a2 b2)

  let sub ((a0, a1, a2) : t) ((b0, b1, b2) : t) : t =
    (Fp2.sub a0 b0, Fp2.sub a1 b1, Fp2.sub a2 b2)

  let neg ((a0, a1, a2) : t) : t = (Fp2.neg a0, Fp2.neg a1, Fp2.neg a2)

  (** v * (c0, c1, c2) = (xi*c2, c0, c1) *)
  let mul_by_v ((c0, c1, c2) : t) : t = (Fp2.mul_by_non_residue c2, c0, c1)

  (** non_residue * x = xi * x *)
  let mul_by_non_residue (x : Fp2.t) : Fp2.t = Fp2.mul_by_non_residue x

  let mul_by_fp2 ((a0, a1, a2) : t) (b : Fp2.t) : t =
    (Fp2.mul a0 b, Fp2.mul a1 b, Fp2.mul a2 b)

  let mul_by_fp ((a0, a1, a2) : t) (s : BI.t) : t =
    (Fp2.mul_by_fp a0 s, Fp2.mul_by_fp a1 s, Fp2.mul_by_fp a2 s)

  (** Fp6 multiplication (schoolbook with Karatsuba on pairs). *)
  let mul ((a0, a1, a2) : t) ((b0, b1, b2) : t) : t =
    let v0 = Fp2.mul a0 b0 in
    let v1 = Fp2.mul a1 b1 in
    let v2 = Fp2.mul a2 b2 in
    let c0 =
      Fp2.add v0
        (Fp2.mul_by_non_residue
           (Fp2.sub (Fp2.mul (Fp2.add a1 a2) (Fp2.add b1 b2)) (Fp2.add v1 v2)) )
    in
    let c1 =
      Fp2.add
        (Fp2.sub (Fp2.mul (Fp2.add a0 a1) (Fp2.add b0 b1)) (Fp2.add v0 v1))
        (Fp2.mul_by_non_residue v2)
    in
    let c2 =
      Fp2.add
        (Fp2.sub (Fp2.mul (Fp2.add a0 a2) (Fp2.add b0 b2)) (Fp2.add v0 v2))
        v1
    in
    (c0, c1, c2)

  (** Multiply by sparse Fp6: b = (b0, b1, 0). *)
  let mul_by_sparse ((a0, a1, a2) : t) ((b0, b1, _) : t) : t =
    let v0 = Fp2.mul a0 b0 in
    let v1 = Fp2.mul a1 b1 in
    let c0 =
      Fp2.add v0
        (Fp2.mul_by_non_residue (Fp2.sub (Fp2.mul (Fp2.add a1 a2) b1) v1))
    in
    let c1 =
      Fp2.sub (Fp2.mul (Fp2.add a0 a1) (Fp2.add b0 b1)) (Fp2.add v0 v1)
    in
    let c2 =
      Fp2.add (Fp2.sub (Fp2.mul (Fp2.add a0 a2) b0) v0) v1
    in
    (c0, c1, c2)

  let inv ((a0, a1, a2) : t) : t =
    let t0 = Fp2.sub (Fp2.mul a0 a0) (Fp2.mul_by_non_residue (Fp2.mul a1 a2)) in
    let t1 = Fp2.sub (Fp2.mul_by_non_residue (Fp2.mul a2 a2)) (Fp2.mul a0 a1) in
    let t2 = Fp2.sub (Fp2.mul a1 a1) (Fp2.mul a0 a2) in
    let c0 = Fp2.mul a0 t0 in
    let c1 = Fp2.mul a2 t1 in
    let c2 = Fp2.mul a1 t2 in
    let det =
      Fp2.add c0
        (Fp2.mul_by_non_residue (Fp2.add c1 c2))
    in
    let inv_det = Fp2.inv det in
    (Fp2.mul t0 inv_det, Fp2.mul t1 inv_det, Fp2.mul t2 inv_det)
end

(* ==== Fp12 = Fp6[w] / (w^2 - v) ==== *)

module Fp12 = struct
  type t = Fp6.t * Fp6.t

  let one : t = (Fp6.one, Fp6.zero)

  (** Karatsuba multiplication. *)
  let mul ((a0, a1) : t) ((b0, b1) : t) : t =
    let v0 = Fp6.mul a0 b0 in
    let v1 = Fp6.mul a1 b1 in
    let v1_shifted =
      let c0, c1, c2 = v1 in
      (Fp6.mul_by_non_residue c2, c0, c1)
    in
    let c0 = Fp6.add v1_shifted v0 in
    let c1 =
      Fp6.sub (Fp6.sub (Fp6.mul (Fp6.add a0 a1) (Fp6.add b0 b1)) v0) v1
    in
    (c0, c1)

  (** Chung-Hasan SQ2. *)
  let square ((a0, a1) : t) : t =
    let c0_tmp = Fp6.sub a0 a1 in
    let c3 = Fp6.sub a0 (Fp6.mul_by_v a1) in
    let c2 = Fp6.mul a0 a1 in
    let c0_c3 = Fp6.mul c0_tmp c3 in
    let c0 = Fp6.add (Fp6.add c0_c3 c2) (Fp6.mul_by_v c2) in
    let c1 = Fp6.mul_by_fp c2 (BI.of_int 2) in
    (c0, c1)

  let conjugate ((a0, a1) : t) : t = (a0, Fp6.neg a1)

  let inverse ((a0, a1) : t) : t =
    let t0 = Fp6.sub (Fp6.mul a0 a0) (Fp6.mul_by_v (Fp6.mul a1 a1)) in
    let t1 = Fp6.inv t0 in
    (Fp6.mul a0 t1, Fp6.mul (Fp6.neg a1) t1)

  (** Sparse multiply: rhs.c0 = (rhs_c0_c0, 0, 0), rhs.c1 = (rhs_c1_c0, rhs_c1_c1, 0). *)
  let sparse_mul ((a0, a1) : t) ((rhs0, rhs1) : t) : t =
    let rhs_c0_c0, _, _ = rhs0 in
    let t0 = Fp6.mul_by_fp2 a0 rhs_c0_c0 in
    let t1 = Fp6.mul_by_sparse a1 rhs1 in
    let c0 = Fp6.add t0 (Fp6.mul_by_v t1) in
    let t2_fp6 : Fp6.t =
      let r0, _, _ = rhs0 in
      let r10, r11, _ = rhs1 in
      (Fp2.add r0 r10, r11, Fp2.zero)
    in
    let c1 = Fp6.sub (Fp6.mul_by_sparse (Fp6.add a0 a1) t2_fp6) (Fp6.add t0 t1) in
    (c0, c1)

  (** Frobenius endomorphisms using gamma constants from Bn254_params. *)
  let frobenius_pow_p ((c0, c1) : t) : t =
    let (a0, a1, a2), (b0, b1, b2) = (c0, c1) in
    let conj = Fp2.conjugate in
    let g = Bn254_params.gamma_1s in
    let t1 = conj a0 in
    let t2 = Fp2.mul (conj b0) g.(0) in
    let t3 = Fp2.mul (conj a1) g.(1) in
    let t4 = Fp2.mul (conj b1) g.(2) in
    let t5 = Fp2.mul (conj a2) g.(3) in
    let t6 = Fp2.mul (conj b2) g.(4) in
    ((t1, t3, t5), (t2, t4, t6))

  let frobenius_pow_p_squared ((c0, c1) : t) : t =
    let (a0, a1, a2), (b0, b1, b2) = (c0, c1) in
    let g = Bn254_params.gamma_2s in
    let t1 = a0 in
    let t2 = Fp2.mul b0 g.(0) in
    let t3 = Fp2.mul a1 g.(1) in
    let t4 = Fp2.mul b1 g.(2) in
    let t5 = Fp2.mul a2 g.(3) in
    let t6 = Fp2.mul b2 g.(4) in
    ((t1, t3, t5), (t2, t4, t6))

  let frobenius_pow_p_cubed ((c0, c1) : t) : t =
    let (a0, a1, a2), (b0, b1, b2) = (c0, c1) in
    let conj = Fp2.conjugate in
    let g = Bn254_params.gamma_3s in
    let t1 = conj a0 in
    let t2 = Fp2.mul (conj b0) g.(0) in
    let t3 = Fp2.mul (conj a1) g.(1) in
    let t4 = Fp2.mul (conj b1) g.(2) in
    let t5 = Fp2.mul (conj a2) g.(3) in
    let t6 = Fp2.mul (conj b2) g.(4) in
    ((t1, t3, t5), (t2, t4, t6))
end
