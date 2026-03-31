(** Fp12 = Fp6[w] / (w^2 - v) arithmetic over BN254.

    Elements are pairs (c0, c1) representing c0 + c1*w where w^2 = v.
    This is the target field of the BN254 pairing. *)

open! Core_kernel

module Constant = struct
  type t = Fp6.Constant.t * Fp6.Constant.t
end

(** Fp12 element as a pair of Fp6 values. *)
module Circuit = struct
  type t = { c0 : Fp6.Circuit.t; c1 : Fp6.Circuit.t }

  let typ : (t, Constant.t) Pickles.Impls.Step.Typ.t =
    Pickles.Impls.Step.Typ.transport
      (Pickles.Impls.Step.Typ.tuple2 Fp6.Circuit.typ Fp6.Circuit.typ)
      ~there:(fun (c0, c1) -> (c0, c1))
      ~back:(fun (c0, c1) -> (c0, c1))
    |> Pickles.Impls.Step.Typ.transport_var
         ~there:(fun { c0; c1 } -> (c0, c1))
         ~back:(fun (c0, c1) -> { c0; c1 })
end

(** Addition. *)
let add (a : Circuit.t) (b : Circuit.t) : Circuit.t =
  { c0 = Fp6.add a.c0 b.c0; c1 = Fp6.add a.c1 b.c1 }

(** Subtraction. *)
let sub (a : Circuit.t) (b : Circuit.t) : Circuit.t =
  { c0 = Fp6.sub a.c0 b.c0; c1 = Fp6.sub a.c1 b.c1 }

(** Negation. *)
let neg (a : Circuit.t) : Circuit.t = { c0 = Fp6.neg a.c0; c1 = Fp6.neg a.c1 }

(** Multiplication using Karatsuba:
    (a0 + a1*w)(b0 + b1*w) = (a0*b0 + a1*b1*v) + (a0*b1 + a1*b0)*w
    where a1*b1*v is computed via mul_by_non_residue on the Fp6 level
    (shifting c2*v^2 -> c0*xi, etc.) *)
let mul (a : Circuit.t) (b : Circuit.t) : Circuit.t =
  let v0 = Fp6.mul a.c0 b.c0 in
  let v1 = Fp6.mul a.c1 b.c1 in
  (* c0 = v0 + v1 * v, where v1*v shifts Fp6 coefficients *)
  let v1_shifted : Fp6.Circuit.t =
    { c0 = Fp6.mul_by_non_residue v1.c2; c1 = v1.c0; c2 = v1.c1 }
  in
  let c0 = Fp6.add v0 v1_shifted in
  let a01 = Fp6.add a.c0 a.c1 in
  let b01 = Fp6.add b.c0 b.c1 in
  let t = Fp6.mul a01 b01 in
  let c1 = Fp6.sub (Fp6.sub t v0) v1 in
  { c0; c1 }

(** Squaring. *)
let square (a : Circuit.t) : Circuit.t = mul a a

(** Conjugate: (a0 + a1*w)* = a0 - a1*w *)
let conjugate (a : Circuit.t) : Circuit.t = { c0 = a.c0; c1 = Fp6.neg a.c1 }

(** Unitary inverse (for elements on the cyclotomic subgroup):
    inv(a) = conjugate(a) since |a| = 1. *)
let unitary_inverse (a : Circuit.t) : Circuit.t = conjugate a

(** Sparse multiplication matching nori's Fp12.sparse_mul().
    The RHS has structure: c0 = (b00, 0, 0), c1 = (b10, b11, 0).

    This is used for multiplying by line evaluation results where
    b00 = 1 (or another Fp2 constant), b10 = lambda * x/y,
    b11 = neg_mu / y.

    Uses Fp6.mul_by_fp2 and Fp6.mul_by_sparse_fp6 for efficiency. *)
let sparse_mul (a : Circuit.t) ~(b00 : Fp2.Constant.t) ~(b10 : Fp2.Circuit.t)
    ~(b11 : Fp2.Circuit.t) : Circuit.t =
  let b00_c = Fp2.of_constant b00 in
  let t0 = Fp6.mul_by_fp2 a.c0 b00_c in
  let t1 = Fp6.mul_by_sparse a.c1 b10 b11 in
  let t1_shifted : Fp6.Circuit.t =
    { c0 = Fp6.mul_by_non_residue t1.c2; c1 = t1.c0; c2 = t1.c1 }
  in
  let c0 = Fp6.add t0 t1_shifted in
  let t2_c0 = Fp2.add b00_c b10 in
  let t2 = Fp6.mul_by_sparse (Fp6.add a.c0 a.c1) t2_c0 b11 in
  let c1 = Fp6.sub (Fp6.sub t2 t0) t1 in
  { c0; c1 }

(** Legacy mul_by_line — use sparse_mul instead. *)
let mul_by_line (_a : Circuit.t) ~(c01 : Fp2.Circuit.t) ~(c11 : Fp2.Circuit.t) :
    Circuit.t =
  ignore (c01 : Fp2.Circuit.t) ;
  ignore (c11 : Fp2.Circuit.t) ;
  failwith "mul_by_line: use sparse_mul with nori convention instead"

(** Assert two Fp12 elements are equal. *)
let assert_equal (a : Circuit.t) (b : Circuit.t) : unit =
  Fp6.assert_equal a.c0 b.c0 ; Fp6.assert_equal a.c1 b.c1

(** Fp12 one as a circuit constant. *)
let one : Circuit.t =
  let module Step = Pickles.Impls.Step in
  let zero_fp2 = Fp2.of_constant Fp2.Constant.zero in
  let one_fp2 = Fp2.of_constant Fp2.Constant.one in
  { c0 = { Fp6.Circuit.c0 = one_fp2; c1 = zero_fp2; c2 = zero_fp2 }
  ; c1 = { Fp6.Circuit.c0 = zero_fp2; c1 = zero_fp2; c2 = zero_fp2 }
  }

(** Assert an Fp12 element equals one. *)
let assert_one (a : Circuit.t) : unit = assert_equal a one

(** Cyclotomic squaring (for elements in the cyclotomic subgroup).
    More efficient than general squaring. *)
let cyclotomic_square (a : Circuit.t) : Circuit.t =
  (* For now, use general squaring. The optimized version can be added later. *)
  square a

(** Frobenius endomorphism: f^p.
    Conjugates all Fp2 components, then multiplies by gamma_1s constants.
    t1 = conj(c0.c0), t2 = conj(c1.c0)*γ1[0], t3 = conj(c0.c1)*γ1[1],
    t4 = conj(c1.c1)*γ1[2], t5 = conj(c0.c2)*γ1[3], t6 = conj(c1.c2)*γ1[4]
    result.c0 = (t1, t3, t5), result.c1 = (t2, t4, t6) *)
let frobenius_pow_p (a : Circuit.t) : Circuit.t =
  let g = Bn254_params.gamma_1s in
  let t1 = Fp2.conjugate a.c0.c0 in
  let t2 = Fp2.mul (Fp2.conjugate a.c1.c0) (Fp2.of_constant g.(0)) in
  let t3 = Fp2.mul (Fp2.conjugate a.c0.c1) (Fp2.of_constant g.(1)) in
  let t4 = Fp2.mul (Fp2.conjugate a.c1.c1) (Fp2.of_constant g.(2)) in
  let t5 = Fp2.mul (Fp2.conjugate a.c0.c2) (Fp2.of_constant g.(3)) in
  let t6 = Fp2.mul (Fp2.conjugate a.c1.c2) (Fp2.of_constant g.(4)) in
  { c0 = { Fp6.Circuit.c0 = t1; c1 = t3; c2 = t5 }
  ; c1 = { Fp6.Circuit.c0 = t2; c1 = t4; c2 = t6 }
  }

(** Frobenius endomorphism squared: f^(p^2).
    No conjugation; multiply by gamma_2s constants (all in Fp). *)
let frobenius_pow_p_squared (a : Circuit.t) : Circuit.t =
  let g = Bn254_params.gamma_2s in
  let t1 = a.c0.c0 in
  let t2 = Fp2.mul a.c1.c0 (Fp2.of_constant g.(0)) in
  let t3 = Fp2.mul a.c0.c1 (Fp2.of_constant g.(1)) in
  let t4 = Fp2.mul a.c1.c1 (Fp2.of_constant g.(2)) in
  let t5 = Fp2.mul a.c0.c2 (Fp2.of_constant g.(3)) in
  let t6 = Fp2.mul a.c1.c2 (Fp2.of_constant g.(4)) in
  { c0 = { Fp6.Circuit.c0 = t1; c1 = t3; c2 = t5 }
  ; c1 = { Fp6.Circuit.c0 = t2; c1 = t4; c2 = t6 }
  }

(** Frobenius endomorphism cubed: f^(p^3).
    Conjugate all Fp2 components, then multiply by gamma_3s constants. *)
let frobenius_pow_p_cubed (a : Circuit.t) : Circuit.t =
  let g = Bn254_params.gamma_3s in
  let t1 = Fp2.conjugate a.c0.c0 in
  let t2 = Fp2.mul (Fp2.conjugate a.c1.c0) (Fp2.of_constant g.(0)) in
  let t3 = Fp2.mul (Fp2.conjugate a.c0.c1) (Fp2.of_constant g.(1)) in
  let t4 = Fp2.mul (Fp2.conjugate a.c1.c1) (Fp2.of_constant g.(2)) in
  let t5 = Fp2.mul (Fp2.conjugate a.c0.c2) (Fp2.of_constant g.(3)) in
  let t6 = Fp2.mul (Fp2.conjugate a.c1.c2) (Fp2.of_constant g.(4)) in
  { c0 = { Fp6.Circuit.c0 = t1; c1 = t3; c2 = t5 }
  ; c1 = { Fp6.Circuit.c0 = t2; c1 = t4; c2 = t6 }
  }

(** Cyclotomic exponentiation by a small exponent. *)
let cyclotomic_pow (base : Circuit.t) ~(exp : int array) : Circuit.t =
  let n = Array.length exp in
  let result = ref base in
  for i = 1 to n - 1 do
    result := cyclotomic_square !result ;
    if exp.(i) = 1 then result := mul !result base
    else if exp.(i) = -1 then result := mul !result (unitary_inverse base)
  done ;
  !result
