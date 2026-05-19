(** Fp12 = Fp6[w] / (w^2 - v) arithmetic over BN254.

    Elements are pairs (c0, c1) representing c0 + c1*w where w^2 = v.
    This is the target field of the BN254 pairing. *)

open! Core_kernel

module Constant = struct
  type t = Fp6.Constant.t * Fp6.Constant.t

  let one : t = (Fp6.Constant.one, Fp6.Constant.zero)
end

module Circuit = struct
  type t = { c0 : Fp6.Circuit.t; c1 : Fp6.Circuit.t }

  let typ : (t, Constant.t) Pickles.Impls.Step.Typ.t =
    Pickles.Impls.Step.Typ.transport_var
      (Pickles.Impls.Step.Typ.tuple2 Fp6.Circuit.typ Fp6.Circuit.typ)
      ~there:(fun { c0; c1 } -> (c0, c1))
      ~back:(fun (c0, c1) -> { c0; c1 })
end

let of_constant ((c0, c1) : Constant.t) : Circuit.t =
  { c0 = Fp6.of_constant c0; c1 = Fp6.of_constant c1 }

let add (a : Circuit.t) (b : Circuit.t) : Circuit.t =
  let c0 = Fp6.add a.c0 b.c0 in
  let c1 = Fp6.add a.c1 b.c1 in
  { c0; c1 }

let sub (a : Circuit.t) (b : Circuit.t) : Circuit.t =
  let c0 = Fp6.sub a.c0 b.c0 in
  let c1 = Fp6.sub a.c1 b.c1 in
  { c0; c1 }

let neg (a : Circuit.t) : Circuit.t =
  let c0 = Fp6.neg a.c0 in
  let c1 = Fp6.neg a.c1 in
  { c0; c1 }

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
  let c0 = Fp6.add v1_shifted v0 in
  let a01 = Fp6.add a.c0 a.c1 in
  let b01 = Fp6.add b.c0 b.c1 in
  let t = Fp6.mul a01 b01 in
  let c1 = Fp6.sub (Fp6.sub t v0) v1 in
  { c0; c1 }

(** Chung-Hasan SQ2: uses 2 Fp6.mul instead of 3. *)
let square (a : Circuit.t) : Circuit.t =
  let c0 = Fp6.sub a.c0 a.c1 in
  let c3 = Fp6.sub a.c0 (Fp6.mul_by_v a.c1) in
  let c2 = Fp6.mul a.c0 a.c1 in
  let c0_c3 = Fp6.mul c0 c3 in
  let c0 = Fp6.add c0_c3 c2 in
  let two =
    Snarky_foreign_field.Foreign_field.FpA.of_constant (Bignum_bigint.of_int 2)
  in
  let c1 = Fp6.mul_by_fp c2 two in
  let c2 = Fp6.mul_by_v c2 in
  let c0 = Fp6.add c0 c2 in
  { c0; c1 }

(** Conjugate: (a0 + a1*w)* = a0 - a1*w *)
let conjugate (a : Circuit.t) : Circuit.t = { c0 = a.c0; c1 = Fp6.neg a.c1 }

(** Unitary inverse (for elements on the cyclotomic subgroup):
    inv(a) = conjugate(a) since |a| = 1. *)
let unitary_inverse (a : Circuit.t) : Circuit.t = conjugate a

(** Full Fp12 inverse.
    Matches nori Fp12.inverse() (fp12.ts:47-58). *)
let inverse (a : Circuit.t) : Circuit.t =
  let t0 = Fp6.mul a.c0 a.c0 in
  let t1 = Fp6.mul a.c1 a.c1 in
  let t0 = Fp6.sub t0 (Fp6.mul_by_v t1) in
  let t1 = Fp6.inverse t0 in
  let c0 = Fp6.mul a.c0 t1 in
  let c1 = Fp6.mul (Fp6.neg a.c1) t1 in
  { c0; c1 }

(** Sparse multiplication.
    The RHS has structure: c0 = (rhs.c0.c0, 0, 0), c1 = (rhs.c1.c0, rhs.c1.c1, 0). *)
let sparse_mul (a : Circuit.t) (rhs : Circuit.t) : Circuit.t =
  let t0 = Fp6.mul_by_fp2 a.c0 rhs.c0.c0 in
  let t1 = Fp6.mul_by_sparse_fp6 a.c1 rhs.c1 in
  let c0 = Fp6.add t0 (Fp6.mul_by_v t1) in
  let t2 : Fp6.Circuit.t =
    { c0 = Fp2.add rhs.c0.c0 rhs.c1.c0
    ; c1 = rhs.c1.c1
    ; c2 = Fp2.of_constant Fp2.Constant.zero
    }
  in
  let c1 = Fp6.mul_by_sparse_fp6 (Fp6.add a.c0 a.c1) t2 in
  let c1 = Fp6.sub c1 t0 in
  let c1 = Fp6.sub c1 t1 in
  { c0; c1 }

let assert_equal (a : Circuit.t) (b : Circuit.t) : unit =
  Fp6.assert_equal a.c0 b.c0 ; Fp6.assert_equal a.c1 b.c1

let one : Circuit.t =
  let module Step = Pickles.Impls.Step in
  let zero_fp2 = Fp2.of_constant Fp2.Constant.zero in
  let one_fp2 = Fp2.of_constant Fp2.Constant.one in
  { c0 = { Fp6.Circuit.c0 = one_fp2; c1 = zero_fp2; c2 = zero_fp2 }
  ; c1 = { Fp6.Circuit.c0 = zero_fp2; c1 = zero_fp2; c2 = zero_fp2 }
  }

let assert_one (a : Circuit.t) : unit = assert_equal a one

(** Typ.t for Fp12 (with range checks on each FpA component).
    Matches nori Fp12 provable type. *)
let typ : (Circuit.t, Constant.t) Pickles.Impls.Step.Typ.t =
  let module Step = Pickles.Impls.Step in
  let fp6_typ = Fp6.Circuit.typ in
  Step.Typ.transport
    (Step.Typ.tuple2 fp6_typ fp6_typ)
    ~there:(fun (c0, c1) -> (c0, c1))
    ~back:(fun (c0, c1) -> (c0, c1))
  |> Step.Typ.transport_var
       ~there:(fun { Circuit.c0; c1 } -> (c0, c1))
       ~back:(fun (c0, c1) -> { Circuit.c0; c1 })

(** Witness an Fp12 value using the proper Typ.t. *)
let witness () : Circuit.t =
  let module Step = Pickles.Impls.Step in
  Step.exists typ ~compute:(fun () -> Constant.one)

(** Cyclotomic squaring — currently uses general squaring. *)
let cyclotomic_square = square

(** Frobenius endomorphism: f^p.
    Conjugates all Fp2 components, then multiplies by gamma_1s constants.
    t1 = conj(c0.c0), t2 = conj(c1.c0)*γ1[0], t3 = conj(c0.c1)*γ1[1],
    t4 = conj(c1.c1)*γ1[2], t5 = conj(c0.c2)*γ1[3], t6 = conj(c1.c2)*γ1[4]
    result.c0 = (t1, t3, t5), result.c1 = (t2, t4, t6) *)
let frobenius_pow_p (a : Circuit.t) : Circuit.t =
  let g = Bn254_params.gamma_1s in
  (* Conjugate ALL components first, then multiply — matching nori's order *)
  let t1 = Fp2.conjugate a.c0.c0 in
  let t2 = Fp2.conjugate a.c1.c0 in
  let t3 = Fp2.conjugate a.c0.c1 in
  let t4 = Fp2.conjugate a.c1.c1 in
  let t5 = Fp2.conjugate a.c0.c2 in
  let t6 = Fp2.conjugate a.c1.c2 in
  let t2 = Fp2.mul t2 (Fp2.of_constant g.(0)) in
  let t3 = Fp2.mul t3 (Fp2.of_constant g.(1)) in
  let t4 = Fp2.mul t4 (Fp2.of_constant g.(2)) in
  let t5 = Fp2.mul t5 (Fp2.of_constant g.(3)) in
  let t6 = Fp2.mul t6 (Fp2.of_constant g.(4)) in
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
  (* Conjugate ALL components first, then multiply — matching nori's order *)
  let t1 = Fp2.conjugate a.c0.c0 in
  let t2 = Fp2.conjugate a.c1.c0 in
  let t3 = Fp2.conjugate a.c0.c1 in
  let t4 = Fp2.conjugate a.c1.c1 in
  let t5 = Fp2.conjugate a.c0.c2 in
  let t6 = Fp2.conjugate a.c1.c2 in
  let t2 = Fp2.mul t2 (Fp2.of_constant g.(0)) in
  let t3 = Fp2.mul t3 (Fp2.of_constant g.(1)) in
  let t4 = Fp2.mul t4 (Fp2.of_constant g.(2)) in
  let t5 = Fp2.mul t5 (Fp2.of_constant g.(3)) in
  let t6 = Fp2.mul t6 (Fp2.of_constant g.(4)) in
  { c0 = { Fp6.Circuit.c0 = t1; c1 = t3; c2 = t5 }
  ; c1 = { Fp6.Circuit.c0 = t2; c1 = t4; c2 = t6 }
  }

(** Cyclotomic exponentiation by a small exponent in NAF form. *)
let cyclotomic_pow (base : Circuit.t) ~(exp : int array) : Circuit.t =
  let n = Array.length exp in
  let result = ref base in
  for i = 1 to n - 1 do
    result := cyclotomic_square !result ;
    if exp.(i) = 1 then result := mul !result base
    else if exp.(i) = -1 then result := mul !result (unitary_inverse base)
  done ;
  !result
