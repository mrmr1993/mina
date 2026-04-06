(** Fp6 = Fp2[v] / (v^3 - xi) arithmetic over BN254.

    Elements are triples (c0, c1, c2) representing c0 + c1*v + c2*v^2
    where v^3 = xi and xi = 9 + u (the Fp2 non-residue). *)

open! Core_kernel

module Constant = struct
  type t = Fp2.Constant.t * Fp2.Constant.t * Fp2.Constant.t
end

module Circuit = struct
  type t = { c0 : Fp2.Circuit.t; c1 : Fp2.Circuit.t; c2 : Fp2.Circuit.t }

  let typ : (t, Constant.t) Pickles.Impls.Step.Typ.t =
    Pickles.Impls.Step.Typ.transport_var
      (Pickles.Impls.Step.Typ.tuple3 Fp2.Circuit.typ Fp2.Circuit.typ
         Fp2.Circuit.typ )
      ~there:(fun { c0; c1; c2 } -> (c0, c1, c2))
      ~back:(fun (c0, c1, c2) -> { c0; c1; c2 })
end

let of_constant ((c0, c1, c2) : Constant.t) : Circuit.t =
  { c0 = Fp2.of_constant c0; c1 = Fp2.of_constant c1; c2 = Fp2.of_constant c2 }

let mul_by_non_residue (x : Fp2.Circuit.t) : Fp2.Circuit.t =
  let xi = Fp2.of_constant Bn254_params.fp2_non_residue in
  Fp2.mul x xi

(** Multiply by v in Fp2[v]/(v^3 - xi):
      { c0: c2 * xi, c1: c0, c2: c1 } *)
let mul_by_v (a : Circuit.t) : Circuit.t =
  let c0 = Fp2.mul a.c2 (Fp2.of_constant Bn254_params.fp2_non_residue) in
  { c0; c1 = a.c0; c2 = a.c1 }

let add (a : Circuit.t) (b : Circuit.t) : Circuit.t =
  let c0 = Fp2.add a.c0 b.c0 in
  let c1 = Fp2.add a.c1 b.c1 in
  let c2 = Fp2.add a.c2 b.c2 in
  { c0; c1; c2 }

let sub (a : Circuit.t) (b : Circuit.t) : Circuit.t =
  let c0 = Fp2.sub a.c0 b.c0 in
  let c1 = Fp2.sub a.c1 b.c1 in
  let c2 = Fp2.sub a.c2 b.c2 in
  { c0; c1; c2 }

let neg (a : Circuit.t) : Circuit.t =
  let c0 = Fp2.neg a.c0 in
  let c1 = Fp2.neg a.c1 in
  let c2 = Fp2.neg a.c2 in
  { c0; c1; c2 }

(** Fp6 multiplication using Karatsuba (6 Fp2.mul instead of 9). *)
let mul (a : Circuit.t) (b : Circuit.t) : Circuit.t =
  let t0 = Fp2.mul a.c0 b.c0 in
  let t1 = Fp2.mul a.c1 b.c1 in
  let t2 = Fp2.mul a.c2 b.c2 in
  let a1_a2 = Fp2.add a.c1 a.c2 in
  let a0_a1 = Fp2.add a.c0 a.c1 in
  let a0_a2 = Fp2.add a.c0 a.c2 in
  let b1_b2 = Fp2.add b.c1 b.c2 in
  let b0_b1 = Fp2.add b.c0 b.c1 in
  let b0_b2 = Fp2.add b.c0 b.c2 in
  let open Snarky_foreign_field.Foreign_field in
  (* c0 = ((a1+a2)(b1+b2) - t1 - t2) * xi + t0 *)
  let c0_mul = Fp2.mul a1_a2 b1_b2 in
  let c0_inner = Fp2.sum [ c0_mul; t1; t2 ] [ Sub; Sub ] in
  let c0 = Fp2.add (mul_by_non_residue c0_inner) t0 in
  (* c1 = (a0+a1)(b0+b1) - t0 - t1 + t2*xi *)
  let c1_mul = Fp2.mul a0_a1 b0_b1 in
  let c1_xi = mul_by_non_residue t2 in
  let c1 = Fp2.sum [ c1_mul; t0; t1; c1_xi ] [ Sub; Sub; Add ] in
  (* c2 = (a0+a2)(b0+b2) - t0 - t2 + t1 *)
  let c2_mul = Fp2.mul a0_a2 b0_b2 in
  let c2 = Fp2.sum [ c2_mul; t0; t2; t1 ] [ Sub; Sub; Add ] in
  { c0; c1; c2 }

(** Fp6 inverse.
    Matches nori Fp6.inverse() (fp6.ts:36-59). *)
let inverse (a : Circuit.t) : Circuit.t =
  let t0 = Fp2.mul a.c0 a.c0 in
  let t1 = Fp2.mul a.c1 a.c1 in
  let t2 = Fp2.mul a.c2 a.c2 in
  let t3 = Fp2.mul a.c0 a.c1 in
  let t4 = Fp2.mul a.c0 a.c2 in
  let t5 = Fp2.mul a.c1 a.c2 in
  let c0 = Fp2.sub t0 (mul_by_non_residue t5) in
  let c1 = Fp2.sub (mul_by_non_residue t2) t3 in
  let c2 = Fp2.sub t1 t4 in
  let t6 = Fp2.mul a.c0 c0 in
  let t6 = Fp2.add t6 (mul_by_non_residue (Fp2.mul a.c2 c1)) in
  let t6 = Fp2.add t6 (mul_by_non_residue (Fp2.mul a.c1 c2)) in
  let t6 = Fp2.inverse t6 in
  let c0 = Fp2.mul c0 t6 in
  let c1 = Fp2.mul c1 t6 in
  let c2 = Fp2.mul c2 t6 in
  { c0; c1; c2 }

let assert_equal (a : Circuit.t) (b : Circuit.t) : unit =
  Fp2.assert_equal a.c0 b.c0 ;
  Fp2.assert_equal a.c1 b.c1 ;
  Fp2.assert_equal a.c2 b.c2

(** Multiply Fp6 by a native Fp scalar (multiply each Field3 limb). *)
let mul_by_fp (a : Circuit.t) (b : Snarky_foreign_field.Foreign_field.FpA.t) :
    Circuit.t =
  let c0 = Fp2.mul_by_fp a.c0 b in
  let c1 = Fp2.mul_by_fp a.c1 b in
  let c2 = Fp2.mul_by_fp a.c2 b in
  { c0; c1; c2 }

(** Multiply Fp6 by a single Fp2 element (scalar multiply each component). *)
let mul_by_fp2 (a : Circuit.t) (b : Fp2.Circuit.t) : Circuit.t =
  let c0 = Fp2.mul a.c0 b in
  let c1 = Fp2.mul a.c1 b in
  let c2 = Fp2.mul a.c2 b in
  { c0; c1; c2 }

(** Multiply Fp6 by a sparse Fp6 element (rhs.c0, rhs.c1, 0). *)
let mul_by_sparse_fp6 (a : Circuit.t) (rhs : Circuit.t) : Circuit.t =
  let t0 = Fp2.mul a.c0 rhs.c0 in
  let t1 = Fp2.mul a.c1 rhs.c1 in
  let a2_b1 = Fp2.mul a.c2 rhs.c1 in
  let c0 = Fp2.mul a2_b1 (Fp2.of_constant Bn254_params.fp2_non_residue) in
  let c0 = Fp2.add c0 t0 in
  let a0_a1 = Fp2.add a.c0 a.c1 in
  let b0_b1 = Fp2.add rhs.c0 rhs.c1 in
  let c1 = Fp2.mul a0_a1 b0_b1 in
  let c1 = Fp2.sub c1 t0 in
  let c1 = Fp2.sub c1 t1 in
  let a2_b0 = Fp2.mul a.c2 rhs.c0 in
  let c2 = Fp2.add a2_b0 t1 in
  { c0; c1; c2 }

let mul_by_01 (a : Circuit.t) (b0 : Fp2.Circuit.t) (b1 : Fp2.Circuit.t) :
    Circuit.t =
  let a0b0 = Fp2.mul a.c0 b0 in
  let a1b1 = Fp2.mul a.c1 b1 in
  let a2b1 = Fp2.mul a.c2 b1 in
  let c0 = Fp2.add a0b0 (mul_by_non_residue a2b1) in
  let a0_a1 = Fp2.add a.c0 a.c1 in
  let b0_b1 = Fp2.add b0 b1 in
  let a0b0_a1b1 = Fp2.add a0b0 a1b1 in
  let c1 = Fp2.sub (Fp2.mul a0_a1 b0_b1) a0b0_a1b1 in
  let a2b0 = Fp2.mul a.c2 b0 in
  let c2 = Fp2.add a2b0 a1b1 in
  { c0; c1; c2 }
