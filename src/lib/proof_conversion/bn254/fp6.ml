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
    Pickles.Impls.Step.Typ.transport
      (Pickles.Impls.Step.Typ.tuple3 Fp2.Circuit.typ Fp2.Circuit.typ
         Fp2.Circuit.typ )
      ~there:(fun (c0, c1, c2) -> (c0, c1, c2))
      ~back:(fun (c0, c1, c2) -> (c0, c1, c2))
    |> Pickles.Impls.Step.Typ.transport_var
         ~there:(fun { c0; c1; c2 } -> (c0, c1, c2))
         ~back:(fun (c0, c1, c2) -> { c0; c1; c2 })
end

let mul_by_non_residue (x : Fp2.Circuit.t) : Fp2.Circuit.t =
  let xi = Fp2.of_constant Bn254_params.fp2_non_residue in
  Fp2.mul x xi

let add (a : Circuit.t) (b : Circuit.t) : Circuit.t =
  { c0 = Fp2.add a.c0 b.c0; c1 = Fp2.add a.c1 b.c1; c2 = Fp2.add a.c2 b.c2 }

let sub (a : Circuit.t) (b : Circuit.t) : Circuit.t =
  { c0 = Fp2.sub a.c0 b.c0; c1 = Fp2.sub a.c1 b.c1; c2 = Fp2.sub a.c2 b.c2 }

let neg (a : Circuit.t) : Circuit.t =
  { c0 = Fp2.neg a.c0; c1 = Fp2.neg a.c1; c2 = Fp2.neg a.c2 }

let mul (a : Circuit.t) (b : Circuit.t) : Circuit.t =
  let a0b0 = Fp2.mul a.c0 b.c0 in
  let a0b1 = Fp2.mul a.c0 b.c1 in
  let a0b2 = Fp2.mul a.c0 b.c2 in
  let a1b0 = Fp2.mul a.c1 b.c0 in
  let a1b1 = Fp2.mul a.c1 b.c1 in
  let a1b2 = Fp2.mul a.c1 b.c2 in
  let a2b0 = Fp2.mul a.c2 b.c0 in
  let a2b1 = Fp2.mul a.c2 b.c1 in
  let a2b2 = Fp2.mul a.c2 b.c2 in
  let c0 = Fp2.add a0b0 (mul_by_non_residue (Fp2.add a1b2 a2b1)) in
  let c1 = Fp2.add (Fp2.add a0b1 a1b0) (mul_by_non_residue a2b2) in
  let c2 = Fp2.add (Fp2.add a0b2 a1b1) a2b0 in
  { c0; c1; c2 }

let assert_equal (a : Circuit.t) (b : Circuit.t) : unit =
  Fp2.assert_equal a.c0 b.c0 ;
  Fp2.assert_equal a.c1 b.c1 ;
  Fp2.assert_equal a.c2 b.c2

(** Multiply Fp6 by a native Fp scalar (multiply each Field3 limb). *)
let mul_by_fp (a : Circuit.t) (b : Snarky_foreign_field.Foreign_field.FpA.t) :
    Circuit.t =
  { c0 = Fp2.mul_by_fp a.c0 b
  ; c1 = Fp2.mul_by_fp a.c1 b
  ; c2 = Fp2.mul_by_fp a.c2 b
  }

(** Multiply Fp6 by a single Fp2 element (scalar multiply each component). *)
let mul_by_fp2 (a : Circuit.t) (b : Fp2.Circuit.t) : Circuit.t =
  { c0 = Fp2.mul a.c0 b; c1 = Fp2.mul a.c1 b; c2 = Fp2.mul a.c2 b }

(** Multiply Fp6 by a sparse Fp6 element (b0, b1, 0).
    Matches nori's Fp6.mul_by_sparse_fp6(rhs) where rhs.c2 = 0. *)
let mul_by_sparse (a : Circuit.t) (b0 : Fp2.Circuit.t) (b1 : Fp2.Circuit.t) :
    Circuit.t =
  let t0 = Fp2.mul a.c0 b0 in
  let t1 = Fp2.mul a.c1 b1 in
  let c0 = Fp2.add t0 (mul_by_non_residue (Fp2.mul a.c2 b1)) in
  let c1 =
    Fp2.sub (Fp2.mul (Fp2.add a.c0 a.c1) (Fp2.add b0 b1)) (Fp2.add t0 t1)
  in
  let c2 = Fp2.add (Fp2.mul a.c2 b0) t1 in
  { c0; c1; c2 }

let mul_by_01 (a : Circuit.t) (b0 : Fp2.Circuit.t) (b1 : Fp2.Circuit.t) :
    Circuit.t =
  let a0b0 = Fp2.mul a.c0 b0 in
  let a1b1 = Fp2.mul a.c1 b1 in
  let c0 = Fp2.add a0b0 (mul_by_non_residue (Fp2.mul a.c2 b1)) in
  let c1 =
    Fp2.sub (Fp2.mul (Fp2.add a.c0 a.c1) (Fp2.add b0 b1)) (Fp2.add a0b0 a1b1)
  in
  let c2 = Fp2.add (Fp2.mul a.c2 b0) a1b1 in
  { c0; c1; c2 }
