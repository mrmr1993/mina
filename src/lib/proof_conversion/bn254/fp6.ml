(** Fp6 = Fp2[v] / (v^3 - xi) arithmetic over BN254.

    Elements are triples (c0, c1, c2) representing c0 + c1*v + c2*v^2
    where v^3 = xi and xi = 9 + u (the Fp2 non-residue). *)

let p = Bn254_params.p

(** Fp6 element as a triple of Fp2 values. *)
module Circuit = struct
  type t = { c0 : Fp2.Circuit.t; c1 : Fp2.Circuit.t; c2 : Fp2.Circuit.t }
end

(** Multiply an Fp2 value by the non-residue xi = 9 + u.
    Used when reducing v^3 = xi in Fp6 arithmetic. *)
let mul_by_non_residue (x : Fp2.Circuit.t) : Fp2.Circuit.t =
  let open Snarky_foreign_field.Foreign_field in
  let xi = Fp2.of_constant Bn254_params.fp2_non_residue in
  Fp2.mul x xi

(** Addition. *)
let add (a : Circuit.t) (b : Circuit.t) : Circuit.t =
  { c0 = Fp2.add a.c0 b.c0
  ; c1 = Fp2.add a.c1 b.c1
  ; c2 = Fp2.add a.c2 b.c2
  }

(** Subtraction. *)
let sub (a : Circuit.t) (b : Circuit.t) : Circuit.t =
  { c0 = Fp2.sub a.c0 b.c0
  ; c1 = Fp2.sub a.c1 b.c1
  ; c2 = Fp2.sub a.c2 b.c2
  }

(** Negation. *)
let neg (a : Circuit.t) : Circuit.t =
  { c0 = Fp2.neg a.c0; c1 = Fp2.neg a.c1; c2 = Fp2.neg a.c2 }

(** Multiplication using schoolbook with non-residue reduction.
    (a0 + a1*v + a2*v^2)(b0 + b1*v + b2*v^2)
    = (a0*b0 + xi*(a1*b2 + a2*b1))
    + (a0*b1 + a1*b0 + xi*a2*b2)*v
    + (a0*b2 + a1*b1 + a2*b0)*v^2 *)
let mul (a : Circuit.t) (b : Circuit.t) : Circuit.t =
  let open Snarky_foreign_field.Foreign_field in
  let a0b0 = Fp2.mul a.c0 b.c0 in
  let a0b1 = Fp2.mul a.c0 b.c1 in
  let a0b2 = Fp2.mul a.c0 b.c2 in
  let a1b0 = Fp2.mul a.c1 b.c0 in
  let a1b1 = Fp2.mul a.c1 b.c1 in
  let a1b2 = Fp2.mul a.c1 b.c2 in
  let a2b0 = Fp2.mul a.c2 b.c0 in
  let a2b1 = Fp2.mul a.c2 b.c1 in
  let a2b2 = Fp2.mul a.c2 b.c2 in
  ignore p ;
  let c0 = Fp2.add a0b0 (mul_by_non_residue (Fp2.add a1b2 a2b1)) in
  let c1 = Fp2.add (Fp2.add a0b1 a1b0) (mul_by_non_residue a2b2) in
  let c2 = Fp2.add (Fp2.add a0b2 a1b1) a2b0 in
  { c0; c1; c2 }

(** Multiply Fp6 element by an Fp2 scalar applied to the c1 coefficient.
    mul_by_01(a, b0, b1) = a * (b0 + b1*v)
    This is a sparse multiplication used in pairing line evaluation. *)
let mul_by_01 (a : Circuit.t) (b0 : Fp2.Circuit.t) (b1 : Fp2.Circuit.t) :
    Circuit.t =
  let a0b0 = Fp2.mul a.c0 b0 in
  let a1b1 = Fp2.mul a.c1 b1 in
  let c0 = Fp2.add a0b0 (mul_by_non_residue (Fp2.mul a.c2 b1)) in
  let c1 =
    Fp2.sub
      (Fp2.mul (Fp2.add a.c0 a.c1) (Fp2.add b0 b1))
      (Fp2.add a0b0 a1b1)
  in
  let c2 = Fp2.add (Fp2.mul a.c2 b0) a1b1 in
  { c0; c1; c2 }
