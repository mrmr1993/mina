(** Fp12 = Fp6[w] / (w^2 - v) arithmetic over BN254.

    Elements are pairs (c0, c1) representing c0 + c1*w where w^2 = v.
    This is the target field of the BN254 pairing. *)

(** Fp12 element as a pair of Fp6 values. *)
module Circuit = struct
  type t = { c0 : Fp6.Circuit.t; c1 : Fp6.Circuit.t }
end

(** Addition. *)
let add (a : Circuit.t) (b : Circuit.t) : Circuit.t =
  { c0 = Fp6.add a.c0 b.c0; c1 = Fp6.add a.c1 b.c1 }

(** Subtraction. *)
let sub (a : Circuit.t) (b : Circuit.t) : Circuit.t =
  { c0 = Fp6.sub a.c0 b.c0; c1 = Fp6.sub a.c1 b.c1 }

(** Negation. *)
let neg (a : Circuit.t) : Circuit.t =
  { c0 = Fp6.neg a.c0; c1 = Fp6.neg a.c1 }

(** Multiplication using Karatsuba:
    (a0 + a1*w)(b0 + b1*w) = (a0*b0 + a1*b1*v) + (a0*b1 + a1*b0)*w
    where a1*b1*v is computed via mul_by_non_residue on the Fp6 level
    (shifting c2*v^2 -> c0*xi, etc.) *)
let mul (a : Circuit.t) (b : Circuit.t) : Circuit.t =
  let v0 = Fp6.mul a.c0 b.c0 in
  let v1 = Fp6.mul a.c1 b.c1 in
  (* c0 = v0 + v1 * v, where v1*v shifts Fp6 coefficients *)
  let v1_shifted : Fp6.Circuit.t =
    { c0 = Fp6.mul_by_non_residue v1.c2
    ; c1 = v1.c0
    ; c2 = v1.c1
    }
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
let conjugate (a : Circuit.t) : Circuit.t =
  { c0 = a.c0; c1 = Fp6.neg a.c1 }

(** Unitary inverse (for elements on the cyclotomic subgroup):
    inv(a) = conjugate(a) since |a| = 1. *)
let unitary_inverse (a : Circuit.t) : Circuit.t = conjugate a

(** Sparse multiplication by a line evaluation result.
    The line result has the form (1, 0, 0, c01, c11, 0) in Fp12 coordinates,
    which means c0 = (1, c01, 0) and c1 = (c11, 0, 0) in Fp6.
    This allows a more efficient multiplication. *)
let mul_by_line (a : Circuit.t) ~(c01 : Fp2.Circuit.t)
    ~(c11 : Fp2.Circuit.t) : Circuit.t =
  let one_fp2 = Fp2.of_constant Fp2.Constant.one in
  let b0 = Fp6.mul_by_01 a.c0 one_fp2 c01 in
  let b1 = Fp6.mul_by_01 a.c1 c11 (Fp2.of_constant Fp2.Constant.zero) in
  (* This is a simplified version; the full sparse mul is more optimized
     in the actual circuit implementation. *)
  let c0_shifted : Fp6.Circuit.t =
    { c0 = Fp6.mul_by_non_residue b1.c2
    ; c1 = b1.c0
    ; c2 = b1.c1
    }
  in
  let c0 = Fp6.add b0 c0_shifted in
  let a01 = Fp6.add a.c0 a.c1 in
  let line_sum_c0 = Fp2.add one_fp2 c11 in
  let line_sum = Fp6.mul_by_01 a01 line_sum_c0 c01 in
  let c1 = Fp6.sub (Fp6.sub line_sum b0) b1 in
  { c0; c1 }

(** Cyclotomic squaring (for elements in the cyclotomic subgroup).
    More efficient than general squaring. *)
let cyclotomic_square (a : Circuit.t) : Circuit.t =
  (* For now, use general squaring. The optimized version can be added later. *)
  square a

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
