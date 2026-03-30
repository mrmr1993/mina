(** Line coefficients for BN254 pairing computation.

    During the Miller loop, we evaluate lines tangent to / through
    points on G2. Each line has coefficients (lambda, neg_mu) in Fp2,
    which are used for sparse Fp12 multiplication. *)

(** Line coefficient pair. *)
module G2Line = struct
  type t = { lambda : Fp2.Circuit.t; neg_mu : Fp2.Circuit.t }
end

(** Affine cache: precomputed x/y values for a G1 point,
    used during line evaluation. *)
module AffineCache = struct
  type t = { x_over_y : Snarky_foreign_field.Foreign_field.Field3.t
           ; y_inv : Snarky_foreign_field.Foreign_field.Field3.t
           }
end

(** Evaluate a line at a G1 point using the affine cache.
    The line evaluation produces an Fp12 element with sparse structure
    that can be multiplied efficiently. *)
let eval_line (line : G2Line.t) (cache : AffineCache.t) :
    Fp2.Circuit.t * Fp2.Circuit.t =
  let c01 = Fp2.mul_by_fp line.lambda cache.x_over_y in
  let c11 = Fp2.mul_by_fp line.neg_mu cache.y_inv in
  (c01, c11)

(** Sparse Fp12 multiplication by a line evaluation result.
    Delegates to Fp12.mul_by_line. *)
let mul_by_line (f : Fp12.Circuit.t) (line : G2Line.t)
    (cache : AffineCache.t) : Fp12.Circuit.t =
  let c01, c11 = eval_line line cache in
  Fp12.mul_by_line f ~c01 ~c11
