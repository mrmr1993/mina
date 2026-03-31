(** Line coefficients for BN254 pairing computation. *)

open! Core_kernel
module FF = Snarky_foreign_field.Foreign_field

module G2Line = struct
  type t = { lambda : Fp2.Circuit.t; neg_mu : Fp2.Circuit.t }
end

module AffineCache = struct
  type t = { x_over_y : FF.Field3.t; y_inv : FF.Field3.t }
end

let eval_line (line : G2Line.t) (cache : AffineCache.t) :
    Fp2.Circuit.t * Fp2.Circuit.t =
  let c01 = Fp2.mul_by_fp line.lambda cache.x_over_y in
  let c11 = Fp2.mul_by_fp line.neg_mu cache.y_inv in
  (c01, c11)

(** Evaluate a line into a full (sparse) Fp12 element.
    The result has the form (1, c01, 0; c11, 0, 0) in Fp12. *)
let eval_to_fp12 (line : G2Line.t) (cache : AffineCache.t) : Fp12.Circuit.t =
  let c01, c11 = eval_line line cache in
  let one_fp2 = Fp2.of_constant Fp2.Constant.one in
  let zero_fp2 = Fp2.of_constant Fp2.Constant.zero in
  { Fp12.Circuit.c0 = { Fp6.Circuit.c0 = one_fp2; c1 = c01; c2 = zero_fp2 }
  ; c1 = { Fp6.Circuit.c0 = c11; c1 = zero_fp2; c2 = zero_fp2 }
  }

let mul_by_line (f : Fp12.Circuit.t) (line : G2Line.t) (cache : AffineCache.t) :
    Fp12.Circuit.t =
  let c01, c11 = eval_line line cache in
  Fp12.mul_by_line f ~c01 ~c11
