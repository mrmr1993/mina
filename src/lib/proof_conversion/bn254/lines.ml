(** Line coefficients for BN254 pairing computation. *)

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

let mul_by_line (f : Fp12.Circuit.t) (line : G2Line.t)
    (cache : AffineCache.t) : Fp12.Circuit.t =
  let c01, c11 = eval_line line cache in
  Fp12.mul_by_line f ~c01 ~c11
