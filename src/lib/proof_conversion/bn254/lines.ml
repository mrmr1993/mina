(** Line coefficients for BN254 pairing computation. *)

open! Core_kernel
module FF = Snarky_foreign_field.Foreign_field

module G2Line = struct
  type t = { lambda : Fp2.Circuit.t; neg_mu : Fp2.Circuit.t }

  type constant = Fp2.Constant.t * Fp2.Constant.t

  let typ : (t, constant) Pickles.Impls.Step.Typ.t =
    Pickles.Impls.Step.Typ.transport
      (Pickles.Impls.Step.Typ.tuple2 Fp2.Circuit.typ Fp2.Circuit.typ)
      ~there:(fun (l, m) -> (l, m))
      ~back:(fun (l, m) -> (l, m))
    |> Pickles.Impls.Step.Typ.transport_var
         ~there:(fun { lambda; neg_mu } -> (lambda, neg_mu))
         ~back:(fun (lambda, neg_mu) -> { lambda; neg_mu })
end

module AffineCache = struct
  type t = { x_over_y : FF.FpA.t; y_inv : FF.FpA.t }
end

(** Compute the addition line through two G2 points in-circuit.
    lambda = (p2.y - p1.y) / (p2.x - p1.x)
    neg_mu = lambda * p1.x - p1.y *)
let compute_add_line (p1 : G2.Circuit.t) (p2 : G2.Circuit.t) : G2Line.t =
  let dx = Fp2.sub p2.x p1.x in
  let dy = Fp2.sub p2.y p1.y in
  let lambda = Fp2.mul dy (Fp2.inverse dx) in
  let neg_mu = Fp2.sub (Fp2.mul lambda p1.x) p1.y in
  { lambda; neg_mu }

(** Compute the tangent line at a G2 point in-circuit.
    lambda = 3 * x^2 / (2 * y)   (for curve y^2 = x^3 + b with a=0)
    neg_mu = lambda * x - y *)
let compute_tangent_line (p : G2.Circuit.t) : G2Line.t =
  let x_sq = Fp2.square p.x in
  let three_x_sq = Fp2.add (Fp2.add x_sq x_sq) x_sq in
  let two_y = Fp2.add p.y p.y in
  let lambda = Fp2.mul three_x_sq (Fp2.inverse two_y) in
  let neg_mu = Fp2.sub (Fp2.mul lambda p.x) p.y in
  { lambda; neg_mu }

(** Assert that a line passes through a G2 point: y - (lambda*x + mu) = 0,
    equivalently: y + neg_mu - lambda*x = 0. *)
let assert_is_on_line (line : G2Line.t) (p : G2.Circuit.t) : unit =
  let lhs = Fp2.add p.y line.neg_mu in
  let rhs = Fp2.mul line.lambda p.x in
  Fp2.assert_equal lhs rhs

(** Assert that a line is tangent to the curve at point p:
    1. Line passes through p
    2. 2*lambda*y = 3*x^2 (tangent condition for y^2 = x^3 + b) *)
let assert_is_tangent (line : G2Line.t) (p : G2.Circuit.t) : unit =
  assert_is_on_line line p ;
  let two_lambda_y = Fp2.mul (Fp2.add line.lambda line.lambda) p.y in
  let x_sq = Fp2.square p.x in
  let three_x_sq = Fp2.add (Fp2.add x_sq x_sq) x_sq in
  Fp2.assert_equal two_lambda_y three_x_sq

(** Assert that a line passes through two G2 points. *)
let assert_is_line (line : G2Line.t) (p1 : G2.Circuit.t) (p2 : G2.Circuit.t) :
    unit =
  assert_is_on_line line p1 ; assert_is_on_line line p2

(** G2 point doubling from a known tangent line.
    x3 = lambda^2 - 2*x, y3 = lambda*(x - x3) - y *)
let double_from_line (p : G2.Circuit.t) ~(lambda : Fp2.Circuit.t) : G2.Circuit.t
    =
  let lambda_sq = Fp2.square lambda in
  let two_x = Fp2.add p.x p.x in
  let x3 = Fp2.sub lambda_sq two_x in
  let y3 = Fp2.sub (Fp2.mul lambda (Fp2.sub p.x x3)) p.y in
  { G2.Circuit.x = x3; y = y3 }

(** G2 point addition from a known line.
    x3 = lambda^2 - x1 - x2, y3 = lambda*(x1 - x3) - y1 *)
let add_from_line (p1 : G2.Circuit.t) ~(lambda : Fp2.Circuit.t)
    (p2 : G2.Circuit.t) : G2.Circuit.t =
  let lambda_sq = Fp2.square lambda in
  let x3 = Fp2.sub (Fp2.sub lambda_sq p1.x) p2.x in
  let y3 = Fp2.sub (Fp2.mul lambda (Fp2.sub p1.x x3)) p1.y in
  { G2.Circuit.x = x3; y = y3 }

let eval_line (line : G2Line.t) (cache : AffineCache.t) :
    Fp2.Circuit.t * Fp2.Circuit.t =
  let c01 = Fp2.mul_by_fp line.lambda cache.x_over_y in
  let c11 = Fp2.mul_by_fp line.neg_mu cache.y_inv in
  (c01, c11)

(** Evaluate a line into a sparse Fp12 element matching nori's psi().
    The result has the form c0=(1,0,0), c1=(h0,h1,0) in Fp12
    where h0 = lambda * x_over_y, h1 = neg_mu * y_inv. *)
let eval_to_fp12 (line : G2Line.t) (cache : AffineCache.t) : Fp12.Circuit.t =
  let h0, h1 = eval_line line cache in
  let one_fp2 = Fp2.of_constant Fp2.Constant.one in
  let zero_fp2 = Fp2.of_constant Fp2.Constant.zero in
  { Fp12.Circuit.c0 = { Fp6.Circuit.c0 = one_fp2; c1 = zero_fp2; c2 = zero_fp2 }
  ; c1 = { Fp6.Circuit.c0 = h0; c1 = h1; c2 = zero_fp2 }
  }

(** Multiply f by a line evaluation using sparse multiplication.
    The line evaluates to c0=(1,0,0), c1=(h0,h1,0) in nori's convention.
    This matches nori's Fp12.sparse_mul(psi_result). *)
let mul_by_line (f : Fp12.Circuit.t) (line : G2Line.t) (cache : AffineCache.t) :
    Fp12.Circuit.t =
  let h0, h1 = eval_line line cache in
  Fp12.sparse_mul f ~b00:Fp2.Constant.one ~b10:h0 ~b11:h1
