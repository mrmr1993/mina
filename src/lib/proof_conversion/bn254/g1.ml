(** G1 affine point operations on BN254.

    G1 is the group of points on y^2 = x^3 + 3 over Fp. *)

open Snarky_foreign_field.Foreign_field

let p = Bn254_params.p

(** G1 affine point as a pair of Field3 values. *)
module Circuit = struct
  type t = { x : Field3.t; y : Field3.t }
end

(** Constant G1 point. *)
module Constant = struct
  type t = { x : Bignum_bigint.t; y : Bignum_bigint.t }
end

let of_constant (pt : Constant.t) : Circuit.t =
  { x = Field3.of_constant pt.x; y = Field3.of_constant pt.y }

(** Negate: -P = (x, -y) *)
let negate (pt : Circuit.t) : Circuit.t =
  { x = pt.x; y = negate pt.y ~f:p }

(** Assert that a point lies on the curve y^2 = x^3 + b. *)
let assert_on_curve (pt : Circuit.t) : unit =
  let x_sq = mul pt.x pt.x ~f:p in
  let x_cu = mul x_sq pt.x ~f:p in
  let y_sq = mul pt.y pt.y ~f:p in
  let rhs = add x_cu (Field3.of_constant Bn254_params.curve_b) ~f:p in
  assert_equal y_sq rhs

(** Add two non-equal, non-zero G1 points.
    lambda = (y2 - y1) / (x2 - x1)
    x3 = lambda^2 - x1 - x2
    y3 = lambda * (x1 - x3) - y1 *)
let add_nonzero (p1 : Circuit.t) (p2 : Circuit.t) : Circuit.t =
  let dx = sub p2.x p1.x ~f:p in
  let dy = sub p2.y p1.y ~f:p in
  let lambda = div dy dx ~f:p in
  let lambda_sq = mul lambda lambda ~f:p in
  let x3 = sub (sub lambda_sq p1.x ~f:p) p2.x ~f:p in
  let y3 = sub (mul lambda (sub p1.x x3 ~f:p) ~f:p) p1.y ~f:p in
  { x = x3; y = y3 }

(** Double a G1 point.
    lambda = (3 * x^2) / (2 * y)
    x3 = lambda^2 - 2*x
    y3 = lambda * (x - x3) - y *)
let double (pt : Circuit.t) : Circuit.t =
  let x_sq = mul pt.x pt.x ~f:p in
  let three_x_sq =
    add (add x_sq x_sq ~f:p) x_sq ~f:p
  in
  let two_y = add pt.y pt.y ~f:p in
  let lambda = div three_x_sq two_y ~f:p in
  let lambda_sq = mul lambda lambda ~f:p in
  let two_x = add pt.x pt.x ~f:p in
  let x3 = sub lambda_sq two_x ~f:p in
  let y3 = sub (mul lambda (sub pt.x x3 ~f:p) ~f:p) pt.y ~f:p in
  { x = x3; y = y3 }
