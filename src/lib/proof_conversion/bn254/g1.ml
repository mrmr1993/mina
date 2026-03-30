(** G1 affine point operations on BN254. *)

open! Core_kernel
module FF = Snarky_foreign_field.Foreign_field

let p = Bn254_params.p

module Constant = struct
  type t = { x : FF.Bignum_bigint.t; y : FF.Bignum_bigint.t }
end

module Circuit = struct
  type t = { x : FF.Field3.t; y : FF.Field3.t }

  let typ : (t, Constant.t) Pickles.Impls.Step.Typ.t =
    Pickles.Impls.Step.Typ.transport
      (Pickles.Impls.Step.Typ.tuple2 FF.Field3.typ FF.Field3.typ)
      ~there:(fun { Constant.x; y } -> (x, y))
      ~back:(fun (x, y) -> { Constant.x; y })
    |> Pickles.Impls.Step.Typ.transport_var
         ~there:(fun { x; y } -> (x, y))
         ~back:(fun (x, y) -> { x; y })
end

let of_constant (pt : Constant.t) : Circuit.t =
  { x = FF.Field3.of_constant pt.x; y = FF.Field3.of_constant pt.y }

let negate (pt : Circuit.t) : Circuit.t = { x = pt.x; y = FF.negate pt.y ~f:p }

let assert_on_curve (pt : Circuit.t) : unit =
  let x_sq = FF.mul pt.x pt.x ~f:p in
  let x_cu = FF.mul x_sq pt.x ~f:p in
  let y_sq = FF.mul pt.y pt.y ~f:p in
  let rhs = FF.add x_cu (FF.Field3.of_constant Bn254_params.curve_b) ~f:p in
  FF.assert_equal y_sq rhs

let add_nonzero (p1 : Circuit.t) (p2 : Circuit.t) : Circuit.t =
  let dx = FF.sub p2.x p1.x ~f:p in
  let dy = FF.sub p2.y p1.y ~f:p in
  let lambda = FF.div dy dx ~f:p in
  let lambda_sq = FF.mul lambda lambda ~f:p in
  let x3 = FF.sub (FF.sub lambda_sq p1.x ~f:p) p2.x ~f:p in
  let y3 = FF.sub (FF.mul lambda (FF.sub p1.x x3 ~f:p) ~f:p) p1.y ~f:p in
  { x = x3; y = y3 }

let double (pt : Circuit.t) : Circuit.t =
  let x_sq = FF.mul pt.x pt.x ~f:p in
  let three_x_sq = FF.add (FF.add x_sq x_sq ~f:p) x_sq ~f:p in
  let two_y = FF.add pt.y pt.y ~f:p in
  let lambda = FF.div three_x_sq two_y ~f:p in
  let lambda_sq = FF.mul lambda lambda ~f:p in
  let two_x = FF.add pt.x pt.x ~f:p in
  let x3 = FF.sub lambda_sq two_x ~f:p in
  let y3 = FF.sub (FF.mul lambda (FF.sub pt.x x3 ~f:p) ~f:p) pt.y ~f:p in
  { x = x3; y = y3 }
