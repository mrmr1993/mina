(** G2 affine point operations on BN254. *)

module Circuit = struct
  type t = { x : Fp2.Circuit.t; y : Fp2.Circuit.t }
end

module Constant = struct
  type t = { x : Fp2.Constant.t; y : Fp2.Constant.t }
end

let of_constant (pt : Constant.t) : Circuit.t =
  { x = Fp2.of_constant pt.x; y = Fp2.of_constant pt.y }

let negate (pt : Circuit.t) : Circuit.t =
  { x = pt.x; y = Fp2.neg pt.y }

let add_nonzero (p1 : Circuit.t) (p2 : Circuit.t) : Circuit.t =
  let dx = Fp2.sub p2.x p1.x in
  let dy = Fp2.sub p2.y p1.y in
  let lambda = Fp2.mul dy (Fp2.inverse dx) in
  let lambda_sq = Fp2.square lambda in
  let x3 = Fp2.sub (Fp2.sub lambda_sq p1.x) p2.x in
  let y3 = Fp2.sub (Fp2.mul lambda (Fp2.sub p1.x x3)) p1.y in
  { x = x3; y = y3 }

let double (pt : Circuit.t) : Circuit.t =
  let x_sq = Fp2.square pt.x in
  let three_x_sq = Fp2.add (Fp2.add x_sq x_sq) x_sq in
  let two_y = Fp2.add pt.y pt.y in
  let lambda = Fp2.mul three_x_sq (Fp2.inverse two_y) in
  let lambda_sq = Fp2.square lambda in
  let two_x = Fp2.add pt.x pt.x in
  let x3 = Fp2.sub lambda_sq two_x in
  let y3 = Fp2.sub (Fp2.mul lambda (Fp2.sub pt.x x3)) pt.y in
  { x = x3; y = y3 }
