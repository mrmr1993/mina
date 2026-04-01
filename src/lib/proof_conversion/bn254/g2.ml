(** G2 affine point operations on BN254. *)

open! Core_kernel

module Constant = struct
  type t = { x : Fp2.Constant.t; y : Fp2.Constant.t }
end

module Circuit = struct
  type t = { x : Fp2.Circuit.t; y : Fp2.Circuit.t }

  let typ : (t, Constant.t) Pickles.Impls.Step.Typ.t =
    Pickles.Impls.Step.Typ.transport
      (Pickles.Impls.Step.Typ.tuple2 Fp2.Circuit.typ Fp2.Circuit.typ)
      ~there:(fun { Constant.x; y } -> (x, y))
      ~back:(fun (x, y) -> { Constant.x; y })
    |> Pickles.Impls.Step.Typ.transport_var
         ~there:(fun { x; y } -> (x, y))
         ~back:(fun (x, y) -> { x; y })
end

let of_constant (pt : Constant.t) : Circuit.t =
  { x = Fp2.of_constant pt.x; y = Fp2.of_constant pt.y }

let negate (pt : Circuit.t) : Circuit.t = { x = pt.x; y = Fp2.neg pt.y }

let add_nonzero (p1 : Circuit.t) (p2 : Circuit.t) : Circuit.t =
  let dx = Fp2.sub p2.x p1.x in
  let dy = Fp2.sub p2.y p1.y in
  let lambda = Fp2.mul dy (Fp2.inverse dx) in
  let lambda_sq = Fp2.square lambda in
  let x3 = Fp2.sub (Fp2.sub lambda_sq p1.x) p2.x in
  let y3 = Fp2.sub (Fp2.mul lambda (Fp2.sub p1.x x3)) p1.y in
  { x = x3; y = y3 }

(** Frobenius endomorphism on G2: conjugate coords, multiply by gammas.
    piB = (conj(B.x) * gamma_1s[1], conj(B.y) * gamma_1s[2])
    Matches nori's G2Affine.frobenius(). *)
let frobenius (pt : Circuit.t) : Circuit.t =
  let g = Bn254_params.gamma_1s in
  { x = Fp2.mul (Fp2.conjugate pt.x) (Fp2.of_constant g.(1))
  ; y = Fp2.mul (Fp2.conjugate pt.y) (Fp2.of_constant g.(2))
  }

(** Negative Frobenius: frobenius then negate y.
    pi2B = (conj(piB.x) * gamma_1s[1], -conj(piB.y) * gamma_1s[2])
    Matches nori's G2Affine.negative_frobenius(). *)
let negative_frobenius (pt : Circuit.t) : Circuit.t =
  let g = Bn254_params.gamma_1s in
  { x = Fp2.mul (Fp2.conjugate pt.x) (Fp2.of_constant g.(1))
  ; y = Fp2.neg (Fp2.mul (Fp2.conjugate pt.y) (Fp2.of_constant g.(2)))
  }

(** G2 point doubling from a known tangent line lambda.
    x3 = lambda^2 - 2*x, y3 = lambda*(x - x3) - y
    Matches nori's G2Affine.double_from_line(lambda). *)
let double_from_line (pt : Circuit.t) ~(lambda : Fp2.Circuit.t) : Circuit.t =
  let lambda_sq = Fp2.square lambda in
  let x3 = Fp2.sub (Fp2.sub lambda_sq pt.x) pt.x in
  let y3 = Fp2.sub (Fp2.mul lambda (Fp2.sub pt.x x3)) pt.y in
  { x = x3; y = y3 }

(** G2 point addition from a known line lambda.
    x3 = lambda^2 - x1 - x2, y3 = lambda*(x1 - x3) - y1
    Matches nori's G2Affine.add_from_line(lambda, rhs). *)
let add_from_line (p1 : Circuit.t) ~(lambda : Fp2.Circuit.t)
    (p2 : Circuit.t) : Circuit.t =
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
