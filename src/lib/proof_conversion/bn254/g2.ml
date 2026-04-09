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
    piB = (conj(B.x) * gamma_1s[1], conj(B.y) * gamma_1s[2]) *)
let frobenius (pt : Circuit.t) : Circuit.t =
  let g = Bn254_params.gamma_1s in
  let x = Fp2.mul (Fp2.conjugate pt.x) (Fp2.of_constant g.(1)) in
  let y = Fp2.mul (Fp2.conjugate pt.y) (Fp2.of_constant g.(2)) in
  { x; y }

(** Negative Frobenius: conjugate coords, multiply x by gamma_1s[1],
    multiply y by -gamma_1s[2] (pre-negated constant). *)
let neg_gamma_1s_2 : Fp2.Constant.t =
  let open Bignum_bigint in
  let c0, c1 = Bn254_params.gamma_1s.(2) in
  (Bn254_params.p - c0, Bn254_params.p - c1)

let negative_frobenius (pt : Circuit.t) : Circuit.t =
  let g = Bn254_params.gamma_1s in
  let x = Fp2.mul (Fp2.conjugate pt.x) (Fp2.of_constant g.(1)) in
  let y = Fp2.mul (Fp2.conjugate pt.y) (Fp2.of_constant neg_gamma_1s_2) in
  { x; y }

(** G2 point doubling from a known tangent line lambda.
    x3 = lambda^2 - 2*x, y3 = lambda*(x - x3) - y *)
let double_from_line (pt : Circuit.t) ~(lambda : Fp2.Circuit.t) : Circuit.t =
  let lambda_sq = Fp2.square lambda in
  let x3 = Fp2.sub (Fp2.sub lambda_sq pt.x) pt.x in
  let y3 = Fp2.sub (Fp2.mul lambda (Fp2.sub pt.x x3)) pt.y in
  { x = x3; y = y3 }

(** G2 point addition from a known line lambda.
    x3 = lambda^2 - x1 - x2, y3 = lambda*(x1 - x3) - y1 *)
let add_from_line (p1 : Circuit.t) ~(lambda : Fp2.Circuit.t) (p2 : Circuit.t) :
    Circuit.t =
  let lambda_sq = Fp2.square lambda in
  let x3 = Fp2.sub (Fp2.sub lambda_sq p1.x) p2.x in
  let y3 = Fp2.sub (Fp2.mul lambda (Fp2.sub p1.x x3)) p1.y in
  { x = x3; y = y3 }
