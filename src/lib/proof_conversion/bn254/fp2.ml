(** Fp2 = Fp[u] / (u^2 + 1) arithmetic over BN254 base field.

    Elements are pairs (c0, c1) representing c0 + c1 * u where u^2 = -1. *)

module FF = Snarky_foreign_field.Foreign_field

let p = Bn254_params.p

(** Constant Fp2 element as bignum pairs. *)
module Constant = struct
  type t = FF.Bignum_bigint.t * FF.Bignum_bigint.t

  let zero : t = (FF.Bignum_bigint.zero, FF.Bignum_bigint.zero)

  let one : t = (FF.Bignum_bigint.one, FF.Bignum_bigint.zero)
end

(** Fp2 element as a pair of Field3 values. *)
module Circuit = struct
  type t = { c0 : FF.Field3.t; c1 : FF.Field3.t }

  let typ : (t, Constant.t) Pickles.Impls.Step.Typ.t =
    Pickles.Impls.Step.Typ.transport
      (Pickles.Impls.Step.Typ.tuple2 FF.Field3.typ FF.Field3.typ)
      ~there:(fun (c0, c1) -> (c0, c1))
      ~back:(fun (c0, c1) -> (c0, c1))
    |> Pickles.Impls.Step.Typ.transport_var
      ~there:(fun { c0; c1 } -> (c0, c1))
      ~back:(fun (c0, c1) -> { c0; c1 })
end

let of_constant ((c0, c1) : Constant.t) : Circuit.t =
  { c0 = FF.Field3.of_constant c0; c1 = FF.Field3.of_constant c1 }

let add (a : Circuit.t) (b : Circuit.t) : Circuit.t =
  { c0 = FF.add a.c0 b.c0 ~f:p; c1 = FF.add a.c1 b.c1 ~f:p }

let sub (a : Circuit.t) (b : Circuit.t) : Circuit.t =
  { c0 = FF.sub a.c0 b.c0 ~f:p; c1 = FF.sub a.c1 b.c1 ~f:p }

let neg (a : Circuit.t) : Circuit.t =
  { c0 = FF.negate a.c0 ~f:p; c1 = FF.negate a.c1 ~f:p }

let conjugate (a : Circuit.t) : Circuit.t =
  { c0 = a.c0; c1 = FF.negate a.c1 ~f:p }

let mul (a : Circuit.t) (b : Circuit.t) : Circuit.t =
  let v0 = FF.mul a.c0 b.c0 ~f:p in
  let v1 = FF.mul a.c1 b.c1 ~f:p in
  let c0 = FF.sub v0 v1 ~f:p in
  let a01 = FF.add a.c0 a.c1 ~f:p in
  let b01 = FF.add b.c0 b.c1 ~f:p in
  let t = FF.mul a01 b01 ~f:p in
  let c1 = FF.sub (FF.sub t v0 ~f:p) v1 ~f:p in
  { c0; c1 }

let square (a : Circuit.t) : Circuit.t =
  let sum_ = FF.add a.c0 a.c1 ~f:p in
  let diff = FF.sub a.c0 a.c1 ~f:p in
  let c0 = FF.mul sum_ diff ~f:p in
  let prod = FF.mul a.c0 a.c1 ~f:p in
  let c1 = FF.add prod prod ~f:p in
  { c0; c1 }

let mul_by_fp (a : Circuit.t) (s : FF.Field3.t) : Circuit.t =
  { c0 = FF.mul a.c0 s ~f:p; c1 = FF.mul a.c1 s ~f:p }

let inverse (a : Circuit.t) : Circuit.t =
  let a0_sq = FF.mul a.c0 a.c0 ~f:p in
  let a1_sq = FF.mul a.c1 a.c1 ~f:p in
  let norm = FF.add a0_sq a1_sq ~f:p in
  let norm_inv = FF.inv norm ~f:p in
  { c0 = FF.mul a.c0 norm_inv ~f:p
  ; c1 = FF.negate (FF.mul a.c1 norm_inv ~f:p) ~f:p
  }

let frobenius (a : Circuit.t) : Circuit.t = conjugate a

let assert_equal (a : Circuit.t) (b : Circuit.t) : unit =
  FF.assert_equal a.c0 b.c0 ;
  FF.assert_equal a.c1 b.c1
