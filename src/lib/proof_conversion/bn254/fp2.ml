(** Fp2 = Fp[u] / (u^2 + 1) arithmetic over BN254 base field.

    Elements are pairs (c0, c1) of FpA values, representing c0 + c1 * u
    where u^2 = -1. Mirrors nori's Fp2 which holds FpA components. *)

open! Core_kernel
module FF = Snarky_foreign_field.Foreign_field
module FpA = FF.FpA

let p = Bn254_params.p

module Constant = struct
  type t = FF.Bignum_bigint.t * FF.Bignum_bigint.t

  let zero : t = (FF.Bignum_bigint.zero, FF.Bignum_bigint.zero)

  let one : t = (FF.Bignum_bigint.one, FF.Bignum_bigint.zero)
end

module Circuit = struct
  type t = { c0 : FpA.t; c1 : FpA.t }

  (** Typ for Fp2 using FpA.typ, matching nori's
      Struct(\{ c0: FpA.provable, c1: FpA.provable \}).
      Witnessing applies MRC + weakBound to each component. *)
  let typ : (t, Constant.t) Pickles.Impls.Step.Typ.t =
    let fpa_typ = FpA.typ ~f:p in
    Pickles.Impls.Step.Typ.transport
      (Pickles.Impls.Step.Typ.tuple2 fpa_typ fpa_typ)
      ~there:(fun (c0, c1) -> (c0, c1))
      ~back:(fun (c0, c1) -> (c0, c1))
    |> Pickles.Impls.Step.Typ.transport_var
         ~there:(fun { c0; c1 } -> (c0, c1))
         ~back:(fun (c0, c1) -> { c0; c1 })
end

let of_constant ((c0, c1) : Constant.t) : Circuit.t =
  { c0 = FpA.of_constant c0; c1 = FpA.of_constant c1 }

(** Convert unreduced pair to Fp2. Matches nori's Fp2.fromUnreduced. *)
let from_unreduced (c0 : FF.FpU.t) (c1 : FF.FpU.t) : Circuit.t =
  match FpA.assert_almost_reduced [ c0; c1 ] ~f:p ~skip_mrc:true () with
  | [ c0a; c1a ] ->
      { c0 = c0a; c1 = c1a }
  | _ ->
      failwith "from_unreduced: unexpected"

(** Fp2 addition: FpA.add each component → unreduced, then fromUnreduced. *)
let add (a : Circuit.t) (b : Circuit.t) : Circuit.t =
  let c0 = FpA.add a.c0 b.c0 ~f:p in
  let c1 = FpA.add a.c1 b.c1 ~f:p in
  from_unreduced c0 c1

let sub (a : Circuit.t) (b : Circuit.t) : Circuit.t =
  let c0 = FpA.sub a.c0 b.c0 ~f:p in
  let c1 = FpA.sub a.c1 b.c1 ~f:p in
  from_unreduced c0 c1

(** Batched sum/difference of multiple Fp2 values.
    Uses a single FF.sum chain per component, matching nori's Fp2.sum.
    More efficient than chaining add/sub for 3+ operands. *)
let sum (inputs : Circuit.t list) (ops : FF.sign list) : Circuit.t =
  let c0s = List.map inputs ~f:(fun x -> FpA.to_field3 x.c0) in
  let c1s = List.map inputs ~f:(fun x -> FpA.to_field3 x.c1) in
  let c0 = FF.FpU.of_field3_unsafe (FF.sum c0s ops ~f:p) in
  let c1 = FF.FpU.of_field3_unsafe (FF.sum c1s ops ~f:p) in
  from_unreduced c0 c1

(* neg returns FpA directly (negation proves result < f) *)
let neg (a : Circuit.t) : Circuit.t =
  let c0 = FpA.neg a.c0 ~f:p in
  let c1 = FpA.neg a.c1 ~f:p in
  { c0; c1 }

let conjugate (a : Circuit.t) : Circuit.t =
  { c0 = a.c0; c1 = FpA.neg a.c1 ~f:p }

(** Fp2 multiplication using witness-and-assertMul pattern.
    Matches nori's Fp2.mul. *)
let mul (a : Circuit.t) (b : Circuit.t) : Circuit.t =
  let a0b0 = FpA.mul a.c0 b.c0 ~f:p in
  let a1b1 = FpA.mul a.c1 b.c1 ~f:p in
  let c0 = FF.FpU.sub a0b0 a1b1 ~f:p in
  let module Step = Pickles.Impls.Step in
  let c1 =
    Step.exists FF.FpU.typ ~compute:(fun () ->
        let read (l0, l1, l2) =
          let r v = FF.field_const_to_bignum (Step.As_prover.read_var v) in
          let open Bignum_bigint in
          r l0 + (r l1 * FF.two_to_limb) + (r l2 * FF.two_to_2limb)
        in
        let a0 = read (FpA.to_field3 a.c0) in
        let a1 = read (FpA.to_field3 a.c1) in
        let b0 = read (FpA.to_field3 b.c0) in
        let b1 = read (FpA.to_field3 b.c1) in
        Bignum_bigint.(((a0 * b1) + (a1 * b0)) % p) )
  in
  let lhs_x =
    FF.Sum.add (FF.Sum.of_field3 (FpA.to_field3 a.c0)) (FpA.to_field3 a.c1)
  in
  let lhs_y =
    FF.Sum.add (FF.Sum.of_field3 (FpA.to_field3 b.c0)) (FpA.to_field3 b.c1)
  in
  let rhs =
    FF.Sum.add
      (FF.Sum.add
         (FF.Sum.of_field3 (FF.FpU.to_field3 c1))
         (FF.FpU.to_field3 a0b0) )
      (FF.FpU.to_field3 a1b1)
  in
  FF.assert_mul_sum (FF.Sum_input lhs_x) (FF.Sum_input lhs_y) (FF.Sum_input rhs)
    ~f:p ;
  from_unreduced c0 c1

(** Fp2 squaring using witness-and-assertMul pattern.
    Matches nori's Fp2.square:
      c0 = (a0+a1)(a0-a1) = a0^2-a1^2
      c1 = (a0+a0)*a1     = 2*a0*a1
    Witnesses c0,c1 directly, uses Sum accumulators for assertMul. *)
let square (a : Circuit.t) : Circuit.t =
  let module Step = Pickles.Impls.Step in
  let c0, c1 =
    let c =
      Step.exists (Step.Typ.tuple2 FF.FpU.typ FF.FpU.typ) ~compute:(fun () ->
          let read (l0, l1, l2) =
            let r v = FF.field_const_to_bignum (Step.As_prover.read_var v) in
            let open Bignum_bigint in
            r l0 + (r l1 * FF.two_to_limb) + (r l2 * FF.two_to_2limb)
          in
          let a0 = read (FpA.to_field3 a.c0) in
          let a1 = read (FpA.to_field3 a.c1) in
          Bignum_bigint.
            ( ((((a0 * a0) - (a1 * a1)) % p) + p) % p
            , ((a0 * a1 * of_int 2 % p) + p) % p ) )
    in
    (fst c, snd c)
  in
  (* c0 = (a0+a1)*(a0-a1) *)
  let sum_a0_a1 =
    FF.Sum.add (FF.Sum.of_field3 (FpA.to_field3 a.c0)) (FpA.to_field3 a.c1)
  in
  let diff_a0_a1 =
    FF.Sum.sub (FF.Sum.of_field3 (FpA.to_field3 a.c0)) (FpA.to_field3 a.c1)
  in
  FF.assert_mul_sum (FF.Sum_input sum_a0_a1) (FF.Sum_input diff_a0_a1)
    (FF.Field3_input (FF.FpU.to_field3 c0))
    ~f:p ;
  (* c1 = (a0+a0)*a1 *)
  let sum_a0_a0 =
    FF.Sum.add (FF.Sum.of_field3 (FpA.to_field3 a.c0)) (FpA.to_field3 a.c0)
  in
  FF.assert_mul_sum (FF.Sum_input sum_a0_a0)
    (FF.Field3_input (FpA.to_field3 a.c1))
    (FF.Field3_input (FF.FpU.to_field3 c1))
    ~f:p ;
  from_unreduced c0 c1

(** Multiply by an Fp scalar. The scalar should already be FpA. *)
let mul_by_fp (a : Circuit.t) (s : FpA.t) : Circuit.t =
  let c0 = FpA.mul a.c0 s ~f:p in
  let c1 = FpA.mul a.c1 s ~f:p in
  from_unreduced c0 c1

let inverse (a : Circuit.t) : Circuit.t =
  let a0_sq = FpA.mul a.c0 a.c0 ~f:p in
  let a1_sq = FpA.mul a.c1 a.c1 ~f:p in
  (* a0_sq, a1_sq are FpU (from mul); use FpU.add *)
  let norm = FF.FpU.add a0_sq a1_sq ~f:p in
  let norm_a =
    match FpA.assert_almost_reduced [ norm ] ~f:p ~skip_mrc:true () with
    | [ n ] ->
        n
    | _ ->
        failwith "inverse"
  in
  let norm_inv = FpA.inv norm_a ~f:p in
  let c0 = FpA.mul a.c0 norm_inv ~f:p in
  let c1_pos = FpA.mul a.c1 norm_inv ~f:p in
  (* neg on FpU result; from_unreduced converts both to FpA *)
  let c1 = FF.FpU.neg c1_pos ~f:p in
  from_unreduced c0 c1

let frobenius (a : Circuit.t) : Circuit.t = conjugate a

let assert_equal (a : Circuit.t) (b : Circuit.t) : unit =
  FF.assert_equal (FpA.to_field3 a.c0) (FpA.to_field3 b.c0) ;
  FF.assert_equal (FpA.to_field3 a.c1) (FpA.to_field3 b.c1)
