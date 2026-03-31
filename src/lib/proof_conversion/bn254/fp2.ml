(** Fp2 = Fp[u] / (u^2 + 1) arithmetic over BN254 base field.

    Elements are pairs (c0, c1) representing c0 + c1 * u where u^2 = -1. *)

open! Core_kernel
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

let _fp2_mul_trace = ref false

let marker_ (x : int) =
  let module Step = Pickles.Impls.Step in
  Step.assert_
    (Raw
       { kind = Zero
       ; values = [||]
       ; coeffs =
           Array.map ~f:Step.Field.Constant.of_int [| x; 1; 2; 3; 4; 5; 6 |]
       } )

(** Fp2 multiplication using witness-and-assertMul pattern.
    Instead of computing (a0+a1)*(b0+b1) with a 3rd FF.mul,
    witnesses c1 directly and verifies via assert_mul_sum:
      (a0 + a1) * (b0 + b1) = c1 + a0*b0 + a1*b1
    Saves 1 FF.mul and its range checks per Fp2.mul. *)
let mul (a : Circuit.t) (b : Circuit.t) : Circuit.t =
  let trace = !_fp2_mul_trace in
  if trace then marker_ 3000 ;
  let a0b0 = FF.mul a.c0 b.c0 ~f:p in
  if trace then marker_ 3001 ;
  let a1b1 = FF.mul a.c1 b.c1 ~f:p in
  if trace then marker_ 3002 ;
  let c0 = FF.sub a0b0 a1b1 ~f:p in
  if trace then marker_ 3003 ;
  (* Witness c1 = a0*b1 + a1*b0 directly *)
  let module Step = Pickles.Impls.Step in
  let c1 =
    Step.exists FF.Field3.typ ~compute:(fun () ->
        let read (l0, l1, l2) =
          let r v = FF.field_const_to_bignum (Step.As_prover.read_var v) in
          let open Bignum_bigint in
          r l0 + (r l1 * FF.two_to_limb) + (r l2 * FF.two_to_2limb)
        in
        let a0 = read a.c0 in
        let a1 = read a.c1 in
        let b0 = read b.c0 in
        let b1 = read b.c1 in
        Bignum_bigint.(((a0 * b1) + (a1 * b0)) % p) )
  in
  (* Assert: (a0 + a1) * (b0 + b1) = c1 + a0b0 + a1b1 *)
  let lhs_x = FF.Sum.add (FF.Sum.of_field3 a.c0) a.c1 in
  let lhs_y = FF.Sum.add (FF.Sum.of_field3 b.c0) b.c1 in
  let rhs = FF.Sum.add (FF.Sum.add (FF.Sum.of_field3 c1) a0b0) a1b1 in
  FF.assert_mul_sum (FF.Sum_input lhs_x) (FF.Sum_input lhs_y) (FF.Sum_input rhs)
    ~f:p ;
  if trace then marker_ 3005 ;
  _fp2_mul_trace := false ;
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
  FF.assert_equal a.c0 b.c0 ; FF.assert_equal a.c1 b.c1
