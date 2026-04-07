(** 32-bit unsigned integer arithmetic for SHA-256.

    Uses constrained kimchi gadgets (XOR, AND, NOT, range checks) to match
    the o1js UInt32 gate sequence exactly. Each operation produces real
    constraints, unlike the previous prover-only implementation.

    Reference: o1js/src/lib/provable/int.ts (UInt32)
               o1js/src/lib/provable/gadgets/arithmetic.ts (divMod32)
               o1js/src/lib/provable/gadgets/bitwise.ts *)

open! Core_kernel
module Step = Pickles.Impls.Step
module Field = Step.Field
module Bitwise = Kimchi_gadgets.Bitwise

type t = Field.t

(** Wrap a field element as a UInt32 (no range check). *)
let of_field (x : Field.t) : t = x

(** Get the underlying field element. *)
let to_field (x : t) : Field.t = x

(** Constant UInt32 from int. *)
let of_int (n : int) : t = Field.of_int n

let two_to_32 =
  Bignum_bigint.(pow (of_int 2) (of_int 32))

let two_to_32_field =
  Field.Constant.of_string (Bignum_bigint.to_string two_to_32)

let mask_32 = Bignum_bigint.(two_to_32 - one)

(** Helper: check if a field is constant. *)
let is_constant (x : t) : bool =
  match Field.to_constant x with Some _ -> true | None -> false

(** Helper: get constant value as Bignum_bigint. *)
let to_bigint_const (x : t) : Bignum_bigint.t =
  match Field.to_constant x with
  | Some c ->
      Bignum_bigint.of_string (Field.Constant.to_string c)
  | None ->
      failwith "UInt32.to_bigint_const: not a constant"

(** Range-check a field value to n bits (n must be a multiple of 16).
    Matches o1js rangeCheckN which calls truncateToBits16.
    Uses Pickles.Scalar_challenge.to_field_checked' internally.
    No-op for constants (matching o1js behavior). *)
let range_check_n (x : Field.t) ~(num_bits : int) : unit =
  assert (num_bits > 0 && num_bits mod 16 = 0) ;
  match Field.to_constant x with
  | Some _ -> ()  (* constants are unchecked, matching o1js *)
  | None ->
    let _a, _b, x0 =
      Pickles.Scalar_challenge.to_field_checked' ~num_bits
        (module Pickles.Impls.Step)
        { inner = x }
    in
    Step.assert_ (Equal (x0, x))

(** Range-check to 32 bits. Matches o1js rangeCheck32. *)
let range_check_32 (x : Field.t) : unit =
  range_check_n x ~num_bits:32

(** Range-check to 16 bits. Matches o1js rangeCheck16. *)
let range_check_16 (x : Field.t) : unit =
  range_check_n x ~num_bits:16

(** divMod32: divide n by 2^32, returning (quotient, remainder).
    Matches o1js divMod32 from arithmetic.ts.
    [n_bits] is the maximum bit width of [n]. *)
let div_mod_32 (n : Field.t) ~(n_bits : int) : t * t =
  assert (n_bits >= 0 && n_bits < 255) ;
  (* Constant case: compute directly, matching o1js *)
  ( match Field.to_constant n with
  | Some c ->
      let n_big = Bignum_bigint.of_string (Field.Constant.to_string c) in
      let q = Bignum_bigint.(shift_right n_big 32) in
      let r = Bignum_bigint.(bit_and n_big mask_32) in
      let qf = Field.constant (Field.Constant.of_string (Bignum_bigint.to_string q)) in
      let rf = Field.constant (Field.Constant.of_string (Bignum_bigint.to_string r)) in
      (qf, rf)
  | None ->
  let quotient_bits = max 0 (n_bits - 32) in
  let quotient =
    Step.exists Field.typ ~compute:(fun () ->
        let nv = Step.As_prover.read_var n in
        let n_big =
          Bignum_bigint.of_string (Field.Constant.to_string nv)
        in
        let q = Bignum_bigint.(shift_right n_big 32) in
        Field.Constant.of_string (Bignum_bigint.to_string q) )
  in
  let remainder =
    Step.exists Field.typ ~compute:(fun () ->
        let nv = Step.As_prover.read_var n in
        let n_big =
          Bignum_bigint.of_string (Field.Constant.to_string nv)
        in
        let mask = Bignum_bigint.(two_to_32 - one) in
        let r = Bignum_bigint.(n_big land mask) in
        Field.Constant.of_string (Bignum_bigint.to_string r) )
  in
  (* Range-check quotient *)
  ( if quotient_bits = 1 then
      (* assertBool: x*(x-1) = 0 *)
      Step.assert_ (Boolean quotient)
    else if quotient_bits > 0 then begin
      (* rangeCheckN for quotientBits (round up to multiple of 16) *)
      let check_bits =
        let r = quotient_bits mod 16 in
        if r = 0 then quotient_bits else quotient_bits + (16 - r)
      in
      range_check_n quotient ~num_bits:check_bits
    end ) ;
  (* Range-check remainder to 32 bits *)
  range_check_32 remainder ;
  (* Assert: n = quotient * 2^32 + remainder *)
  let reconstructed =
    Field.(
      (quotient * constant two_to_32_field) + remainder)
  in
  Step.assert_ (Equal (n, reconstructed)) ;
  (quotient, remainder) )

(** Add two UInt32 values modulo 2^32.
    Matches o1js addMod32: divMod32(x + y, 33).remainder *)
let add (a : t) (b : t) : t =
  if is_constant a && is_constant b then
    of_field (Field.constant (Field.Constant.of_string
      (Bignum_bigint.to_string Bignum_bigint.(bit_and (to_bigint_const a + to_bigint_const b) mask_32))))
  else begin
    let sum = Field.add a b in
    let _q, r = div_mod_32 sum ~n_bits:33 in
    r
  end

(** Ensure a UInt32 is a variable (not constant).
    Kimchi bitwise gates require non-constant Cvars. *)
let ensure_var (x : t) : t =
  match Field.to_constant x with
  | None -> x
  | Some c ->
      (* Create a variable and assert equal to the constant *)
      let v = Step.exists Field.typ ~compute:(fun () -> c) in
      Step.assert_ (Equal (v, Field.constant c)) ;
      v

(** Bitwise XOR (32-bit).
    Uses kimchi Xor gate via Bitwise.bxor.
    Falls back to constant computation when both inputs are constant. *)
let xor (a : t) (b : t) : t =
  if is_constant a && is_constant b then
    of_field (Field.constant (Field.Constant.of_string
      (Bignum_bigint.to_string Bignum_bigint.(bit_xor (to_bigint_const a) (to_bigint_const b)))))
  else
    Bitwise.bxor a b 32 ~len_xor:4

(** Bitwise AND (32-bit).
    Uses kimchi AND gadget via Bitwise.band. *)
let bit_and (a : t) (b : t) : t =
  if is_constant a && is_constant b then
    of_field (Field.constant (Field.Constant.of_string
      (Bignum_bigint.to_string Bignum_bigint.(bit_and (to_bigint_const a) (to_bigint_const b)))))
  else
    Bitwise.band a b 32 ~len_xor:4

(** Bitwise NOT (32-bit, unchecked).
    Uses allOnes - x. *)
let bit_not (a : t) : t =
  if is_constant a then
    of_field (Field.constant (Field.Constant.of_string
      (Bignum_bigint.to_string Bignum_bigint.(bit_xor (to_bigint_const a) mask_32))))
  else begin
    (* Match nori: allOnes.sub(a).seal() *)
    let all_ones = Field.of_int ((1 lsl 32) - 1) in
    Snarky_foreign_field.Foreign_field.seal (Field.sub all_ones a)
  end

(** Bitwise right rotation (32-bit).
    Matches o1js UInt32.rotate(n, 'right').
    Constant fast path for use in sigma_simple. *)
let rotr (x : t) ~(n : int) : t =
  match Field.to_constant x with
  | Some c ->
    let x_int = Bignum_bigint.of_string (Field.Constant.to_string c) in
    let mask = Bignum_bigint.(two_to_32 - one) in
    let shift = 32 - n in
    let rotated = Bignum_bigint.(
      bit_or (shift_right x_int n) (bit_and (shift_left x_int shift) mask)) in
    of_field (Field.constant (Field.Constant.of_string (Bignum_bigint.to_string rotated)))
  | None ->
    Step.exists Field.typ ~compute:(fun () ->
        let xv = Step.As_prover.read_var x in
        let x_int = Bignum_bigint.of_string (Field.Constant.to_string xv) in
        let mask = Bignum_bigint.(two_to_32 - one) in
        let shift = 32 - n in
        let rotated = Bignum_bigint.(
          bit_or (shift_right x_int n) (bit_and (shift_left x_int shift) mask)) in
        Field.Constant.of_string (Bignum_bigint.to_string rotated) )

(** Bitwise right shift (32-bit).
    Matches o1js UInt32.rightShift(n).
    Constant fast path for use in sigma_simple. *)
let shr (x : t) ~(n : int) : t =
  match Field.to_constant x with
  | Some c ->
    let x_int = Bignum_bigint.of_string (Field.Constant.to_string c) in
    let shifted = Bignum_bigint.(shift_right x_int n) in
    of_field (Field.constant (Field.Constant.of_string (Bignum_bigint.to_string shifted)))
  | None ->
    Step.exists Field.typ ~compute:(fun () ->
        let xv = Step.As_prover.read_var x in
        let x_int = Bignum_bigint.of_string (Field.Constant.to_string xv) in
        let shifted = Bignum_bigint.(shift_right x_int n) in
        Field.Constant.of_string (Bignum_bigint.to_string shifted) )
