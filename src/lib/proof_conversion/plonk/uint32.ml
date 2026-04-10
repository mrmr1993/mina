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

type t = Field.t

(** Wrap a field element as a UInt32 (no range check). *)
let of_field (x : Field.t) : t = x

(** Get the underlying field element. *)
let to_field (x : t) : Field.t = x

(** Constant UInt32 from int. *)
let of_int (n : int) : t = Field.of_int n

let two_to_32 = Bignum_bigint.(pow (of_int 2) (of_int 32))

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
  | Some _ ->
      () (* constants are unchecked, matching o1js *)
  | None ->
      let _a, _b, x0 =
        Pickles.Scalar_challenge.to_field_checked' ~num_bits
          (module Pickles.Impls.Step)
          { inner = x }
      in
      Step.assert_ (Equal (x0, x))

(** Range-check to 32 bits. Matches o1js rangeCheck32. *)
let range_check_32 (x : Field.t) : unit = range_check_n x ~num_bits:32

(** Range-check to 16 bits. Matches o1js rangeCheck16. *)
let range_check_16 (x : Field.t) : unit = range_check_n x ~num_bits:16

(** Range-check to 8 bits. Matches o1js rangeCheck8.
    Checks x fits in 16 bits, then checks 2^8*x fits in 16 bits. *)
let range_check_8 (x : Field.t) : unit =
  match Field.to_constant x with
  | Some _ ->
      ()
  | None ->
      range_check_n x ~num_bits:16 ;
      let x256 =
        Snarky_foreign_field.Foreign_field.seal
          (Field.scale x (Field.Constant.of_int (1 lsl 8)))
      in
      range_check_n x256 ~num_bits:16

(** divMod32: divide n by 2^32, returning (quotient, remainder).
    Matches o1js divMod32 from arithmetic.ts.
    [n_bits] is the maximum bit width of [n]. *)
let div_mod_32 (n : Field.t) ~(n_bits : int) : t * t =
  assert (n_bits >= 0 && n_bits < 255) ;
  (* Constant case: compute directly, matching o1js *)
  match Field.to_constant n with
  | Some c ->
      let n_big = Bignum_bigint.of_string (Field.Constant.to_string c) in
      let q = Bignum_bigint.(shift_right n_big 32) in
      let r = Bignum_bigint.(bit_and n_big mask_32) in
      let qf =
        Field.constant (Field.Constant.of_string (Bignum_bigint.to_string q))
      in
      let rf =
        Field.constant (Field.Constant.of_string (Bignum_bigint.to_string r))
      in
      (qf, rf)
  | None ->
      let quotient_bits = max 0 (n_bits - 32) in
      let quotient =
        Step.exists Field.typ ~compute:(fun () ->
            let nv = Step.As_prover.read_var n in
            let n_big = Bignum_bigint.of_string (Field.Constant.to_string nv) in
            let q = Bignum_bigint.(shift_right n_big 32) in
            Field.Constant.of_string (Bignum_bigint.to_string q) )
      in
      let remainder =
        Step.exists Field.typ ~compute:(fun () ->
            let nv = Step.As_prover.read_var n in
            let n_big = Bignum_bigint.of_string (Field.Constant.to_string nv) in
            let mask = Bignum_bigint.(two_to_32 - one) in
            let r = Bignum_bigint.(n_big land mask) in
            Field.Constant.of_string (Bignum_bigint.to_string r) )
      in
      (* Range-check quotient *)
      ( if quotient_bits = 1 then
        (* assertBool: x*(x-1) = 0 *)
        Step.assert_ (Boolean quotient)
      else if quotient_bits > 0 then
        (* rangeCheckN for quotientBits (round up to multiple of 16) *)
        let check_bits =
          let r = quotient_bits mod 16 in
          if r = 0 then quotient_bits else quotient_bits + (16 - r)
        in
        range_check_n quotient ~num_bits:check_bits ) ;
      (* Range-check remainder to 32 bits *)
      range_check_32 remainder ;
      (* Assert: n = quotient * 2^32 + remainder *)
      let reconstructed =
        Field.((quotient * constant two_to_32_field) + remainder)
      in
      Step.assert_ (Equal (n, reconstructed)) ;
      (quotient, remainder)

(** Add two UInt32 values modulo 2^32.
    Matches o1js addMod32: divMod32(x + y, 33).remainder *)
let add (a : t) (b : t) : t =
  if is_constant a && is_constant b then
    of_field
      (Field.constant
         (Field.Constant.of_string
            (Bignum_bigint.to_string
               Bignum_bigint.(
                 bit_and (to_bigint_const a + to_bigint_const b) mask_32) ) ) )
  else
    let sum = Field.add a b in
    let _q, r = div_mod_32 sum ~n_bits:33 in
    r

(** Ensure a UInt32 is a variable (not constant).
    Kimchi bitwise gates require non-constant Cvars. *)
let ensure_var (x : t) : t =
  match Field.to_constant x with
  | None ->
      x
  | Some c ->
      (* Create a variable and assert equal to the constant *)
      let v = Step.exists Field.typ ~compute:(fun () -> c) in
      Step.assert_ (Equal (v, Field.constant c)) ;
      v

(** Read a circuit variable as a Bignum_bigint during proving. *)
let read_bigint (x : Field.t) : Bignum_bigint.t =
  Bignum_bigint.of_string
    (Field.Constant.to_string (Step.As_prover.read_var x))

(** Convert a Bignum_bigint to a field constant. *)
let bigint_to_const (x : Bignum_bigint.t) : Field.Constant.t =
  Field.Constant.of_string (Bignum_bigint.to_string x)

(** Extract a bit slice from a bigint: bits [start, start+len). *)
let bit_slice (x : Bignum_bigint.t) ~(start : int) ~(len : int) : Bignum_bigint.t =
  Bignum_bigint.(bit_and (shift_right x start) (pow (of_int 2) (of_int len) - one))

(** Build a chain of Xor16 gates matching o1js buildXor.
    Processes 16 bits per iteration. Emits Xor gates + terminal Zero gate
    + assertEquals(0) on terminal values.
    [num_bits] must be a positive multiple of 16 (padded by caller).
    Reference: o1js/src/lib/provable/gadgets/bitwise.ts:buildXor *)
let build_xor (a : Field.t) (b : Field.t) (out : Field.t) ~(num_bits : int) : unit =
  let iterations = num_bits / 16 in
  let a_ref = ref a in
  let b_ref = ref b in
  let out_ref = ref out in
  for _ = 1 to iterations do
    let a_cur = !a_ref in
    let b_cur = !b_ref in
    let out_cur = !out_ref in
    (* Witness 15 values: 4 nybble slices each of a, b, out; 3 next values.
       Matches o1js exists(15, ...) *)
    let slices =
      Array.init 15 ~f:(fun idx ->
          Step.exists Field.typ ~compute:(fun () ->
              let a0 = read_bigint a_cur in
              let b0 = read_bigint b_cur in
              let o0 = read_bigint out_cur in
              let src, start =
                match idx with
                | 0 -> (a0, 0)  | 1 -> (a0, 4)  | 2 -> (a0, 8)  | 3 -> (a0, 12)
                | 4 -> (b0, 0)  | 5 -> (b0, 4)  | 6 -> (b0, 8)  | 7 -> (b0, 12)
                | 8 -> (o0, 0)  | 9 -> (o0, 4)  | 10 -> (o0, 8) | 11 -> (o0, 12)
                | _ -> assert false
              in
              if idx < 12 then bigint_to_const (bit_slice src ~start ~len:4)
              else
                let v = match idx with
                  | 12 -> Bignum_bigint.(shift_right a0 16)
                  | 13 -> Bignum_bigint.(shift_right b0 16)
                  | 14 -> Bignum_bigint.(shift_right o0 16)
                  | _ -> assert false
                in bigint_to_const v ) )
    in
    Step.assert_
      (Xor
         { in1 = a_cur ; in2 = b_cur ; out = out_cur
         ; in1_0 = slices.(0) ; in1_1 = slices.(1)
         ; in1_2 = slices.(2) ; in1_3 = slices.(3)
         ; in2_0 = slices.(4) ; in2_1 = slices.(5)
         ; in2_2 = slices.(6) ; in2_3 = slices.(7)
         ; out_0 = slices.(8) ; out_1 = slices.(9)
         ; out_2 = slices.(10) ; out_3 = slices.(11)
         } ) ;
    a_ref := slices.(12) ;
    b_ref := slices.(13) ;
    out_ref := slices.(14)
  done ;
  Step.assert_
    (Raw { kind = Zero ; values = [| !a_ref; !b_ref; !out_ref |] ; coeffs = [||] }) ;
  (* Match o1js buildXor which asserts all terminal values are zero *)
  let zero = Step.Field.constant Step.Field.Constant.zero in
  Step.Field.Assert.equal zero !a_ref ;
  Step.Field.Assert.equal zero !b_ref ;
  Step.Field.Assert.equal zero !out_ref

(** Bitwise XOR matching o1js Gadgets.xor.
    [length] is the bit width (padded up to multiple of 16 internally).
    Witness output, build xor chain, return output.
    Reference: o1js/src/lib/provable/gadgets/bitwise.ts:xor *)
let xor_n (a : Field.t) (b : Field.t) ~(length : int) : Field.t =
  if is_constant (of_field a) && is_constant (of_field b) then
    Field.constant (bigint_to_const
      Bignum_bigint.(bit_xor (to_bigint_const a) (to_bigint_const b)))
  else
    let pad_length = ((length + 15) / 16) * 16 in
    let output =
      Step.exists Field.typ ~compute:(fun () ->
          bigint_to_const Bignum_bigint.(bit_xor (read_bigint a) (read_bigint b)))
    in
    build_xor a b output ~num_bits:pad_length ;
    output

(** 32-bit XOR for UInt32. *)
let xor (a : t) (b : t) : t =
  of_field (xor_n a b ~length:32)

(** Bitwise AND (32-bit).
    Matches o1js Gadgets.and from gadgets/bitwise.ts:
    witness output, compute xor(a,b), assert 2*output + xor = a + b.
    Reference: o1js/src/lib/provable/gadgets/bitwise.ts:and *)
let bit_and (a : t) (b : t) : t =
  if is_constant a && is_constant b then
    of_field (Field.constant (bigint_to_const
      Bignum_bigint.(bit_and (to_bigint_const a) (to_bigint_const b))))
  else
    let output =
      Step.exists Field.typ ~compute:(fun () ->
          bigint_to_const Bignum_bigint.(bit_and (read_bigint a) (read_bigint b)))
    in
    let xor_output = xor a b in
    Step.Field.Assert.equal
      (Field.add (Field.scale output (Field.Constant.of_int 2)) xor_output)
      (Field.add a b) ;
    of_field output

(** Bitwise NOT (32-bit, unchecked).
    Uses allOnes - x. *)
let bit_not (a : t) : t =
  if is_constant a then
    of_field
      (Field.constant
         (Field.Constant.of_string
            (Bignum_bigint.to_string
               Bignum_bigint.(bit_xor (to_bigint_const a) mask_32) ) ) )
  else
    (* Match nori: allOnes.sub(a).seal() *)
    let all_ones = Field.of_int ((1 lsl 32) - 1) in
    Snarky_foreign_field.Foreign_field.seal (Field.sub all_ones a)

(** Bitwise right rotation (32-bit).
    Matches o1js UInt32.rotate(n, 'right').
    Constant fast path for use in sigma_simple. *)
let rotr (x : t) ~(n : int) : t =
  match Field.to_constant x with
  | Some c ->
      let x_int = Bignum_bigint.of_string (Field.Constant.to_string c) in
      let mask = Bignum_bigint.(two_to_32 - one) in
      let shift = 32 - n in
      let rotated =
        Bignum_bigint.(
          bit_or (shift_right x_int n) (bit_and (shift_left x_int shift) mask))
      in
      of_field
        (Field.constant
           (Field.Constant.of_string (Bignum_bigint.to_string rotated)) )
  | None ->
      Step.exists Field.typ ~compute:(fun () ->
          let xv = Step.As_prover.read_var x in
          let x_int = Bignum_bigint.of_string (Field.Constant.to_string xv) in
          let mask = Bignum_bigint.(two_to_32 - one) in
          let shift = 32 - n in
          let rotated =
            Bignum_bigint.(
              bit_or (shift_right x_int n)
                (bit_and (shift_left x_int shift) mask))
          in
          Field.Constant.of_string (Bignum_bigint.to_string rotated) )

(** Bitwise right shift (32-bit).
    Matches o1js UInt32.rightShift(n).
    Constant fast path for use in sigma_simple. *)
let shr (x : t) ~(n : int) : t =
  match Field.to_constant x with
  | Some c ->
      let x_int = Bignum_bigint.of_string (Field.Constant.to_string c) in
      let shifted = Bignum_bigint.(shift_right x_int n) in
      of_field
        (Field.constant
           (Field.Constant.of_string (Bignum_bigint.to_string shifted)) )
  | None ->
      Step.exists Field.typ ~compute:(fun () ->
          let xv = Step.As_prover.read_var x in
          let x_int = Bignum_bigint.of_string (Field.Constant.to_string xv) in
          let shifted = Bignum_bigint.(shift_right x_int n) in
          Field.Constant.of_string (Bignum_bigint.to_string shifted) )
