(** 32-bit unsigned integer arithmetic for SHA256.

    A UInt32 is a single circuit field element constrained to [0, 2^32).
    Operations match the o1js UInt32 API for gate-compatible SHA256. *)

module Step = Pickles.Impls.Step
module Field = Step.Field
module Boolean = Step.Boolean

type t = Field.t

let two_to_32 = Field.Constant.of_string "4294967296"

(** Wrap a field element as a UInt32 (no range check). *)
let of_field (x : Field.t) : t = x

(** Get the underlying field element. *)
let to_field (x : t) : Field.t = x

(** Constant UInt32 from int. *)
let of_int (n : int) : t = Field.of_int n

(** Witness a UInt32 from a computation. *)
let witness (compute : unit -> int) : t =
  Step.exists Field.typ ~compute:(fun () ->
      Field.Constant.of_int (compute ()) )

(** Add two UInt32 values modulo 2^32. *)
let add (a : t) (b : t) : t =
  let sum =
    Step.exists Field.typ ~compute:(fun () ->
        let av = Step.As_prover.read_var a in
        let bv = Step.As_prover.read_var b in
        let a_int =
          Bignum_bigint.of_string (Field.Constant.to_string av)
        in
        let b_int =
          Bignum_bigint.of_string (Field.Constant.to_string bv)
        in
        let mask = Bignum_bigint.of_string "4294967295" in
        let r = Bignum_bigint.((a_int + b_int) land mask) in
        Field.Constant.of_string (Bignum_bigint.to_string r) )
  in
  (* Constrain: a + b = sum + q * 2^32 for some q in {0, 1} *)
  let q =
    Step.exists Field.typ ~compute:(fun () ->
        let av = Step.As_prover.read_var a in
        let bv = Step.As_prover.read_var b in
        let a_int =
          Bignum_bigint.of_string (Field.Constant.to_string av)
        in
        let b_int =
          Bignum_bigint.of_string (Field.Constant.to_string bv)
        in
        let total = Bignum_bigint.(a_int + b_int) in
        let two32 = Bignum_bigint.of_string "4294967296" in
        if Bignum_bigint.(total >= two32) then Field.Constant.one
        else Field.Constant.zero )
  in
  (* a + b = sum + q * 2^32 *)
  let lhs = Field.add a b in
  let rhs = Field.add sum (Field.mul q (Field.constant two_to_32)) in
  Step.assert_ (Equal (lhs, rhs)) ;
  sum

(** Bitwise right rotation. *)
let rotr (x : t) ~(n : int) : t =
  Step.exists Field.typ ~compute:(fun () ->
      let xv = Step.As_prover.read_var x in
      let x_int =
        Bignum_bigint.of_string (Field.Constant.to_string xv)
      in
      let mask = Bignum_bigint.of_string "4294967295" in
      let shift = 32 - n in
      let rotated = Bignum_bigint.(
        bit_or (shift_right x_int n)
          (bit_and (shift_left x_int shift) mask) )
      in
      Field.Constant.of_string (Bignum_bigint.to_string rotated) )

(** Bitwise right shift. *)
let shr (x : t) ~(n : int) : t =
  Step.exists Field.typ ~compute:(fun () ->
      let xv = Step.As_prover.read_var x in
      let x_int =
        Bignum_bigint.of_string (Field.Constant.to_string xv)
      in
      let shifted = Bignum_bigint.(shift_right x_int n) in
      Field.Constant.of_string (Bignum_bigint.to_string shifted) )

(** Bitwise XOR. *)
let xor (a : t) (b : t) : t =
  Step.exists Field.typ ~compute:(fun () ->
      let av = Step.As_prover.read_var a in
      let bv = Step.As_prover.read_var b in
      let a_int =
        Bignum_bigint.of_string (Field.Constant.to_string av)
      in
      let b_int =
        Bignum_bigint.of_string (Field.Constant.to_string bv)
      in
      let r = Bignum_bigint.bit_xor a_int b_int in
      Field.Constant.of_string (Bignum_bigint.to_string r) )

(** Bitwise AND. *)
let bit_and (a : t) (b : t) : t =
  Step.exists Field.typ ~compute:(fun () ->
      let av = Step.As_prover.read_var a in
      let bv = Step.As_prover.read_var b in
      let a_int =
        Bignum_bigint.of_string (Field.Constant.to_string av)
      in
      let b_int =
        Bignum_bigint.of_string (Field.Constant.to_string bv)
      in
      let r = Bignum_bigint.bit_and a_int b_int in
      Field.Constant.of_string (Bignum_bigint.to_string r) )

(** Bitwise NOT (complement within 32 bits). *)
let bit_not (a : t) : t =
  Step.exists Field.typ ~compute:(fun () ->
      let av = Step.As_prover.read_var a in
      let a_int =
        Bignum_bigint.of_string (Field.Constant.to_string av)
      in
      let mask = Bignum_bigint.of_string "4294967295" in
      let r = Bignum_bigint.(bit_xor a_int mask) in
      Field.Constant.of_string (Bignum_bigint.to_string r) )
