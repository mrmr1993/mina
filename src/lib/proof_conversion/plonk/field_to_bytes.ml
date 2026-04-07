(** Convert BN254 foreign field elements to byte arrays for SHA-256 input.

    Matches nori's provableBn254BaseFieldToBytes and
    provableBn254ScalarFieldToBytes from sha/utils.ts.

    The conversion:
    1. Decompose each 88-bit limb of the Field3 into individual bits
       via choose_preimage_var
    2. Prepend 2 zero bits to reach 256 bits
    3. Group into 32 bytes (8 bits each)
    4. Reverse for big-endian byte order

    Reference: nori-proof-conversion/src/sha/utils.ts *)

open! Core_kernel
module Step = Pickles.Impls.Step
module FF = Snarky_foreign_field.Foreign_field

(** A byte is a native field element constrained to [0, 256).
    Corresponds to o1js UInt8. *)
type byte = Step.Field.t

(** Convert a foreign field element (3 limbs) to 32 bytes (big-endian).
    [size_in_bits] is the bit width of the field (254 for both Fp and Fr).

    Matches o1js ForeignField.toBits() + prepend 2 zeros + chunk to bytes +
    reverse. *)
let field3_to_bytes (f3 : FF.Field3.t) ~(size_in_bits : int) : byte array =
  let l0, l1, l2 = f3 in
  let limb_size = 88 in
  let l2_bits = size_in_bits - (2 * limb_size) in
  (* Decompose each limb into bits.
     l0: 88 bits, l1: 88 bits, l2: remaining bits.
     For constant limbs, compute bits without constraints (matching o1js
     Field.toBits() which constant-folds on constant inputs). *)
  let decompose_limb limb length =
    match Step.Field.to_constant limb with
    | Some c ->
      let v = FF.field_const_to_bignum c in
      List.init length ~f:(fun k ->
          if Bignum_bigint.(bit_and (shift_right v k) one = one)
          then Step.Boolean.true_
          else Step.Boolean.false_ )
    | None ->
      (* Match o1js Field.toBits(length):
         1. Provable.witness(Array(Bool, length), ...) — witness + check
         2. Field.fromBits(bits).assertEquals(this)
         choose_preimage_var emits an extra reconstruction gate vs o1js,
         so we replicate the o1js approach directly. *)
      let bits_rev = List.init length ~f:(fun k ->
          let k' = length - 1 - k in
          Step.exists Step.Boolean.typ ~compute:(fun () ->
              let v = Step.As_prover.read_var limb in
              let bi = FF.field_const_to_bignum v in
              Bignum_bigint.(bit_and (shift_right bi k') one = one) ) ) in
      let bits = List.rev bits_rev in
      (* Field.fromBits(bits).assertEquals(this) *)
      let lc = List.foldi bits ~init:Step.Field.zero ~f:(fun i acc bit ->
          let coeff = FF.bignum_to_field_const
            Bignum_bigint.(pow (of_int 2) (of_int i)) in
          Step.Field.add acc (Step.Field.scale (bit :> Step.Field.t) coeff) ) in
      let sealed = FF.seal lc in
      Step.Field.Assert.equal sealed limb ;
      bits
  in
  let bits0 = decompose_limb l0 limb_size in
  let bits1 = decompose_limb l1 limb_size in
  let bits2 = decompose_limb l2 l2_bits in
  (* Concatenate: bits0 ++ bits1 ++ bits2 = size_in_bits bits total *)
  let all_bits = bits0 @ bits1 @ bits2 in
  (* Append 2 zero bits to reach 256 bits (matching nori: x.toBits().concat([false, false])) *)
  let zero_bit = Step.Boolean.false_ in
  let padded_bits = all_bits @ [ zero_bit; zero_bit ] in
  assert (List.length padded_bits = 256) ;
  (* Group into 32 bytes, 8 bits each.
     For each group of 8 bits, reconstruct a field element via fromBits.
     Matches o1js: Field.fromBits(bits.slice(i, i+8)) *)
  let bits_array = Array.of_list padded_bits in
  let bytes_le =
    Array.init 32 ~f:(fun i ->
        let byte_bits = Array.sub bits_array ~pos:(i * 8) ~len:8 in
        (* Pack 8 bits into a byte: sum of bit_j * 2^j *)
        let terms =
          Array.to_list
            (Array.mapi byte_bits ~f:(fun j bit ->
                 let coeff = Step.Field.Constant.of_int (1 lsl j) in
                 Step.Field.scale (bit :> Step.Field.t) coeff ) )
        in
        FF.seal (List.fold terms ~init:Step.Field.zero ~f:Step.Field.add) )
  in
  (* Reverse for big-endian byte order *)
  let bytes_be = Array.copy bytes_le in
  let n = Array.length bytes_be in
  for i = 0 to (n / 2) - 1 do
    let tmp = bytes_be.(i) in
    bytes_be.(i) <- bytes_be.(n - 1 - i) ;
    bytes_be.(n - 1 - i) <- tmp
  done ;
  bytes_be

(** Convert a BN254 base field element (FpC) to 32 bytes.
    BN254 Fp has 254 bits. *)
let fp_to_bytes (x : FF.FpA.t) : byte array =
  field3_to_bytes (FF.FpA.to_field3 x) ~size_in_bits:254

(** Convert a BN254 scalar field element (FrC) to 32 bytes.
    BN254 Fr has 254 bits (same as Fp for this purpose). *)
let fr_to_bytes (x : FF.FpA.t) : byte array =
  field3_to_bytes (FF.FpA.to_field3 x) ~size_in_bits:254

(** Convert 4 bytes (big-endian) to one UInt32 word.
    Matches nori's bytesToWord(bytes.reverse()):
    The bytes are reversed to little-endian before packing.

    byte[0] is MSB, byte[3] is LSB.
    word = byte[3] + byte[2]*256 + byte[1]*65536 + byte[0]*16777216 *)
let bytes_to_word (bytes : byte array) : Uint32.t =
  assert (Array.length bytes = 4) ;
  (* Reverse to little-endian, then pack *)
  let result =
    Array.foldi bytes ~init:Step.Field.zero ~f:(fun i acc b ->
        let shift = 8 * (3 - i) in
        let coeff = Step.Field.Constant.of_string (Int.to_string (1 lsl shift)) in
        Step.Field.add acc (Step.Field.scale b coeff) )
  in
  Uint32.of_field result

(** Convert a foreign field element to UInt32 words for SHA-256 input.
    Returns 8 UInt32 words (32 bytes / 4 bytes per word). *)
let field3_to_words (f3 : FF.Field3.t) ~(size_in_bits : int) :
    Uint32.t array =
  let bytes = field3_to_bytes f3 ~size_in_bits in
  Array.init 8 ~f:(fun i ->
      bytes_to_word (Array.sub bytes ~pos:(i * 4) ~len:4) )
