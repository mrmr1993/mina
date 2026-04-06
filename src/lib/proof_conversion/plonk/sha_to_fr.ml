(** Convert SHA-256 digest to BN254 scalar field element.

    Matches nori's shaToFr from plonk/fiat-shamir/sha_to_fr.ts.

    The 256-bit SHA digest is interpreted as a big-endian integer.
    Since BN254 Fr has ~254 bits, the top 2 bits are handled via
    conditional addition of 2^254 mod r and 2^255 mod r.

    Reference: nori-proof-conversion/src/plonk/fiat-shamir/sha_to_fr.ts *)

open! Core_kernel
module Step = Pickles.Impls.Step
module FF = Snarky_foreign_field.Foreign_field

(** 2^254 mod r (BN254 scalar field order). *)
let two_254_mod_r =
  Bignum_bigint.of_string
    "7059779437489773633646340506914701874769131765994106666166191815402473914367"

(** 2^255 mod r. *)
let two_255_mod_r =
  Bignum_bigint.of_string
    "14119558874979547267292681013829403749538263531988213332332383630804947828734"

(** Convert a SHA-256 digest (8 UInt32 words) to a BN254 scalar (FrC).

    Matches nori's shaToFr:
    1. Convert 8 words → 32 bytes → 256 bits (big-endian)
    2. Take 254 low bits, save bits 254 and 255
    3. Construct FrU from 254 bits
    4. Conditionally add 2^254 mod r and 2^255 mod r *)
let sha_to_fr (digest : Uint32.t array) : FF.FpA.t =
  assert (Array.length digest = 8) ;
  (* Convert 8 UInt32 words to 32 bytes.
     Each word is 4 bytes, big-endian within the word.
     Matches nori: wordToBytes(x.value, 4).reverse() for each word,
     then flat() to get 32 bytes. *)
  let bytes =
    Array.concat_map digest ~f:(fun word ->
        (* Decompose each UInt32 into 4 bytes (big-endian) *)
        Array.init 4 ~f:(fun j ->
            Step.exists Step.Field.typ ~compute:(fun () ->
                let wv = Step.As_prover.read_var (Uint32.to_field word) in
                let w_big =
                  Bignum_bigint.of_string
                    (Step.Field.Constant.to_string wv)
                in
                let shift = 8 * (3 - j) in
                let byte_val =
                  Bignum_bigint.(
                    bit_and (shift_right w_big shift) (of_int 255))
                in
                Step.Field.Constant.of_string
                  (Bignum_bigint.to_string byte_val) ) ) )
  in
  (* Constrain byte decomposition: word = b0*2^24 + b1*2^16 + b2*2^8 + b3 *)
  Array.iteri digest ~f:(fun i word ->
      let b = Array.sub bytes ~pos:(i * 4) ~len:4 in
      let reconstructed =
        Step.Field.(
          add
            (add
               (scale b.(0) (Step.Field.Constant.of_int (1 lsl 24)))
               (scale b.(1) (Step.Field.Constant.of_int (1 lsl 16))))
            (add
               (scale b.(2) (Step.Field.Constant.of_int (1 lsl 8)))
               b.(3)))
      in
      Step.assert_ (Equal (Uint32.to_field word, reconstructed)) ) ;
  (* Convert 32 bytes to 256 bits.
     nori iterates bytes 31..0 (reversed), decomposing each to 8 bits.
     The result is little-endian bit array (bit 0 = LSB). *)
  let all_bits =
    let rev_bytes = Array.copy bytes in
    Array.rev_inplace rev_bytes ;
    Array.concat_map rev_bytes ~f:(fun byte_val ->
        let bits = Step.Field.choose_preimage_var byte_val ~length:8 in
        Array.of_list bits )
  in
  assert (Array.length all_bits = 256) ;
  (* Extract bit 254 and bit 255 (the top 2 bits) *)
  let bit_254 = all_bits.(254) in
  let bit_255 = all_bits.(255) in
  (* Take the low 254 bits → construct FrU via fromBits *)
  (* Pack 254 bits into 3 limbs of the Fr field:
     limb0 = bits[0..87], limb1 = bits[88..175], limb2 = bits[176..253] *)
  let pack_limb ~pos ~len =
    let terms =
      Array.to_list
        (Array.init len ~f:(fun j ->
             let bit = all_bits.(pos + j) in
             let coeff =
               FF.bignum_to_field_const Bignum_bigint.(pow (of_int 2) (of_int j))
             in
             Step.Field.scale (bit :> Step.Field.t) coeff ) )
    in
    List.fold terms ~init:Step.Field.zero ~f:Step.Field.add
  in
  let limb0 = pack_limb ~pos:0 ~len:88 in
  let limb1 = pack_limb ~pos:88 ~len:88 in
  let limb2 = pack_limb ~pos:176 ~len:78 in
  let x_unreduced =
    FF.FpU.of_field3_unsafe (limb0, limb1, limb2)
  in
  (* Conditionally add 2^254 mod r if bit_254 is set.
     Matches nori: Provable.if(bit255.equals(true), FrC.provable, sh254, FrC.from(0n))
     We use if_field on each limb. *)
  let cond_field3 (b : Step.Boolean.var) (c : Bignum_bigint.t) : FF.Field3.t =
    let l0, l1, l2 = FF.Field3.Constant.split c in
    let bf = (b :> Step.Field.t) in
    ( Step.Field.scale bf (FF.bignum_to_field_const l0)
    , Step.Field.scale bf (FF.bignum_to_field_const l1)
    , Step.Field.scale bf (FF.bignum_to_field_const l2) )
  in
  let a = cond_field3 bit_254 two_254_mod_r in
  let b = cond_field3 bit_255 two_255_mod_r in
  (* x + a + b, then assertCanonical *)
  let x_f3 = FF.FpU.to_field3 x_unreduced in
  let sum =
    FF.Sum.add
      (FF.Sum.add (FF.Sum.of_field3 x_f3) a)
      b
  in
  let result = FF.Sum.finish_simple sum ~f:Bn254_params.r in
  let result_checked =
    match FF.FpA.assert_almost_reduced
            [ FF.FpU.of_field3_unsafe result ] ~f:Bn254_params.r () with
    | [ a ] -> a
    | _ -> assert false
  in
  let canonical =
    FF.FpC.assert_canonical result_checked ~f:Bn254_params.r
  in
  FF.FpC.to_fpa canonical
