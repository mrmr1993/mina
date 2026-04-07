(** BSB22-PLONK hash-to-field: hash two BN254 base field elements to a
    scalar field element.

    Matches nori HashFr from plonk/piop/hash_fr.ts.

    Uses 3 SHA-256 hashes + XOR + bit manipulation to produce an
    element in BN254 Fr.

    Reference: nori-proof-conversion/src/plonk/piop/hash_fr.ts *)

open! Core_kernel
module Step = Pickles.Impls.Step
module FF = Snarky_foreign_field.Foreign_field

(* Constants matching nori HashFr constructor *)
let r = Bn254_params.r

let assert_canonical_fr (x : FF.Field3.t) : FF.FpA.t =
  FF.assert_less_than x ~bound:r ;
  FF.FpA.of_field3_unsafe x

let mul_fr (a : FF.FpA.t) (b : FF.FpA.t) : FF.FpA.t =
  let result = FF.mul (FF.FpA.to_field3 a) (FF.FpA.to_field3 b) ~f:r in
  assert_canonical_fr result

let add_fr (a : FF.FpA.t) (b : FF.FpA.t) : FF.FpA.t =
  let result = FF.add (FF.FpA.to_field3 a) (FF.FpA.to_field3 b) ~f:r in
  assert_canonical_fr result

let hash_fr_len_in_bytes = [| 0x00; 0x30; 0x00 |]
let hash_fr_size_domain = [| 0x0b |]
(* "BSB22-Plonk" in ASCII *)
let bsb22_plonk =
  [| 0x42; 0x53; 0x42; 0x32; 0x32; 0x2d; 0x50; 0x6c; 0x6f; 0x6e; 0x6b |]

(** XOR two 32-byte SHA outputs, byte by byte.
    Matches nori xorShaOutputs (hash_fr.ts:16-28). *)
let xor_sha_outputs (lhs : Step.Field.t array) (rhs : Step.Field.t array) :
    Step.Field.t array =
  assert (Array.length lhs = 32) ;
  assert (Array.length rhs = 32) ;
  Array.init 32 ~f:(fun i ->
      Kimchi_gadgets.Bitwise.bxor
        (FF.seal lhs.(i)) (FF.seal rhs.(i)) 8 ~len_xor:4)

(** Convert lower 128 bits (bytes 16..31) of SHA digest to Fr.
    Matches nori shr128 (hash_fr.ts:30-43).
    Iterates bytes 15 downto 0, decomposes each to bits, packs into FrC. *)
let shr128 (digest_bytes : Step.Field.t array) : FF.FpA.t =
  assert (Array.length digest_bytes = 32) ;
  let sha_bit_repr = Queue.create () in
  for i = 15 downto 0 do
    let length = Step.Field.size_in_bits - 1 in
    let bits_rev = List.init length ~f:(fun k ->
        let k' = length - 1 - k in
        Step.exists Step.Boolean.typ ~compute:(fun () ->
            let v = Step.As_prover.read_var digest_bytes.(i) in
            let bi = FF.field_const_to_bignum v in
            Bignum_bigint.(bit_and (shift_right bi k') one = one) ) ) in
    let bits = List.rev bits_rev in
    let lc = List.foldi bits ~init:Step.Field.zero ~f:(fun j acc bit ->
        let coeff = FF.bignum_to_field_const
          Bignum_bigint.(pow (of_int 2) (of_int j)) in
        Step.Field.add acc (Step.Field.scale (bit :> Step.Field.t) coeff) ) in
    let sealed = FF.seal lc in
    Step.Field.Assert.equal sealed digest_bytes.(i) ;
    let bits = Array.of_list bits in
    for j = 0 to 7 do
      Queue.enqueue sha_bit_repr bits.(j)
    done
  done ;
  let bits = Queue.to_array sha_bit_repr in
  (* FrC.fromBits(shaBitRepr).assertCanonical() *)
  let pack_limb ~pos ~len =
    let terms = Array.to_list (Array.init len ~f:(fun j ->
        let bit = bits.(pos + j) in
        let coeff = FF.bignum_to_field_const
          Bignum_bigint.(pow (of_int 2) (of_int j)) in
        Step.Field.scale (bit :> Step.Field.t) coeff )) in
    List.fold terms ~init:Step.Field.zero ~f:Step.Field.add
  in
  let limb0 = pack_limb ~pos:0 ~len:88 in
  let limb1 = pack_limb ~pos:88 ~len:40 in
  let f3 = (limb0, limb1, Step.Field.zero) in
  assert_canonical_fr f3

(** Shift left by 128 mod r: decompose SHA digest to 254 bits + top 2,
    construct FrU, conditionally add 2^254/2^255 mod r, multiply all by 2^128.
    Matches nori shl_123_modR (hash_fr.ts:45-97). *)
let shl_128_mod_r (digest_bytes : Step.Field.t array) : FF.FpA.t =
  assert (Array.length digest_bytes = 32) ;
  let sha_bit_repr = Queue.create () in
  let bit_255 = ref Step.Boolean.false_ in
  let bit_256 = ref Step.Boolean.false_ in
  for i = 31 downto 0 do
    let length = Step.Field.size_in_bits - 1 in
    let bits_rev = List.init length ~f:(fun k ->
        let k' = length - 1 - k in
        Step.exists Step.Boolean.typ ~compute:(fun () ->
            let v = Step.As_prover.read_var digest_bytes.(i) in
            let bi = FF.field_const_to_bignum v in
            Bignum_bigint.(bit_and (shift_right bi k') one = one) ) ) in
    let bits = List.rev bits_rev in
    let lc = List.foldi bits ~init:Step.Field.zero ~f:(fun j acc bit ->
        let coeff = FF.bignum_to_field_const
          Bignum_bigint.(pow (of_int 2) (of_int j)) in
        Step.Field.add acc (Step.Field.scale (bit :> Step.Field.t) coeff) ) in
    let sealed = FF.seal lc in
    Step.Field.Assert.equal sealed digest_bytes.(i) ;
    let bits = Array.of_list bits in
    for j = 0 to 7 do
      if i = 0 && j = 6 then bit_255 := bits.(j)
      else if i = 0 && j = 7 then bit_256 := bits.(j)
      else Queue.enqueue sha_bit_repr bits.(j)
    done
  done ;
  let bits = Queue.to_array sha_bit_repr in
  let two_254_mod_r = Bignum_bigint.of_string
    "7059779437489773633646340506914701874769131765994106666166191815402473914367" in
  let two_255_mod_r = Bignum_bigint.of_string
    "14119558874979547267292681013829403749538263531988213332332383630804947828734" in
  let sh = Bignum_bigint.of_string
    "340282366920938463463374607431768211456" in  (* 2^128 *)
  let sh_fpa = FF.FpA.of_constant sh in
  let pack_limb ~pos ~len =
    let terms = Array.to_list (Array.init len ~f:(fun j ->
        let bit = bits.(pos + j) in
        let coeff = FF.bignum_to_field_const
          Bignum_bigint.(pow (of_int 2) (of_int j)) in
        Step.Field.scale (bit :> Step.Field.t) coeff )) in
    List.fold terms ~init:Step.Field.zero ~f:Step.Field.add
  in
  let limb0 = pack_limb ~pos:0 ~len:88 in
  let limb1 = pack_limb ~pos:88 ~len:88 in
  let limb2 = pack_limb ~pos:176 ~len:78 in
  let x = FF.FpU.of_field3_unsafe (limb0, limb1, limb2) in
  let cond_field3 (b : Step.Boolean.var) (c : Bignum_bigint.t) : FF.Field3.t =
    let l0, l1, l2 = FF.Field3.Constant.split c in
    let bf = (b :> Step.Field.t) in
    ( Step.Field.scale bf (FF.bignum_to_field_const l0)
    , Step.Field.scale bf (FF.bignum_to_field_const l1)
    , Step.Field.scale bf (FF.bignum_to_field_const l2) )
  in
  let a = cond_field3 !bit_255 two_254_mod_r in
  let b = cond_field3 !bit_256 two_255_mod_r in
  (* x.mul(SH).assertCanonical() *)
  let res = mul_fr
    (FF.FpA.of_field3_unsafe (FF.FpU.to_field3 x)) sh_fpa in
  (* res.add(a.mul(SH).assertCanonical()).assertCanonical() *)
  let a_fpa = assert_canonical_fr a in
  let res = add_fr res (mul_fr a_fpa sh_fpa) in
  (* res.add(b.mul(SH).assertCanonical()).assertCanonical() *)
  let b_fpa = assert_canonical_fr b in
  add_fr res (mul_fr b_fpa sh_fpa)

(** BSB22-PLONK hash: hash two BN254 Fp elements to an Fr element.
    Matches nori HashFr.hash (hash_fr.ts:133-171). *)
let hash (x : FF.FpA.t) (y : FF.FpA.t) : FF.FpA.t =
  let const_bytes arr = Array.map arr ~f:(fun v -> Step.Field.of_int v) in
  let provable_bn254_base_field_to_bytes =
    Fiat_shamir.provable_bn254_base_field_to_bytes in
  (* bytes = 64 zeros ++ x_bytes ++ y_bytes ++ HASH_FR_LEN_IN_BYTES ++ BSB22_Plonk ++ HASH_FR_SIZE_DOMAIN *)
  let b0_input = Array.concat
    [ Array.create ~len:64 Step.Field.zero
    ; provable_bn254_base_field_to_bytes x
    ; provable_bn254_base_field_to_bytes y
    ; const_bytes hash_fr_len_in_bytes
    ; const_bytes bsb22_plonk
    ; const_bytes hash_fr_size_domain
    ] in
  let _h0, b0 = Fiat_shamir.sha256_hash b0_input in
  (* bytes = b0_digest ++ [1] ++ BSB22_Plonk ++ HASH_FR_SIZE_DOMAIN *)
  let b1_input = Array.concat
    [ b0
    ; [| Step.Field.of_int 1 |]
    ; const_bytes bsb22_plonk
    ; const_bytes hash_fr_size_domain
    ] in
  let _h1, b1 = Fiat_shamir.sha256_hash b1_input in
  (* bytes = xor(b0, b1) ++ [2] ++ BSB22_Plonk ++ HASH_FR_SIZE_DOMAIN *)
  let xored = xor_sha_outputs b0 b1 in
  let b2_input = Array.concat
    [ xored
    ; [| Step.Field.of_int 2 |]
    ; const_bytes bsb22_plonk
    ; const_bytes hash_fr_size_domain
    ] in
  let _h2, b2 = Fiat_shamir.sha256_hash b2_input in
  (* res = shl_128_modR(b1) + shr128(b2) *)
  let res = shl_128_mod_r b1 in
  let low = shr128 b2 in
  add_fr res low
