(** Fiat-Shamir transcript for PLONK proof verification.

    Uses SHA-256 to derive deterministic challenges from the proof
    and verification key data. Matches the SP1 PLONK Fiat-Shamir
    transcript construction.

    Reference: nori-proof-conversion/src/plonk/fiat-shamir/index.ts *)

open! Core_kernel
module Step = Pickles.Impls.Step
module FF = Snarky_foreign_field.Foreign_field

(** In-circuit Fiat-Shamir state (mutable). *)
type t = Plonk_accumulator.circuit_fs

(** SHA-256 padding: append 0x80 byte, zeros, then 8-byte big-endian length.
    Total must be multiple of 64 bytes (512 bits per block).
    Returns array of 16-word blocks. *)
let sha256_pad_and_block (bytes : Field_to_bytes.byte array) :
    Uint32.t array array =
  let msg_len = Array.length bytes in
  let bit_len = msg_len * 8 in
  (* Pad: 1 byte 0x80, then zeros, then 8-byte big-endian length *)
  let padded_len =
    let base = msg_len + 1 + 8 in
    let rem = base mod 64 in
    if rem = 0 then base else base + (64 - rem)
  in
  let padded = Array.create ~len:padded_len Step.Field.zero in
  Array.blit ~src:bytes ~src_pos:0 ~dst:padded ~dst_pos:0 ~len:msg_len ;
  padded.(msg_len) <- Step.Field.of_int 0x80 ;
  (* Length in bits as big-endian 8 bytes at end *)
  for i = 0 to 7 do
    let shift = 8 * (7 - i) in
    let byte_val = (bit_len lsr shift) land 0xff in
    padded.(padded_len - 8 + i) <- Step.Field.of_int byte_val
  done ;
  (* Convert to UInt32 words: 4 bytes per word, big-endian *)
  let n_words = padded_len / 4 in
  let words =
    Array.init n_words ~f:(fun i ->
        Field_to_bytes.bytes_to_word (Array.sub padded ~pos:(i * 4) ~len:4) )
  in
  (* Split into 16-word blocks *)
  let n_blocks = n_words / 16 in
  Array.init n_blocks ~f:(fun i -> Array.sub words ~pos:(i * 16) ~len:16)

(** SHA-256 hash of a byte array (handles padding).
    Returns 8 UInt32 words and a Bytes32 digest. *)
let sha256_hash (bytes : Field_to_bytes.byte array) :
    Uint32.t array * Plonk_accumulator.bytes32 =
  let blocks = sha256_pad_and_block bytes in
  let h = Sha256.hash_blocks blocks in
  (* Convert 8 UInt32 words to 32 bytes (for digest storage).
     Each word → witness 4 bytes + constrain, matching nori:
     H.map(x => wordToBytes(x.value, 4).reverse()).flat()
     Interleave witness + constrain per word to match nori gate order. *)
  let digest_bytes =
    let all_bytes = Queue.create () in
    for wi = 0 to 7 do
      let word = h.(wi) in
      (* wordToBytes: Provable.witness(Array(UInt8, 4), ...)
         Witness all 4 bytes first, then check all 4 (matching nori order) *)
      let bytes_le =
        Array.init 4 ~f:(fun j ->
            let shift = 8 * j in
            Step.exists Step.Field.typ ~compute:(fun () ->
                let wv = Step.As_prover.read_var (Uint32.to_field word) in
                let w_big =
                  Bignum_bigint.of_string (Step.Field.Constant.to_string wv)
                in
                let byte_val =
                  Bignum_bigint.(bit_and (shift_right w_big shift) (of_int 255))
                in
                Step.Field.Constant.of_string (Bignum_bigint.to_string byte_val) ) )
      in
      (* UInt8 check: rangeCheck8 on each byte *)
      Array.iter bytes_le ~f:Uint32.range_check_8 ;
      (* bytesToWord(bytes).assertEquals(word) *)
      let reconstructed =
        Array.foldi bytes_le ~init:Step.Field.zero ~f:(fun j acc b ->
            let shift = Step.Field.Constant.of_int (1 lsl (8 * j)) in
            Step.Field.add acc (Step.Field.scale b shift) )
      in
      Step.Field.Assert.equal reconstructed (Uint32.to_field word) ;
      (* .reverse() for big-endian *)
      let bytes_be = Array.copy bytes_le in
      let n = Array.length bytes_be in
      for k = 0 to (n / 2) - 1 do
        let tmp = bytes_be.(k) in
        bytes_be.(k) <- bytes_be.(n - 1 - k) ;
        bytes_be.(n - 1 - k) <- tmp
      done ;
      Array.iter bytes_be ~f:(Queue.enqueue all_bytes)
    done ;
    Queue.to_array all_bytes
  in
  (h, digest_bytes)

(** provableBn254BaseFieldToBytes: convert FpA to 32 bytes.
    Matches nori sha/utils.ts:provableBn254BaseFieldToBytes. *)
let provable_bn254_base_field_to_bytes (x : FF.FpA.t) :
    Field_to_bytes.byte array =
  Field_to_bytes.fp_to_bytes x

(** provableBn254ScalarFieldToBytes: convert FrA to 32 bytes.
    Matches nori sha/utils.ts:provableBn254ScalarFieldToBytes. *)
let provable_bn254_scalar_field_to_bytes (x : FF.FpA.t) :
    Field_to_bytes.byte array =
  Field_to_bytes.fr_to_bytes x

(** Squeeze gamma challenge from proof + VK + public inputs.
    Matches nori squeezeGamma (fiat-shamir/index.ts:206-297). *)
let squeeze_gamma (fs : t) ~(proof : Plonk_accumulator.circuit_proof)
    ~(pi0 : FF.FpA.t) ~(pi1 : FF.FpA.t) ~(vk : Plonk_proof.vk) : unit =
  let gamma_separator =
    FF.FpA.of_constant (Bignum_bigint.of_string "0x67616d6d61")
  in
  (* TODO: we can read this from file *)
  let separator_bytes = provable_bn254_base_field_to_bytes gamma_separator in

  (* gamma is 39 bits, so we leave only 40 bits (to keep it multiple of 8)
     and we cut the rest (256 - 40) bits which is 27 bytes *)
  let cm_bytes =
    ref (Array.sub separator_bytes ~pos:27 ~len:5 |> Array.to_list)
  in
  let append bs = cm_bytes := !cm_bytes @ Array.to_list bs in

  let s1x = provable_bn254_base_field_to_bytes (FF.FpA.of_constant vk.s1.x) in
  append s1x ;

  let s1y = provable_bn254_base_field_to_bytes (FF.FpA.of_constant vk.s1.y) in
  append s1y ;

  let s2x = provable_bn254_base_field_to_bytes (FF.FpA.of_constant vk.s2.x) in
  append s2x ;

  let s2y = provable_bn254_base_field_to_bytes (FF.FpA.of_constant vk.s2.y) in
  append s2y ;

  let s3x = provable_bn254_base_field_to_bytes (FF.FpA.of_constant vk.s3.x) in
  append s3x ;

  let s3y = provable_bn254_base_field_to_bytes (FF.FpA.of_constant vk.s3.y) in
  append s3y ;

  let qlx = provable_bn254_base_field_to_bytes (FF.FpA.of_constant vk.ql.x) in
  append qlx ;

  let qly = provable_bn254_base_field_to_bytes (FF.FpA.of_constant vk.ql.y) in
  append qly ;

  let qrx = provable_bn254_base_field_to_bytes (FF.FpA.of_constant vk.qr.x) in
  append qrx ;

  let qry = provable_bn254_base_field_to_bytes (FF.FpA.of_constant vk.qr.y) in
  append qry ;

  let qmx = provable_bn254_base_field_to_bytes (FF.FpA.of_constant vk.qm.x) in
  append qmx ;

  let qmy = provable_bn254_base_field_to_bytes (FF.FpA.of_constant vk.qm.y) in
  append qmy ;

  let qox = provable_bn254_base_field_to_bytes (FF.FpA.of_constant vk.qo.x) in
  append qox ;

  let qoy = provable_bn254_base_field_to_bytes (FF.FpA.of_constant vk.qo.y) in
  append qoy ;

  let qkx = provable_bn254_base_field_to_bytes (FF.FpA.of_constant vk.qk.x) in
  append qkx ;

  let qky = provable_bn254_base_field_to_bytes (FF.FpA.of_constant vk.qk.y) in
  append qky ;

  let qcp_0 =
    match vk.qcp_0 with
    | Some pt ->
        pt
    | None ->
        failwith "squeeze_gamma: VK missing qcp_0"
  in
  let qcp_0_x =
    provable_bn254_base_field_to_bytes (FF.FpA.of_constant qcp_0.x)
  in
  append qcp_0_x ;

  let qcp_0_y =
    provable_bn254_base_field_to_bytes (FF.FpA.of_constant qcp_0.y)
  in
  append qcp_0_y ;

  (* two public inputs *)
  let pi0_bytes = provable_bn254_scalar_field_to_bytes pi0 in
  append pi0_bytes ;

  let pi1_bytes = provable_bn254_scalar_field_to_bytes pi1 in
  append pi1_bytes ;

  (* there is one gate, so we have just 1 [l, r, o] *)
  let lx = provable_bn254_base_field_to_bytes proof.l_com_x in
  append lx ;

  let ly = provable_bn254_base_field_to_bytes proof.l_com_y in
  append ly ;

  let rx = provable_bn254_base_field_to_bytes proof.r_com_x in
  append rx ;

  let ry = provable_bn254_base_field_to_bytes proof.r_com_y in
  append ry ;

  let ox = provable_bn254_base_field_to_bytes proof.o_com_x in
  append ox ;

  let oy = provable_bn254_base_field_to_bytes proof.o_com_y in
  append oy ;

  (* assert(cm_bytes.length === gammaSizeInBytes()) *)
  let bytes = Array.of_list !cm_bytes in
  let _h, digest = sha256_hash bytes in
  fs.gamma_digest <- digest ;
  fs.gamma <- Sha_to_fr.sha_to_fr digest

(** Squeeze beta challenge from gamma digest.
    Matches nori squeezeBeta (fiat-shamir/index.ts:299-310). *)
let squeeze_beta (fs : t) : unit =
  let beta_separator =
    FF.FpA.of_constant (Bignum_bigint.of_string "0x62657461")
  in
  let separator_bytes = provable_bn254_base_field_to_bytes beta_separator in

  (* beta is 32 bits and we cut the rest (256 - 32) bits which is 28 bytes *)
  let cm_bytes =
    ref (Array.sub separator_bytes ~pos:28 ~len:4 |> Array.to_list)
  in

  cm_bytes := !cm_bytes @ Array.to_list fs.gamma_digest ;
  (* assert(cm_bytes.length === sizeBetaBytes()) *)
  let bytes = Array.of_list !cm_bytes in
  let _h, digest = sha256_hash bytes in
  fs.beta_digest <- digest ;
  fs.beta <- Sha_to_fr.sha_to_fr digest

(** Squeeze alpha challenge from beta digest + proof commitments.
    Matches nori squeezeAlpha (fiat-shamir/index.ts:312-340). *)
let squeeze_alpha (fs : t) ~(proof : Plonk_accumulator.circuit_proof) : unit =
  let alpha_separator =
    FF.FpA.of_constant (Bignum_bigint.of_string "0x616c706861")
  in
  let separator_bytes = provable_bn254_base_field_to_bytes alpha_separator in

  (* alpha is 39 bits, so we leave only 40 bits (to keep it multiple of 8)
     and we cut the rest (256 - 40) bits which is 27 bytes *)
  let cm_bytes =
    ref (Array.sub separator_bytes ~pos:27 ~len:5 |> Array.to_list)
  in
  let append bs = cm_bytes := !cm_bytes @ Array.to_list bs in

  append (Array.to_list fs.beta_digest |> Array.of_list) ;

  let qcp_0_x = provable_bn254_base_field_to_bytes proof.qcp_0_wire_x in
  append qcp_0_x ;

  let qcp_0_y = provable_bn254_base_field_to_bytes proof.qcp_0_wire_y in
  append qcp_0_y ;

  let grand_product_x =
    provable_bn254_base_field_to_bytes proof.grand_product_x
  in
  append grand_product_x ;

  let grand_product_y =
    provable_bn254_base_field_to_bytes proof.grand_product_y
  in
  append grand_product_y ;

  let bytes = Array.of_list !cm_bytes in
  let _h, digest = sha256_hash bytes in
  fs.alpha_digest <- digest ;
  fs.alpha <- Sha_to_fr.sha_to_fr digest

(** Squeeze zeta challenge from alpha digest + proof commitments.
    Matches nori squeezeZeta (fiat-shamir/index.ts:342-372). *)
let squeeze_zeta (fs : t) ~(proof : Plonk_accumulator.circuit_proof) : unit =
  let zeta_separator =
    FF.FpA.of_constant (Bignum_bigint.of_string "0x7a657461")
  in
  let separator_bytes = provable_bn254_base_field_to_bytes zeta_separator in

  (* zeta is 31 bits, so we leave only 32 bits (to keep it multiple of 8)
     and we cut the rest (256 - 32) bits which is 28 bytes *)
  let cm_bytes =
    ref (Array.sub separator_bytes ~pos:28 ~len:4 |> Array.to_list)
  in
  let append bs = cm_bytes := !cm_bytes @ Array.to_list bs in

  append (Array.to_list fs.alpha_digest |> Array.of_list) ;

  let h0_x = provable_bn254_base_field_to_bytes proof.h0_x in
  append h0_x ;

  let h0_y = provable_bn254_base_field_to_bytes proof.h0_y in
  append h0_y ;

  let h1_x = provable_bn254_base_field_to_bytes proof.h1_x in
  append h1_x ;

  let h1_y = provable_bn254_base_field_to_bytes proof.h1_y in
  append h1_y ;

  let h2_x = provable_bn254_base_field_to_bytes proof.h2_x in
  append h2_x ;

  let h2_y = provable_bn254_base_field_to_bytes proof.h2_y in
  append h2_y ;

  let bytes = Array.of_list !cm_bytes in
  let _h, digest = sha256_hash bytes in
  fs.zeta_digest <- digest ;
  fs.zeta <- Sha_to_fr.sha_to_fr digest

(** Squeeze random challenge for KZG from commitments + zeta + gamma_kzg.
    Matches nori squeezeRandomForKzg (fiat-shamir/index.ts:438-466). *)
let squeeze_random_for_kzg (fs : t) ~(proof : Plonk_accumulator.circuit_proof)
    ~(cm_x : FF.FpA.t) ~(cm_y : FF.FpA.t) : FF.FpA.t =
  let cm_bytes =
    ref (Array.to_list (provable_bn254_base_field_to_bytes cm_x))
  in
  let append bs = cm_bytes := !cm_bytes @ Array.to_list bs in

  append (provable_bn254_base_field_to_bytes cm_y) ;

  append (provable_bn254_base_field_to_bytes proof.batch_opening_at_zeta_x) ;
  append (provable_bn254_base_field_to_bytes proof.batch_opening_at_zeta_y) ;

  append (provable_bn254_base_field_to_bytes proof.grand_product_x) ;
  append (provable_bn254_base_field_to_bytes proof.grand_product_y) ;

  append
    (provable_bn254_base_field_to_bytes proof.batch_opening_at_zeta_omega_x) ;
  append
    (provable_bn254_base_field_to_bytes proof.batch_opening_at_zeta_omega_y) ;

  append (provable_bn254_scalar_field_to_bytes fs.zeta) ;
  append (provable_bn254_scalar_field_to_bytes fs.gamma_kzg) ;

  let bytes = Array.of_list !cm_bytes in
  let _h, random_digest = sha256_hash bytes in
  Sha_to_fr.sha_to_fr random_digest

(** Partial SHA-256 for gamma_kzg: process first 11 blocks.
    Matches nori gammaKzgDigest_part0 (fiat-shamir/index.ts:470-545).
    Returns intermediate SHA-256 state (8 UInt32 words). *)
let gamma_kzg_digest_part0 (fs : t) ~(proof : Plonk_accumulator.circuit_proof)
    ~(vk : Plonk_proof.vk) ~(linearized_cm_x : FF.FpA.t)
    ~(linearized_cm_y : FF.FpA.t) ~(linearized_opening : FF.FpA.t) :
    Uint32.t array =
  let gamma_separator =
    FF.FpA.of_constant (Bignum_bigint.of_string "0x67616d6d61")
  in
  let separator_bytes = provable_bn254_base_field_to_bytes gamma_separator in

  (* gamma is 39 bits, so we leave only 40 bits (to keep it multiple of 8)
     and we cut the rest (256 - 40) bits which is 27 bytes *)
  let cm_bytes =
    ref (Array.sub separator_bytes ~pos:27 ~len:5 |> Array.to_list)
  in
  let append bs = cm_bytes := !cm_bytes @ Array.to_list bs in

  (* note that here they compute challenge from zeta_reduced and not unreduced as before *)
  append (provable_bn254_scalar_field_to_bytes fs.zeta) ;

  append (provable_bn254_base_field_to_bytes linearized_cm_x) ;
  append (provable_bn254_base_field_to_bytes linearized_cm_y) ;

  append (provable_bn254_base_field_to_bytes proof.l_com_x) ;
  append (provable_bn254_base_field_to_bytes proof.l_com_y) ;
  append (provable_bn254_base_field_to_bytes proof.r_com_x) ;
  append (provable_bn254_base_field_to_bytes proof.r_com_y) ;
  append (provable_bn254_base_field_to_bytes proof.o_com_x) ;
  append (provable_bn254_base_field_to_bytes proof.o_com_y) ;

  append (provable_bn254_base_field_to_bytes (FF.FpA.of_constant vk.s1.x)) ;
  append (provable_bn254_base_field_to_bytes (FF.FpA.of_constant vk.s1.y)) ;
  append (provable_bn254_base_field_to_bytes (FF.FpA.of_constant vk.s2.x)) ;
  append (provable_bn254_base_field_to_bytes (FF.FpA.of_constant vk.s2.y)) ;

  let qcp_0 =
    match vk.qcp_0 with
    | Some pt ->
        pt
    | None ->
        failwith "gamma_kzg_digest_part0: VK missing qcp_0"
  in
  append (provable_bn254_base_field_to_bytes (FF.FpA.of_constant qcp_0.x)) ;
  append (provable_bn254_base_field_to_bytes (FF.FpA.of_constant qcp_0.y)) ;

  append (provable_bn254_scalar_field_to_bytes linearized_opening) ;
  append (provable_bn254_scalar_field_to_bytes proof.l_at_zeta) ;
  append (provable_bn254_scalar_field_to_bytes proof.r_at_zeta) ;
  append (provable_bn254_scalar_field_to_bytes proof.o_at_zeta) ;
  append (provable_bn254_scalar_field_to_bytes proof.s1_at_zeta) ;
  append (provable_bn254_scalar_field_to_bytes proof.s2_at_zeta) ;
  (* qcp_0_at_zeta: only first 27 bytes *)
  let qcp_0_at_zeta_bytes =
    provable_bn254_scalar_field_to_bytes proof.qcp_0_at_zeta
  in
  append (Array.sub qcp_0_at_zeta_bytes ~pos:0 ~len:27) ;

  (* Convert bytes to UInt32 words (4 bytes each, little-endian reversed) *)
  let all_bytes = Array.of_list !cm_bytes in
  let n_words = Array.length all_bytes / 4 in
  let chunks =
    Array.init n_words ~f:(fun i ->
        Field_to_bytes.bytes_to_word (Array.sub all_bytes ~pos:(i * 4) ~len:4) )
  in

  (* Process first 11 blocks *)
  let h = ref (Sha256.initial_state ()) in
  for i = 0 to 10 do
    let message_block = Array.sub chunks ~pos:(16 * i) ~len:16 in
    let w = Sha256.message_schedule message_block in
    h := Sha256.compress !h w
  done ;
  !h

(** Partial SHA-256 for gamma_kzg: process final block.
    Matches nori gammaKzgDigest_part1 (fiat-shamir/index.ts:547-573). *)
let gamma_kzg_digest_part1 (fs : t) ~(proof : Plonk_accumulator.circuit_proof)
    ~(h_state : Uint32.t array) : unit =
  (* remaining bytes: qcp_0_at_zeta[27:32] + grand_product_at_omega_zeta *)
  let qcp_0_at_zeta_bytes =
    provable_bn254_scalar_field_to_bytes proof.qcp_0_at_zeta
  in
  let cm_bytes =
    ref (Array.sub qcp_0_at_zeta_bytes ~pos:27 ~len:5 |> Array.to_list)
  in
  let append bs = cm_bytes := !cm_bytes @ Array.to_list bs in

  append
    (provable_bn254_scalar_field_to_bytes proof.grand_product_at_omega_zeta) ;

  (* Append SHA-256 padding for total message of 741 bytes *)
  let total_msg_len = 741 in
  let bit_len = total_msg_len * 8 in
  let padded_len =
    let base = total_msg_len + 1 + 8 in
    let rem = base mod 64 in
    if rem = 0 then base else base + (64 - rem)
  in
  (* Only the padding portion after the 37 bytes in this block *)
  let current_bytes = List.length !cm_bytes in
  let pad_len = padded_len - (11 * 64) - current_bytes in
  let padding = Array.create ~len:pad_len Step.Field.zero in
  padding.(0) <- Step.Field.of_int 0x80 ;
  (* Length in bits as big-endian 8 bytes at end of padding *)
  let total_pad = current_bytes + pad_len in
  for i = 0 to 7 do
    let shift = 8 * (7 - i) in
    let byte_val = (bit_len lsr shift) land 0xff in
    padding.(total_pad - 8 + i - current_bytes) <- Step.Field.of_int byte_val
  done ;
  append padding ;

  (* Convert to words and process final block *)
  let all_bytes = Array.of_list !cm_bytes in
  let n_words = Array.length all_bytes / 4 in
  let chunks =
    Array.init n_words ~f:(fun i ->
        Field_to_bytes.bytes_to_word (Array.sub all_bytes ~pos:(i * 4) ~len:4) )
  in

  let message_block = chunks in
  let w = Sha256.message_schedule message_block in
  let h = Sha256.compress h_state w in

  (* Nori: wordToBytes(word, 4) witnesses 4 UInt8 in LE order,
     rangeCheck8 each, then bytesToWord(bytes).assertEquals(word).
     Digest = H.map(x => wordToBytes(x.value, 4).reverse()).flat(). *)
  let digest_bytes = Array.create ~len:32 Step.Field.zero in
  Array.iteri h ~f:(fun i word ->
      (* witness 4 bytes in LE order: b_le[0]=LSB .. b_le[3]=MSB *)
      let b_le =
        Array.init 4 ~f:(fun j ->
            Step.exists Step.Field.typ ~compute:(fun () ->
                let wv = Step.As_prover.read_var (Uint32.to_field word) in
                let w_big =
                  Bignum_bigint.of_string (Step.Field.Constant.to_string wv)
                in
                let shift = 8 * j in
                let byte_val =
                  Bignum_bigint.(bit_and (shift_right w_big shift) (of_int 255))
                in
                Step.Field.Constant.of_string (Bignum_bigint.to_string byte_val) ) )
      in
      (* rangeCheck8 each byte *)
      Array.iter b_le ~f:Uint32.range_check_8 ;
      (* bytesToWord(bytes).assertEquals(word) — LE reconstruction *)
      let reconstructed =
        Array.foldi b_le ~init:Step.Field.zero ~f:(fun j acc b ->
            let coeff = Step.Field.Constant.of_int (1 lsl (8 * j)) in
            Step.Field.add acc (Step.Field.scale b coeff) )
      in
      Step.assert_ (Equal (Uint32.to_field word, reconstructed)) ;
      (* Store as big-endian: reverse of LE *)
      digest_bytes.(i * 4) <- b_le.(3) ;
      digest_bytes.((i * 4) + 1) <- b_le.(2) ;
      digest_bytes.((i * 4) + 2) <- b_le.(1) ;
      digest_bytes.((i * 4) + 3) <- b_le.(0) ) ;
  fs.gamma_kzg_digest <- digest_bytes

(** Squeeze gamma_kzg from precomputed digest.
    Matches nori squeezeGammaKzgFromDigest (fiat-shamir/index.ts:575-577). *)
let squeeze_gamma_kzg_from_digest (fs : t) : unit =
  fs.gamma_kzg <- Sha_to_fr.sha_to_fr fs.gamma_kzg_digest

(** Create an empty Fiat-Shamir state (all zeros). *)
let empty () : t =
  { gamma_digest = Array.create ~len:32 Step.Field.zero
  ; gamma = FF.FpA.of_constant Bignum_bigint.zero
  ; beta_digest = Array.create ~len:32 Step.Field.zero
  ; beta = FF.FpA.of_constant Bignum_bigint.zero
  ; alpha_digest = Array.create ~len:32 Step.Field.zero
  ; alpha = FF.FpA.of_constant Bignum_bigint.zero
  ; zeta_digest = Array.create ~len:32 Step.Field.zero
  ; zeta = FF.FpA.of_constant Bignum_bigint.zero
  ; gamma_kzg_digest = Array.create ~len:32 Step.Field.zero
  ; gamma_kzg = FF.FpA.of_constant Bignum_bigint.zero
  }
