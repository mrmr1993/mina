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
        Field_to_bytes.bytes_to_word
          (Array.sub padded ~pos:(i * 4) ~len:4) )
  in
  (* Split into 16-word blocks *)
  let n_blocks = n_words / 16 in
  Array.init n_blocks ~f:(fun i ->
      Array.sub words ~pos:(i * 16) ~len:16 )

(** SHA-256 hash of a byte array (handles padding).
    Returns 8 UInt32 words and a Bytes32 digest. *)
let sha256_hash (bytes : Field_to_bytes.byte array) :
    Uint32.t array * Plonk_accumulator.bytes32 =
  let blocks = sha256_pad_and_block bytes in
  let h = Sha256.hash_blocks blocks in
  (* Convert 8 UInt32 words to 32 bytes (for digest storage).
     Each word → 4 big-endian bytes via wordToBytes.
     Matches nori: H.map(x => wordToBytes(x.value, 4).reverse()).flat() *)
  let digest_bytes =
    Array.concat_map h ~f:(fun word ->
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
  (* Constrain byte decomposition *)
  Array.iteri h ~f:(fun i word ->
      let b = Array.sub digest_bytes ~pos:(i * 4) ~len:4 in
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
  (h, digest_bytes)

(** Convert a FpC (base field constant) to 32 bytes.
    VK fields are constants, so this produces constant bytes. *)
let fp_const_to_bytes (v : Bignum_bigint.t) : Field_to_bytes.byte array =
  let f3 = FF.Field3.of_constant v in
  Field_to_bytes.field3_to_bytes f3 ~size_in_bits:254

(** Convert an FpA (in-circuit base field) to 32 bytes. *)
let fpa_to_bytes (x : FF.FpA.t) : Field_to_bytes.byte array =
  Field_to_bytes.fp_to_bytes x

(** Convert an FrC/FrA (in-circuit scalar field) to 32 bytes.
    FrC and FpC use the same representation (3 limbs). *)
let fra_to_bytes (x : FF.FpA.t) : Field_to_bytes.byte array =
  Field_to_bytes.fr_to_bytes x

(** Squeeze gamma challenge from proof + VK + public inputs.
    Matches nori squeezeGamma (fiat-shamir/index.ts:206-297). *)
let squeeze_gamma (fs : t) ~(proof : Plonk_accumulator.circuit_proof)
    ~(pi0 : FF.FpA.t) ~(pi1 : FF.FpA.t)
    ~(vk : Plonk_proof.vk) : unit =
  (* gamma separator = 0x67616d6d61 = "gamma" in ASCII *)
  let separator_bytes = fp_const_to_bytes
    (Bignum_bigint.of_string "0x67616d6d61") in
  (* Slice last 5 bytes (gamma is 39 bits → 40 bits → 5 bytes) *)
  let cm_bytes = Queue.create () in
  for i = 27 to 31 do
    Queue.enqueue cm_bytes separator_bytes.(i)
  done ;
  (* VK permutation polynomials: s1, s2, s3 *)
  let add_g1_const (pt : G1.Constant.t) =
    let xb = fp_const_to_bytes pt.x in
    let yb = fp_const_to_bytes pt.y in
    Array.iter xb ~f:(Queue.enqueue cm_bytes) ;
    Array.iter yb ~f:(Queue.enqueue cm_bytes)
  in
  add_g1_const vk.s1 ;
  add_g1_const vk.s2 ;
  add_g1_const vk.s3 ;
  (* VK selector polynomials: ql, qr, qm, qo, qk, qcp_0 *)
  add_g1_const vk.ql ;
  add_g1_const vk.qr ;
  add_g1_const vk.qm ;
  add_g1_const vk.qo ;
  add_g1_const vk.qk ;
  ( match vk.qcp_0 with
  | Some pt -> add_g1_const pt
  | None -> failwith "squeeze_gamma: VK missing qcp_0" ) ;
  (* Two public inputs (scalar field) *)
  let add_fra (x : FF.FpA.t) =
    Array.iter (fra_to_bytes x) ~f:(Queue.enqueue cm_bytes)
  in
  add_fra pi0 ;
  add_fra pi1 ;
  (* Proof wire commitments: l, r, o *)
  let add_fpa (x : FF.FpA.t) =
    Array.iter (fpa_to_bytes x) ~f:(Queue.enqueue cm_bytes)
  in
  add_fpa proof.l_com_x ;
  add_fpa proof.l_com_y ;
  add_fpa proof.r_com_x ;
  add_fpa proof.r_com_y ;
  add_fpa proof.o_com_x ;
  add_fpa proof.o_com_y ;
  (* SHA-256 hash *)
  let bytes = Queue.to_array cm_bytes in
  let _h, digest = sha256_hash bytes in
  fs.gamma_digest <- digest ;
  fs.gamma <- Sha_to_fr.sha_to_fr _h

(** Squeeze beta challenge from gamma digest.
    Matches nori squeezeBeta (fiat-shamir/index.ts:299-310). *)
let squeeze_beta (fs : t) : unit =
  (* beta separator = 0x62657461 = "beta" in ASCII *)
  let separator_bytes = fp_const_to_bytes
    (Bignum_bigint.of_string "0x62657461") in
  (* Slice last 4 bytes (beta is 32 bits) *)
  let cm_bytes = Queue.create () in
  for i = 28 to 31 do
    Queue.enqueue cm_bytes separator_bytes.(i)
  done ;
  (* Append gamma digest bytes *)
  Array.iter fs.gamma_digest ~f:(Queue.enqueue cm_bytes) ;
  (* SHA-256 hash *)
  let bytes = Queue.to_array cm_bytes in
  let _h, digest = sha256_hash bytes in
  fs.beta_digest <- digest ;
  fs.beta <- Sha_to_fr.sha_to_fr _h

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
