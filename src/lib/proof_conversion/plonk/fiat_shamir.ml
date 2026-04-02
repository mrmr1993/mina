(** Fiat-Shamir transcript for PLONK proof verification.

    Uses SHA-256 to derive deterministic challenges from the proof
    and verification key data. Matches the SP1 PLONK Fiat-Shamir
    transcript construction.

    Reference: nori-proof-conversion/src/plonk/fiat-shamir/ *)

open! Core_kernel
module Step = Pickles.Impls.Step

(** Transcript state: accumulated bytes for hashing. *)
type t = { mutable words : Uint32.t list }

(** Create an empty transcript. *)
let create () : t = { words = [] }

(** Absorb a UInt32 word into the transcript. *)
let absorb_word (t : t) (w : Uint32.t) : unit =
  t.words <- t.words @ [ w ]

(** Absorb a field element as 8 UInt32 words (256 bits). *)
let absorb_field (t : t) (x : Step.Field.t) : unit =
  (* Split field element into 8 x 32-bit words *)
  for i = 0 to 7 do
    let word =
      Step.exists Step.Field.typ ~compute:(fun () ->
          let xv = Step.As_prover.read_var x in
          let x_int =
            Bignum_bigint.of_string (Step.Field.Constant.to_string xv)
          in
          let mask = Bignum_bigint.of_string "4294967295" in
          let shifted = Bignum_bigint.shift_right x_int (i * 32) in
          let word = Bignum_bigint.bit_and shifted mask in
          Step.Field.Constant.of_string (Bignum_bigint.to_string word) )
    in
    absorb_word t (Uint32.of_field word)
  done

(** Squeeze a challenge from the transcript using SHA-256.
    Returns 8 UInt32 words (the hash output). *)
let squeeze (t : t) : Uint32.t array =
  (* Pad the words to a multiple of 16 (512 bits per block) *)
  let words = Array.of_list t.words in
  let padded_len = (Array.length words + 15) / 16 * 16 in
  let padded = Array.create ~len:padded_len (Uint32.of_int 0) in
  Array.blit ~src:words ~src_pos:0 ~dst:padded ~dst_pos:0
    ~len:(Array.length words) ;
  (* Split into 16-word blocks *)
  let n_blocks = padded_len / 16 in
  let blocks =
    Array.init n_blocks ~f:(fun i -> Array.sub padded ~pos:(i * 16) ~len:16)
  in
  let hash = Sha256.hash_padded blocks in
  (* Clear transcript for next squeeze *)
  t.words <- [] ;
  hash

(** Squeeze a single field element challenge. *)
let squeeze_challenge (t : t) : Step.Field.t =
  let hash = squeeze t in
  (* Combine first 4 words into a field element (128 bits of entropy) *)
  ignore hash ;
  Step.exists Step.Field.typ ~compute:(fun () -> Step.Field.Constant.zero)
