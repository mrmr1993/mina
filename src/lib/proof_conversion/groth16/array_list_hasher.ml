(** ArrayListHasher: Poseidon hash of a fixed-size array of Fields with
    selective opening of Fp12 chunks.

    Used to verify g_digest: the accumulator commits to a 65-element array
    of line evaluation hashes. Each circuit opens a window of that array
    by providing the actual Fp12 values and verifying the recomputed hash
    matches the committed g_digest.

*)

open! Core_kernel
open Proof_conversion_bn254
module Step = Pickles.Impls.Step

(** Fixed array size = ATE_LOOP_COUNT length. *)
let n = Array.length Bn254_params.ate_loop_count

(** Hash a fixed-size array of n Fields using Poseidon. *)
let hash (arr : Step.Field.t array) : Step.Field.t =
  assert (Array.length arr = n) ;
  Accumulator_hash.poseidon_hash arr

(** Open a window in the committed array by providing:
    - lhs: already-committed hashes before the opening
    - opening: Fp12 values to be hashed into Fields
    - rhs: already-committed hashes after the opening

    Returns the hash of [lhs; map hash_fp12 opening; rhs].
    The caller asserts this equals acc.state.g_digest. *)
let open_ ~(lhs : Step.Field.t array) ~(opening : Fp12.Circuit.t array)
    ~(rhs : Step.Field.t array) : Step.Field.t =
  let opening_hashes = Array.map opening ~f:Accumulator_hash.hash_fp12 in
  let combined = Array.concat [ lhs; opening_hashes; rhs ] in
  assert (Array.length combined = n) ;
  hash combined
