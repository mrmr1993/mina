(** ArrayListHasher: Poseidon hash of a fixed-size array of Fields with
    selective opening of Fp12 chunks.

    Used to verify g_digest: the accumulator commits to a 65-element array
    of line evaluation hashes. Each circuit opens a window of that array
    by providing the actual Fp12 values and verifying the recomputed hash
    matches the committed g_digest.

    Matches nori's array_list_hasher.ts. *)

open! Core_kernel
module Step = Pickles.Impls.Step

(** Fixed array size = ATE_LOOP_COUNT length. *)
let n = Array.length Bn254_params.ate_loop_count

(** Hash a fixed-size array of n Fields using Poseidon.
    Matches nori's ArrayListHasher.hash(arr). *)
let hash (arr : Step.Field.t array) : Step.Field.t =
  assert (Array.length arr = n) ;
  Accumulator_hash.poseidon_hash arr

(** Open a window in the committed array by providing:
    - lhs: already-committed hashes before the opening
    - opening: Fp12 values to be hashed into Fields
    - rhs: already-committed hashes after the opening

    Returns the hash of [lhs; map hash_fp12 opening; rhs].
    The caller asserts this equals acc.state.g_digest. *)
let _alh_marker (x : int) =
  Step.assert_
    (Raw
       { kind = Zero
       ; values = [||]
       ; coeffs =
           Array.map ~f:Step.Field.Constant.of_int [| x; 1; 2; 3; 4; 5; 6 |]
       } )

let open_ ~(lhs : Step.Field.t array) ~(opening : Fp12.Circuit.t array)
    ~(rhs : Step.Field.t array) : Step.Field.t =
  _alh_marker 7000 ;
  let opening_hashes = Array.map opening ~f:Accumulator_hash.hash_fp12 in
  _alh_marker 7001 ;
  let combined = Array.concat [ lhs; opening_hashes; rhs ] in
  assert (Array.length combined = n) ;
  let result = hash combined in
  _alh_marker 7002 ; result
