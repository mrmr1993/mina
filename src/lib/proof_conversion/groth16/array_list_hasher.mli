(** Poseidon hash of a fixed-size array of Fields with selective opening
    of Fp12 chunks.

    Used to verify [g_digest]: the accumulator commits to a fixed-size
    array of line-evaluation hashes; each circuit opens a window of that
    array and verifies the recomputed hash matches the committed digest. *)

open Proof_conversion_bn254
module Step = Pickles.Impls.Step

(** Fixed array size (= [ate_loop_count] length). *)
val n : int

(** Hash a fixed-size array of [n] Fields using Poseidon. *)
val hash : Step.Field.t array -> Step.Field.t

(** Open a window in the committed array: hashes
    [[lhs; map hash_fp12 opening; rhs]]. The caller asserts the result
    equals [acc.state.g_digest]. *)
val open_ :
     lhs:Step.Field.t array
  -> opening:Fp12.Circuit.t array
  -> rhs:Step.Field.t array
  -> Step.Field.t
