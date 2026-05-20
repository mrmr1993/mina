(** Binary-tree proof compression for Groth16.

    Reduces 16 individual proofs to a single proof via layer1 and merge
    nodes. *)

module Step = Pickles.Impls.Step

(** Layer1 circuit body: combine two adjacent proof hashes, asserting
    [left_out = right_in]. *)
val layer1_body : Step.Field.t array -> Step.Field.t array

(** Merge circuit body: combine two subtree hashes. *)
val merge_body : Step.Field.t array -> Step.Field.t array

(** Prove a layer1 node. *)
val prove_layer1 :
     left_in:Step.Field.Constant.t
  -> left_out:Step.Field.Constant.t
  -> right_in:Step.Field.Constant.t
  -> right_out:Step.Field.Constant.t
  -> Step.Field.Constant.t * Pickles_types.Nat.N0.n Pickles.Proof.t

(** Prove a merge node. *)
val prove_merge :
     left:Step.Field.Constant.t
  -> right:Step.Field.Constant.t
  -> layer:int
  -> Step.Field.Constant.t * Pickles_types.Nat.N0.n Pickles.Proof.t

(** Run the full compression tree on 16 circuit hash pairs. *)
val compress :
     hash_pairs:(Step.Field.Constant.t * Step.Field.Constant.t) array
  -> Step.Field.Constant.t * Pickles_types.Nat.N0.n Pickles.Proof.t
