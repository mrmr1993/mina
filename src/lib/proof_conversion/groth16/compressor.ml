(** Binary tree proof compression for Groth16.

    Reduces 16 individual proofs to a single proof via recursive
    binary compression:
      16 → 8 (layer1) → 4 → 2 → 1 (merge nodes)

    Layer1 nodes verify two adjacent zkp proofs and assert
    accumulator continuity (left output = right input).

    Merge nodes verify two layer1/merge proofs and combine
    their subtree VK digests.

    Reference: nori-proof-conversion/src/compressor/ *)

module Step = Pickles.Impls.Step

(** Subtree carry: the data passed up through the compression tree.
    Contains the leftmost input hash, rightmost output hash, and
    a Poseidon digest of the subtree's verification keys. *)
module SubtreeCarry = struct
  type t =
    { left_in : Step.Field.t
    ; right_out : Step.Field.t
    ; subtree_vk_digest : Step.Field.t
    }
end

(** Layer1 rule: verify two zkp proofs from adjacent circuits.
    Asserts that left_proof.output = right_proof.input (continuity).
    Computes subtree_vk_digest = Poseidon(left_vk_hash, right_vk_hash, 1). *)
let _layer1_rule : _ Pickles.Inductive_rule.Promise.t =
  { identifier = "layer1"
  ; prevs = []  (* TODO: should verify two N0 proofs via side-loading *)
  ; main =
      (fun { public_input = _pub } ->
        Circuit_utils.dummy_constraints () ;
        (* TODO: verify two proofs, assert continuity, combine VK hashes *)
        Promise.return
          { Pickles.Inductive_rule.previous_proof_statements = []
          ; public_output = [||]
          ; auxiliary_output = ()
          } )
  ; feature_flags = Pickles_types.Plonk_types.Features.none_bool
  }

(** Merge rule: verify two layer1/merge proofs.
    Asserts left.right_out = right.left_in (continuity).
    Computes new subtree_vk_digest combining both subtrees. *)
let _merge_rule : _ Pickles.Inductive_rule.Promise.t =
  { identifier = "merge"
  ; prevs = []  (* TODO: should verify two N2 proofs *)
  ; main =
      (fun { public_input = _pub } ->
        Circuit_utils.dummy_constraints () ;
        (* TODO: verify two proofs, assert continuity *)
        Promise.return
          { Pickles.Inductive_rule.previous_proof_statements = []
          ; public_output = [||]
          ; auxiliary_output = ()
          } )
  ; feature_flags = Pickles_types.Plonk_types.Features.none_bool
  }

(** Run the full compression tree.
    Takes 16 proofs and reduces to 1. *)
let compress ~(_proofs : unit array) : unit =
  Printf.printf "Compression tree: 16 -> 8 -> 4 -> 2 -> 1\n%!" ;
  Printf.printf "  Layer 1: 8 nodes (pairs of adjacent zkp proofs)\n%!" ;
  Printf.printf "  Layer 2: 4 merge nodes\n%!" ;
  Printf.printf "  Layer 3: 2 merge nodes\n%!" ;
  Printf.printf "  Layer 4: 1 merge node (final proof)\n%!" ;
  failwith "Compression tree not yet implemented"
