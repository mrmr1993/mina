(** Binary tree proof compression for Groth16.

    Reduces 16 individual proofs to a single proof:
      16 → 8 (layer1) → 4 → 2 → 1 (merge nodes)

    Layer1: verify two adjacent zkp proofs, assert hash continuity.
    Merge: verify two layer1/merge proofs, combine VK digests.

    For now, implements a simplified version that combines proofs
    without recursive verification (verification requires side-loaded
    VKs which need additional infrastructure). *)

open! Core_kernel
module Step = Pickles.Impls.Step

(** Layer1 circuit: takes two adjacent proof hashes and combines them.
    Input: [left_in_hash, left_out_hash, right_in_hash, right_out_hash]
    Output: [combined_hash]
    Asserts: left_out_hash = right_in_hash (continuity) *)
let layer1_body (pub : Step.Field.t array) : Step.Field.t array =
  let left_in = pub.(0) in
  let left_out = pub.(1) in
  let right_in = pub.(2) in
  let right_out = pub.(3) in
  (* Assert continuity: left output = right input *)
  Step.Field.Assert.equal left_out right_in ;
  (* Combine into a single hash *)
  let combined =
    Accumulator_hash.combine_hashes [ left_in; right_out; Step.Field.of_int 1 ]
  in
  [| combined |]

let layer1_rule : _ Pickles.Inductive_rule.Promise.t =
  { identifier = "layer1"
  ; prevs = []
  ; main =
      (fun { public_input = pub } ->
        Circuit_utils.dummy_constraints () ;
        let output = layer1_body pub in
        Promise.return
          { Pickles.Inductive_rule.previous_proof_statements = []
          ; public_output = output
          ; auxiliary_output = ()
          } )
  ; feature_flags = Pickles_types.Plonk_types.Features.none_bool
  }

(** Merge circuit: takes two subtree hashes and combines them.
    Input: [left_hash, right_hash, layer]
    Output: [combined_hash] *)
let merge_body (pub : Step.Field.t array) : Step.Field.t array =
  let left = pub.(0) in
  let right = pub.(1) in
  let layer = pub.(2) in
  let combined = Accumulator_hash.combine_hashes [ left; right; layer ] in
  [| combined |]

let merge_rule : _ Pickles.Inductive_rule.Promise.t =
  { identifier = "merge"
  ; prevs = []
  ; main =
      (fun { public_input = pub } ->
        Circuit_utils.dummy_constraints () ;
        let output = merge_body pub in
        Promise.return
          { Pickles.Inductive_rule.previous_proof_statements = []
          ; public_output = output
          ; auxiliary_output = ()
          } )
  ; feature_flags = Pickles_types.Plonk_types.Features.none_bool
  }

(** Compiled layer1 prover (lazily compiled on first use). *)
let layer1_prover =
  lazy
    (let _tag, _cache, (module Proof), provers =
       Pickles.compile_promise
         ~public_input:
           (Pickles.Inductive_rule.Input_and_output
              ( Circuit_utils.public_input_typ 4
              , Circuit_utils.public_input_typ 1 ) )
         ~auxiliary_typ:Step.Typ.unit
         ~max_proofs_verified:(module Pickles_types.Nat.N0)
         ~name:"groth16-layer1" ~o1js_compatible_mode:false
         ~choices:(fun ~self:_ -> [ layer1_rule ])
         ()
     in
     let Pickles.Provers.[ prove ] = provers in
     prove )

(** Compiled merge prover (lazily compiled on first use). *)
let merge_prover =
  lazy
    (let _tag, _cache, (module Proof), provers =
       Pickles.compile_promise
         ~public_input:
           (Pickles.Inductive_rule.Input_and_output
              ( Circuit_utils.public_input_typ 3
              , Circuit_utils.public_input_typ 1 ) )
         ~auxiliary_typ:Step.Typ.unit
         ~max_proofs_verified:(module Pickles_types.Nat.N0)
         ~name:"groth16-merge" ~o1js_compatible_mode:false
         ~choices:(fun ~self:_ -> [ merge_rule ])
         ()
     in
     let Pickles.Provers.[ prove ] = provers in
     prove )

(** Prove a layer1 node. *)
let prove_layer1 ~(left_in : Step.Field.Constant.t)
    ~(left_out : Step.Field.Constant.t) ~(right_in : Step.Field.Constant.t)
    ~(right_out : Step.Field.Constant.t) :
    Step.Field.Constant.t * Pickles_types.Nat.N0.n Pickles.Proof.t =
  let prove = Lazy.force layer1_prover in
  let output, _aux, proof =
    Promise.block_on_async_exn (fun () ->
        prove [| left_in; left_out; right_in; right_out |] )
  in
  (output.(0), proof)

(** Prove a merge node. *)
let prove_merge ~(left : Step.Field.Constant.t) ~(right : Step.Field.Constant.t)
    ~(layer : int) :
    Step.Field.Constant.t * Pickles_types.Nat.N0.n Pickles.Proof.t =
  ignore (layer : int) ;
  let prove = Lazy.force merge_prover in
  let output, _aux, proof =
    Promise.block_on_async_exn (fun () ->
        prove [| left; right; Step.Field.Constant.of_int layer |] )
  in
  (output.(0), proof)

(** Run the full compression tree on 16 circuit hash pairs.
    Returns the final combined hash and proof. *)
let compress
    ~(hash_pairs : (Step.Field.Constant.t * Step.Field.Constant.t) array) :
    Step.Field.Constant.t * Pickles_types.Nat.N0.n Pickles.Proof.t =
  assert (Array.length hash_pairs = 16) ;
  (* Layer 1: combine pairs *)
  let layer1_hashes =
    Array.init 8 ~f:(fun i ->
        let left_in, left_out = hash_pairs.(i * 2) in
        let right_in, right_out = hash_pairs.((i * 2) + 1) in
        fst (prove_layer1 ~left_in ~left_out ~right_in ~right_out) )
  in
  (* Layer 2-4: merge pairs *)
  let current = ref layer1_hashes in
  for layer = 2 to 4 do
    let n = Array.length !current in
    current :=
      Array.init (n / 2) ~f:(fun i ->
          fst
            (prove_merge
               ~left:!current.(i * 2)
               ~right:!current.((i * 2) + 1)
               ~layer ) )
  done ;
  let final_hash = !current.(0) in
  let _, proof = prove_merge ~left:final_hash ~right:final_hash ~layer:5 in
  (final_hash, proof)
