(** Binary tree proof compression matching nori's layer1/node circuits.

    Layer1: Verify two base-layer proofs (zkp0-23) with conditional
    verification (verifyIf pattern). Produces SubtreeCarry.

    Node: Verify two node proofs unconditionally. Builds hierarchical
    VK digest. Produces SubtreeCarry.

    Reference:
      nori-proof-conversion/src/compressor/layer1node.ts
      nori-proof-conversion/src/compressor/compressor.ts
      nori-proof-conversion/src/structs.ts *)

open! Core_kernel
open Proof_conversion_circuit_kit
module Step = Pickles.Impls.Step

(** NOTHING_UP_MY_SLEEVE = Field(0), used for dummy VK hashes. *)
let nothing_up_my_sleeve = Step.Field.zero

(** SubtreeCarry: the public output of merge circuits.
    Uses left-associated pair to match Typ.( * ) nesting. *)
type subtree_carry_var = (Step.Field.t * Step.Field.t) * Step.Field.t

type subtree_carry_const =
  (Step.Field.Constant.t * Step.Field.Constant.t) * Step.Field.Constant.t

let subtree_carry_typ : (subtree_carry_var, subtree_carry_const) Step.Typ.t =
  Step.Typ.(Step.Field.typ * Step.Field.typ * Step.Field.typ)

(** Side-loaded tag for base-layer (zkp) proofs.
    These have public_input:Field, public_output:Field, maxProofsVerified=0. *)
let zkp_side_loaded_tag_left =
  Pickles.Side_loaded.create ~name:"zkp_left"
    ~max_proofs_verified:(module Pickles_types.Nat.N2)
    ~feature_flags:Pickles_types.Plonk_types.Features.maybe
    ~typ:Step.Typ.(Step.Field.typ * Step.Field.typ)

let zkp_side_loaded_tag_right =
  Pickles.Side_loaded.create ~name:"zkp_right"
    ~max_proofs_verified:(module Pickles_types.Nat.N2)
    ~feature_flags:Pickles_types.Plonk_types.Features.maybe
    ~typ:Step.Typ.(Step.Field.typ * Step.Field.typ)

(** Request types for layer1 circuit private inputs. *)
type _ Snarky_backendless.Request.t +=
  | Layer1_proof_left : Pickles.Side_loaded.Proof.t Snarky_backendless.Request.t
  | Layer1_vk_left :
      Pickles.Side_loaded.Verification_key.t Snarky_backendless.Request.t
  | Layer1_verify_left : bool Snarky_backendless.Request.t
  | Layer1_proof_right :
      Pickles.Side_loaded.Proof.t Snarky_backendless.Request.t
  | Layer1_vk_right :
      Pickles.Side_loaded.Verification_key.t Snarky_backendless.Request.t
  | Layer1_verify_right : bool Snarky_backendless.Request.t
  | Layer1_pi_left :
      (Step.Field.Constant.t * Step.Field.Constant.t)
      Snarky_backendless.Request.t
  | Layer1_pi_right :
      (Step.Field.Constant.t * Step.Field.Constant.t)
      Snarky_backendless.Request.t

(** Layer1 rule: verify two base-layer proofs with conditional verification.
    Matches nori layer1node.ts. *)
let layer1_rule : _ Pickles.Inductive_rule.Promise.t =
  { identifier = "layer1"
  ; prevs = [ zkp_side_loaded_tag_left; zkp_side_loaded_tag_right ]
  ; feature_flags = Pickles_types.Plonk_types.Features.none_bool
  ; main =
      (fun { public_input = () } ->
        Circuit_utils.dummy_constraints () ;
        (* Witness proofs, VKs, and verify flags *)
        let proof_left =
          Step.exists (Step.Typ.prover_value ()) ~request:(fun () ->
              Layer1_proof_left )
        in
        let vk_left_pv =
          Step.exists (Step.Typ.prover_value ()) ~request:(fun () ->
              Layer1_vk_left )
        in
        let verify_left =
          Step.exists Step.Boolean.typ ~request:(fun () -> Layer1_verify_left)
        in
        let proof_right =
          Step.exists (Step.Typ.prover_value ()) ~request:(fun () ->
              Layer1_proof_right )
        in
        let vk_right_pv =
          Step.exists (Step.Typ.prover_value ()) ~request:(fun () ->
              Layer1_vk_right )
        in
        let verify_right =
          Step.exists Step.Boolean.typ ~request:(fun () -> Layer1_verify_right)
        in
        (* Witness public inputs/outputs for the sub-proofs *)
        let pi_left_in, pi_left_out =
          let pi =
            Step.exists (Step.Typ.tuple2 Step.Field.typ Step.Field.typ)
              ~request:(fun () -> Layer1_pi_left)
          in
          pi
        in
        let pi_right_in, pi_right_out =
          let pi =
            Step.exists (Step.Typ.tuple2 Step.Field.typ Step.Field.typ)
              ~request:(fun () -> Layer1_pi_right)
          in
          pi
        in
        (* Register VKs in prover and circuit *)
        Step.as_prover (fun () ->
            let vk_l =
              Step.As_prover.read (Step.Typ.prover_value ()) vk_left_pv
            in
            Pickles.Side_loaded.in_prover zkp_side_loaded_tag_left vk_l ;
            let vk_r =
              Step.As_prover.read (Step.Typ.prover_value ()) vk_right_pv
            in
            Pickles.Side_loaded.in_prover zkp_side_loaded_tag_right vk_r ) ;
        let vk_left =
          Step.exists Pickles.Side_loaded.Verification_key.typ
            ~compute:(fun () ->
              Step.As_prover.read (Step.Typ.prover_value ()) vk_left_pv )
        in
        Pickles.Side_loaded.in_circuit zkp_side_loaded_tag_left vk_left ;
        let vk_right =
          Step.exists Pickles.Side_loaded.Verification_key.typ
            ~compute:(fun () ->
              Step.As_prover.read (Step.Typ.prover_value ()) vk_right_pv )
        in
        Pickles.Side_loaded.in_circuit zkp_side_loaded_tag_right vk_right ;
        (* Assert continuity: left output = right input *)
        Step.Field.Assert.equal pi_left_out pi_right_in ;
        (* VK hash: use NOTHING_UP_MY_SLEEVE for unverified proofs *)
        let vk_hash_left =
          let real_hash =
            Pickles.Side_loaded.Verification_key.Checked.to_input vk_left
            |> Random_oracle.Checked.pack_input |> Random_oracle.Checked.hash
          in
          Step.Field.if_ verify_left ~then_:real_hash
            ~else_:nothing_up_my_sleeve
        in
        let vk_hash_right =
          let real_hash =
            Pickles.Side_loaded.Verification_key.Checked.to_input vk_right
            |> Random_oracle.Checked.pack_input |> Random_oracle.Checked.hash
          in
          Step.Field.if_ verify_right ~then_:real_hash
            ~else_:nothing_up_my_sleeve
        in
        (* SubtreeVkDigest = Poseidon.hash([vkHashLeft, vkHashRight, 1]) *)
        let subtree_vk_digest =
          Random_oracle.Checked.hash
            [| vk_hash_left; vk_hash_right; Step.Field.of_int 1 |]
        in
        let output : subtree_carry_var =
          ((pi_left_in, pi_right_out), subtree_vk_digest)
        in
        Promise.return
          { Pickles.Inductive_rule.previous_proof_statements =
              [ { public_input = (pi_left_in, pi_left_out)
                ; proof = proof_left
                ; proof_must_verify = verify_left
                }
              ; { public_input = (pi_right_in, pi_right_out)
                ; proof = proof_right
                ; proof_must_verify = verify_right
                }
              ]
          ; public_output = output
          ; auxiliary_output = ()
          } )
  }

(** Side-loaded tags for node proofs (layers 2+).
    These have public_input:Undefined, public_output:SubtreeCarry,
    maxProofsVerified=2. *)
let node_side_loaded_tag_left =
  Pickles.Side_loaded.create ~name:"node_left"
    ~max_proofs_verified:(module Pickles_types.Nat.N2)
    ~feature_flags:Pickles_types.Plonk_types.Features.maybe
    ~typ:subtree_carry_typ

let node_side_loaded_tag_right =
  Pickles.Side_loaded.create ~name:"node_right"
    ~max_proofs_verified:(module Pickles_types.Nat.N2)
    ~feature_flags:Pickles_types.Plonk_types.Features.maybe
    ~typ:subtree_carry_typ

(** Request types for node circuit private inputs. *)
type _ Snarky_backendless.Request.t +=
  | Node_proof_left : Pickles.Side_loaded.Proof.t Snarky_backendless.Request.t
  | Node_vk_left :
      Pickles.Side_loaded.Verification_key.t Snarky_backendless.Request.t
  | Node_proof_right : Pickles.Side_loaded.Proof.t Snarky_backendless.Request.t
  | Node_vk_right :
      Pickles.Side_loaded.Verification_key.t Snarky_backendless.Request.t
  | Node_layer : int Snarky_backendless.Request.t
  | Node_carry_left : subtree_carry_const Snarky_backendless.Request.t
  | Node_carry_right : subtree_carry_const Snarky_backendless.Request.t

(** Node rule: verify two node proofs unconditionally.
    Matches nori compressor.ts. *)
let node_rule : _ Pickles.Inductive_rule.Promise.t =
  { identifier = "node"
  ; prevs = [ node_side_loaded_tag_left; node_side_loaded_tag_right ]
  ; feature_flags = Pickles_types.Plonk_types.Features.none_bool
  ; main =
      (fun { public_input = () } ->
        Circuit_utils.dummy_constraints () ;
        let proof_left =
          Step.exists (Step.Typ.prover_value ()) ~request:(fun () ->
              Node_proof_left )
        in
        let vk_left_pv =
          Step.exists (Step.Typ.prover_value ()) ~request:(fun () ->
              Node_vk_left )
        in
        let proof_right =
          Step.exists (Step.Typ.prover_value ()) ~request:(fun () ->
              Node_proof_right )
        in
        let vk_right_pv =
          Step.exists (Step.Typ.prover_value ()) ~request:(fun () ->
              Node_vk_right )
        in
        let layer_pv =
          Step.exists (Step.Typ.prover_value ()) ~request:(fun () ->
              Node_layer )
        in
        let layer =
          Step.exists Step.Field.typ ~compute:(fun () ->
              Step.Field.Constant.of_int
                (Step.As_prover.read (Step.Typ.prover_value ()) layer_pv) )
        in
        (* Witness the SubtreeCarry values from the sub-proofs *)
        let carry_left =
          Step.exists subtree_carry_typ ~request:(fun () -> Node_carry_left)
        in
        let carry_right =
          Step.exists subtree_carry_typ ~request:(fun () -> Node_carry_right)
        in
        let (left_in_l, right_out_l), subtree_digest_l = carry_left in
        let (left_in_r, right_out_r), subtree_digest_r = carry_right in
        (* Register VKs *)
        Step.as_prover (fun () ->
            let vk_l =
              Step.As_prover.read (Step.Typ.prover_value ()) vk_left_pv
            in
            Pickles.Side_loaded.in_prover node_side_loaded_tag_left vk_l ;
            let vk_r =
              Step.As_prover.read (Step.Typ.prover_value ()) vk_right_pv
            in
            Pickles.Side_loaded.in_prover node_side_loaded_tag_right vk_r ) ;
        let vk_left =
          Step.exists Pickles.Side_loaded.Verification_key.typ
            ~compute:(fun () ->
              Step.As_prover.read (Step.Typ.prover_value ()) vk_left_pv )
        in
        Pickles.Side_loaded.in_circuit node_side_loaded_tag_left vk_left ;
        let vk_right =
          Step.exists Pickles.Side_loaded.Verification_key.typ
            ~compute:(fun () ->
              Step.As_prover.read (Step.Typ.prover_value ()) vk_right_pv )
        in
        Pickles.Side_loaded.in_circuit node_side_loaded_tag_right vk_right ;
        (* Assert continuity: left.rightOut == right.leftIn *)
        Step.Field.Assert.equal right_out_l left_in_r ;
        (* Compute VK hashes *)
        let vk_hash_left =
          Pickles.Side_loaded.Verification_key.Checked.to_input vk_left
          |> Random_oracle.Checked.pack_input |> Random_oracle.Checked.hash
        in
        let vk_hash_right =
          Pickles.Side_loaded.Verification_key.Checked.to_input vk_right
          |> Random_oracle.Checked.pack_input |> Random_oracle.Checked.hash
        in
        (* SubtreeVkDigest = Poseidon.hash([vkL.hash, vkR.hash, leftDigest, rightDigest, layer]) *)
        let subtree_vk_digest =
          Random_oracle.Checked.hash
            [| vk_hash_left
             ; vk_hash_right
             ; subtree_digest_l
             ; subtree_digest_r
             ; layer
            |]
        in
        let output : subtree_carry_var =
          ((left_in_l, right_out_r), subtree_vk_digest)
        in
        Promise.return
          { Pickles.Inductive_rule.previous_proof_statements =
              [ { public_input = carry_left
                ; proof = proof_left
                ; proof_must_verify = Step.Boolean.true_
                }
              ; { public_input = carry_right
                ; proof = proof_right
                ; proof_must_verify = Step.Boolean.true_
                }
              ]
          ; public_output = output
          ; auxiliary_output = ()
          } )
  }

(** Witness data for a layer1 merge. *)
type layer1_witness =
  { proof_left : Pickles.Side_loaded.Proof.t
  ; vk_left : Pickles.Side_loaded.Verification_key.t
  ; verify_left : bool
  ; proof_right : Pickles.Side_loaded.Proof.t
  ; vk_right : Pickles.Side_loaded.Verification_key.t
  ; verify_right : bool
  ; pi_left : Step.Field.Constant.t * Step.Field.Constant.t
  ; pi_right : Step.Field.Constant.t * Step.Field.Constant.t
  }

(** Handler for layer1 circuit requests. *)
let layer1_handler (w : layer1_witness) :
    Snarky_backendless.Request.request -> Snarky_backendless.Request.response =
 fun (With { request; respond }) ->
  match request with
  | Layer1_proof_left ->
      respond (Provide w.proof_left)
  | Layer1_vk_left ->
      respond (Provide w.vk_left)
  | Layer1_verify_left ->
      respond (Provide w.verify_left)
  | Layer1_proof_right ->
      respond (Provide w.proof_right)
  | Layer1_vk_right ->
      respond (Provide w.vk_right)
  | Layer1_verify_right ->
      respond (Provide w.verify_right)
  | Layer1_pi_left ->
      respond (Provide w.pi_left)
  | Layer1_pi_right ->
      respond (Provide w.pi_right)
  | _ ->
      respond Unhandled

(** Witness data for a node merge. *)
type node_witness =
  { proof_left : Pickles.Side_loaded.Proof.t
  ; vk_left : Pickles.Side_loaded.Verification_key.t
  ; proof_right : Pickles.Side_loaded.Proof.t
  ; vk_right : Pickles.Side_loaded.Verification_key.t
  ; layer : int
  ; carry_left : subtree_carry_const
  ; carry_right : subtree_carry_const
  }

(** Handler for node circuit requests. *)
let node_handler (w : node_witness) :
    Snarky_backendless.Request.request -> Snarky_backendless.Request.response =
 fun (With { request; respond }) ->
  match request with
  | Node_proof_left ->
      respond (Provide w.proof_left)
  | Node_vk_left ->
      respond (Provide w.vk_left)
  | Node_proof_right ->
      respond (Provide w.proof_right)
  | Node_vk_right ->
      respond (Provide w.vk_right)
  | Node_layer ->
      respond (Provide w.layer)
  | Node_carry_left ->
      respond (Provide w.carry_left)
  | Node_carry_right ->
      respond (Provide w.carry_right)
  | _ ->
      respond Unhandled

(** Compile the layer1 circuit.
    Returns (tag, Proof module, prover). *)
let compile_layer1 () =
  let tag, _cache, (module Proof), provers =
    Pickles.compile_promise
      ~cache:(Cache_config.get_cache ())
      ~public_input:
        (Pickles.Inductive_rule.Input_and_output
           (Step.Typ.unit, subtree_carry_typ) )
      ~auxiliary_typ:Step.Typ.unit
      ~max_proofs_verified:(module Pickles_types.Nat.N2)
      ~name:"layer1" ~o1js_compatible_mode:false
      ~override_wrap_domain:Pickles_base.Proofs_verified.N1
      ~choices:(fun ~self:_ -> [ layer1_rule ])
      ()
  in
  let Pickles.Provers.[ prove ] = provers in
  ( tag
  , (module Proof : Pickles.Proof_intf
      with type t = Pickles_types.Nat.N2.n Pickles.Proof.t
       and type statement = unit * subtree_carry_const )
  , prove )

(** Compile the node circuit.
    Returns (tag, Proof module, prover). *)
let compile_node () =
  let tag, _cache, (module Proof), provers =
    Pickles.compile_promise
      ~cache:(Cache_config.get_cache ())
      ~public_input:
        (Pickles.Inductive_rule.Input_and_output
           (Step.Typ.unit, subtree_carry_typ) )
      ~auxiliary_typ:Step.Typ.unit
      ~max_proofs_verified:(module Pickles_types.Nat.N2)
      ~name:"node" ~o1js_compatible_mode:false
      ~override_wrap_domain:Pickles_base.Proofs_verified.N1
      ~choices:(fun ~self:_ -> [ node_rule ])
      ()
  in
  let Pickles.Provers.[ prove ] = provers in
  ( tag
  , (module Proof : Pickles.Proof_intf
      with type t = Pickles_types.Nat.N2.n Pickles.Proof.t
       and type statement = unit * subtree_carry_const )
  , prove )

(** Prove a layer1 merge of two base-layer proofs.
    [prover] comes from [compile_layer1]. *)
let prove_layer1 ~prover ~(witness : layer1_witness) =
  let handler = layer1_handler witness in
  let output, _aux, proof =
    Promise.block_on_async_exn (fun () -> prover ?handler:(Some handler) ())
  in
  (output, proof)

(** Prove a node merge of two sub-proofs.
    [prover] comes from [compile_node]. *)
let prove_node ~prover ~(witness : node_witness) =
  let handler = node_handler witness in
  let output, _aux, proof =
    Promise.block_on_async_exn (fun () -> prover ?handler:(Some handler) ())
  in
  (output, proof)
