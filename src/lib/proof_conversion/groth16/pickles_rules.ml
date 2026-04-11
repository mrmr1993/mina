(** Pickles inductive rules for Groth16 proof conversion.

    Each circuit uses public input = [input_hash] and
    public output = [output_hash] to chain circuits together.
    The hash is a Poseidon digest of the accumulator state. *)

open! Core_kernel
module Step = Pickles.Impls.Step

(** Build a Pickles inductive rule for circuit [n]. *)
let make_rule ~(vk : Vk_constants.t) ~(n : int) :
    _ Pickles.Inductive_rule.Promise.t =
  let body = Circuits.build_circuit_body ~vk ~circuit_index:n in
  { identifier = sprintf "zkp%d" n
  ; prevs = []
  ; main =
      (fun { public_input = input_hash } ->
        Circuit_utils.dummy_constraints () ;
        (* pub is Field.t array of length 1 = [input_hash] *)
        let output_hash = body input_hash in
        Promise.return
          { Pickles.Inductive_rule.previous_proof_statements = []
          ; public_output = output_hash
          ; auxiliary_output = ()
          } )
  ; feature_flags =
      (* All Groth16 circuits use foreign field arithmetic and Poseidon hashing.
         Feature flags must exactly match the gate types present. *)
      ( ignore (n : int) ;
        { Pickles_types.Plonk_types.Features.none_bool with
          range_check0 = true
        ; range_check1 = true
        ; foreign_field_add = true
        ; foreign_field_mul = true
        } )
  }

(** Compile and prove a single circuit.
    Takes the input hash value and returns (output_hash, proof). *)
let compile_and_prove_one ~(vk : Vk_constants.t) ~(n : int)
    ~(input_hash : Step.Field.Constant.t) ~(witness : Groth16_requests.witness)
    : Step.Field.Constant.t * Pickles_types.Nat.N0.n Pickles.Proof.t =
  let rule = make_rule ~vk ~n in
  let _tag, _cache, (module Proof), provers =
    Pickles.compile_promise
      ~cache:(Cache_config.get_cache ())
      ~public_input:
        (Pickles.Inductive_rule.Input_and_output (Step.Field.typ, Step.Field.typ)
        )
      ~auxiliary_typ:Step.Typ.unit
      ~max_proofs_verified:(module Pickles_types.Nat.N0)
      ~name:(sprintf "groth16-zkp%d" n)
      ~o1js_compatible_mode:false
      ~choices:(fun ~self:_ -> [ rule ])
      ()
  in
  let Pickles.Provers.[ prove ] = provers in
  let handler = Groth16_requests.handler witness in
  let output_hash, _aux, proof =
    Promise.block_on_async_exn (fun () -> prove ~handler input_hash)
  in
  (* Verify *)
  let verified =
    Promise.block_on_async_exn (fun () ->
        Proof.verify_promise [ ((input_hash, output_hash), proof) ] )
  in
  ( match verified with
  | Ok () ->
      ()
  | Error e ->
      failwith (sprintf "zkp%d verify failed: %s" n (Error.to_string_hum e)) ) ;
  (output_hash, proof)

(** Build a rule that returns the Groth16 Accumulator as auxiliary output.
    Used for circuits 0-12 to chain accumulator state.
    Uses [build_circuit_body_with_acc] which returns (hash, acc). *)
let make_rule_with_acc ~(vk : Vk_constants.t) ~(n : int) :
    _ Pickles.Inductive_rule.Promise.t =
  assert (n >= 0 && n <= 12) ;
  let body = Circuits.build_circuit_body_with_acc ~vk ~circuit_index:n in
  { identifier = sprintf "zkp%d" n
  ; prevs = []
  ; main =
      (fun { public_input = input_hash } ->
        Circuit_utils.dummy_constraints () ;
        let output_hash, (acc, lh, gv) = body input_hash in
        Promise.return
          { Pickles.Inductive_rule.previous_proof_statements = []
          ; public_output = output_hash
          ; auxiliary_output = ((acc, lh), gv)
          } )
  ; feature_flags =
      ( ignore (n : int) ;
        { Pickles_types.Plonk_types.Features.none_bool with
          range_check0 = true
        ; range_check1 = true
        ; foreign_field_add = true
        ; foreign_field_mul = true
        } )
  }

(** Compile and prove a single circuit (0-12), returning the accumulator
    and line_hashes via auxiliary_output for chaining. *)
let compile_and_prove_one_with_acc ~(vk : Vk_constants.t) ~(n : int)
    ~(input_hash : Step.Field.Constant.t) ~(witness : Groth16_requests.witness)
    :
    Step.Field.Constant.t
    * Accumulator.Constant.t
    * Step.Field.Constant.t array
    * Fp12.Constant.t array
    * Pickles_types.Nat.N0.n Pickles.Proof.t =
  let rule = make_rule_with_acc ~vk ~n in
  let _tag, _cache, (module Proof), provers =
    Pickles.compile_promise
      ~cache:(Cache_config.get_cache ())
      ~public_input:
        (Pickles.Inductive_rule.Input_and_output (Step.Field.typ, Step.Field.typ)
        )
      ~auxiliary_typ:(Circuits.ate_aux_typ_with_g ~circuit_index:n)
      ~max_proofs_verified:(module Pickles_types.Nat.N0)
      ~name:(sprintf "groth16-zkp%d" n)
      ~o1js_compatible_mode:false
      ~choices:(fun ~self:_ -> [ rule ])
      ()
  in
  let Pickles.Provers.[ prove ] = provers in
  let handler = Groth16_requests.handler witness in
  let output_hash, ((acc_after, lh_after), gv_after), proof =
    Promise.block_on_async_exn (fun () -> prove ~handler input_hash)
  in
  let verified =
    Promise.block_on_async_exn (fun () ->
        Proof.verify_promise [ ((input_hash, output_hash), proof) ] )
  in
  ( match verified with
  | Ok () ->
      ()
  | Error e ->
      failwith (sprintf "zkp%d verify failed: %s" n (Error.to_string_hum e)) ) ;
  (output_hash, acc_after, lh_after, gv_after, proof)

(** Compile and prove all 16 circuits, chaining input/output hashes. *)
let compile_and_prove_all ~(vk : Vk_constants.t)
    ~(witnesses : Groth16_requests.witness array) :
    Pickles_types.Nat.N0.n Pickles.Proof.t array =
  assert (Array.length witnesses = Circuits.num_circuits) ;
  let current_hash = ref Step.Field.Constant.zero in
  let proofs =
    Array.init Circuits.num_circuits ~f:(fun n ->
        let output_hash, proof =
          compile_and_prove_one ~vk ~n ~input_hash:!current_hash
            ~witness:witnesses.(n)
        in
        current_hash := output_hash ;
        proof )
  in
  proofs

(** Compile and prove a single circuit, returning proof + VK for tree
    compression.  Used for circuits that don't need accumulator chaining
    (13-15). *)
let compile_prove_and_export ~(vk : Vk_constants.t) ~(n : int)
    ~(input_hash : Step.Field.Constant.t) ~(witness : Groth16_requests.witness)
    :
    Step.Field.Constant.t
    * Pickles_types.Nat.N0.n Pickles.Proof.t
    * Pickles.Side_loaded.Verification_key.t =
  let rule = make_rule ~vk ~n in
  let tag, _cache, (module Proof), provers =
    Pickles.compile_promise
      ~cache:(Cache_config.get_cache ())
      ~public_input:
        (Pickles.Inductive_rule.Input_and_output (Step.Field.typ, Step.Field.typ)
        )
      ~auxiliary_typ:Step.Typ.unit
      ~max_proofs_verified:(module Pickles_types.Nat.N0)
      ~name:(sprintf "groth16-zkp%d" n)
      ~o1js_compatible_mode:false
      ~choices:(fun ~self:_ -> [ rule ])
      ()
  in
  let side_vk =
    Promise.block_on_async_exn (fun () ->
        Pickles.Side_loaded.Verification_key.of_compiled_promise tag )
  in
  let Pickles.Provers.[ prove ] = provers in
  let handler = Groth16_requests.handler witness in
  let output_hash, _aux, proof =
    Promise.block_on_async_exn (fun () -> prove ~handler input_hash)
  in
  let verified =
    Promise.block_on_async_exn (fun () ->
        Proof.verify_promise [ ((input_hash, output_hash), proof) ] )
  in
  ( match verified with
  | Ok () ->
      ()
  | Error e ->
      failwith (sprintf "zkp%d verify failed: %s" n (Error.to_string_hum e)) ) ;
  (output_hash, proof, side_vk)

(** Compile and prove a single circuit (0-12), returning the accumulator,
    line_hashes, g_values, and VK via auxiliary_output for chaining +
    tree compression. *)
let compile_prove_and_export_with_acc ~(vk : Vk_constants.t) ~(n : int)
    ~(input_hash : Step.Field.Constant.t) ~(witness : Groth16_requests.witness)
    :
    Step.Field.Constant.t
    * Accumulator.Constant.t
    * Step.Field.Constant.t array
    * Fp12.Constant.t array
    * Pickles_types.Nat.N0.n Pickles.Proof.t
    * Pickles.Side_loaded.Verification_key.t =
  let rule = make_rule_with_acc ~vk ~n in
  let tag, _cache, (module Proof), provers =
    Pickles.compile_promise
      ~cache:(Cache_config.get_cache ())
      ~public_input:
        (Pickles.Inductive_rule.Input_and_output (Step.Field.typ, Step.Field.typ)
        )
      ~auxiliary_typ:(Circuits.ate_aux_typ_with_g ~circuit_index:n)
      ~max_proofs_verified:(module Pickles_types.Nat.N0)
      ~name:(sprintf "groth16-zkp%d" n)
      ~o1js_compatible_mode:false
      ~choices:(fun ~self:_ -> [ rule ])
      ()
  in
  let side_vk =
    Promise.block_on_async_exn (fun () ->
        Pickles.Side_loaded.Verification_key.of_compiled_promise tag )
  in
  let Pickles.Provers.[ prove ] = provers in
  let handler = Groth16_requests.handler witness in
  let output_hash, ((acc_after, lh_after), gv_after), proof =
    Promise.block_on_async_exn (fun () -> prove ~handler input_hash)
  in
  let verified =
    Promise.block_on_async_exn (fun () ->
        Proof.verify_promise [ ((input_hash, output_hash), proof) ] )
  in
  ( match verified with
  | Ok () ->
      ()
  | Error e ->
      failwith (sprintf "zkp%d verify failed: %s" n (Error.to_string_hum e)) ) ;
  (output_hash, acc_after, lh_after, gv_after, proof, side_vk)
