(** Pickles rules for PLONK proof conversion circuits.

    Each circuit takes a public input hash, witnesses the accumulator,
    performs verification operations, and returns the output hash.
    The accumulator is returned as auxiliary_output so the prover can
    chain it to the next circuit without re-computing witnesses. *)

open! Core_kernel
module Step = Pickles.Impls.Step

(** Feature flags for each PLONK circuit. *)
let feature_flags ~(n : int) =
  { Pickles_types.Plonk_types.Features.none_bool with
    range_check0 = true
  ; range_check1 = true
  ; foreign_field_add = true
  ; foreign_field_mul = not @@ Array.exists ~f:(( = ) n) [| 0; 7 |]
  ; xor = Array.exists ~f:(( = ) n) [| 0; 1; 3; 7; 8; 10 |]
  }

(** Make a Pickles rule for circuit [n] (unit auxiliary output). *)
let make_rule ~(n : int) : _ Pickles.Inductive_rule.Promise.t =
  let body = Plonk_circuits.circuit_body n in
  { identifier = sprintf "plonk-zkp%d" n
  ; prevs = []
  ; main =
      (fun { public_input = input_hash } ->
        Circuit_utils.dummy_constraints () ;
        let output_hash = body input_hash in
        Promise.return
          { Pickles.Inductive_rule.previous_proof_statements = []
          ; public_output = output_hash
          ; auxiliary_output = ()
          } )
  ; feature_flags = feature_flags ~n
  }

(** Make a rule for circuits 0-11 that returns the Plonk_accumulator
    as auxiliary output, enabling chaining to the next circuit. *)
let make_rule_with_plonk_acc ~(n : int) : _ Pickles.Inductive_rule.Promise.t =
  assert (n >= 0 && n <= 11) ;
  let zkp_fn =
    Plonk_circuits.(
      match n with
      | 0 ->
          zkp0
      | 1 ->
          zkp1
      | 2 ->
          zkp2
      | 3 ->
          zkp3
      | 4 ->
          zkp4
      | 5 ->
          zkp5
      | 6 ->
          zkp6
      | 7 ->
          zkp7
      | 8 ->
          zkp8
      | 9 ->
          zkp9
      | 10 ->
          zkp10
      | 11 ->
          zkp11
      | _ ->
          assert false)
  in
  { identifier = sprintf "plonk-zkp%d" n
  ; prevs = []
  ; main =
      (fun { public_input = input_hash } ->
        Circuit_utils.dummy_constraints () ;
        let output_hash, acc = zkp_fn input_hash in
        Promise.return
          { Pickles.Inductive_rule.previous_proof_statements = []
          ; public_output = output_hash
          ; auxiliary_output = acc
          } )
  ; feature_flags = feature_flags ~n
  }

(** Compile and prove a single PLONK circuit (0-11), returning the
    post-circuit accumulator via auxiliary_output for chaining. *)
let compile_and_prove_one_with_plonk_acc ~(n : int)
    ~(input_hash : Step.Field.Constant.t) ~(witness : Plonk_requests.witness) :
    Step.Field.Constant.t
    * Plonk_accumulator.t_const
    * Pickles_types.Nat.N0.n Pickles.Proof.t =
  let rule = make_rule_with_plonk_acc ~n in
  let _tag, _cache, (module Proof), provers =
    Pickles.compile_promise
      ~public_input:
        (Pickles.Inductive_rule.Input_and_output (Step.Field.typ, Step.Field.typ)
        )
      ~auxiliary_typ:Plonk_accumulator.typ
      ~max_proofs_verified:(module Pickles_types.Nat.N0)
      ~name:(sprintf "plonk-zkp%d" n) ~o1js_compatible_mode:false
      ~choices:(fun ~self:_ -> [ rule ])
      ()
  in
  let Pickles.Provers.[ prove ] = provers in
  let handler = Plonk_requests.handler witness in
  let output_hash, acc_after, proof =
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
      failwith
        (sprintf "plonk-zkp%d verify failed: %s" n (Error.to_string_hum e)) ) ;
  (output_hash, acc_after, proof)

(** Compile and prove a single circuit (unit auxiliary output). *)
let compile_and_prove_one ~(n : int) ~(input_hash : Step.Field.Constant.t)
    ~(witness : Plonk_requests.witness) :
    Step.Field.Constant.t * Pickles_types.Nat.N0.n Pickles.Proof.t =
  let rule = make_rule ~n in
  let _tag, _cache, (module Proof), provers =
    Pickles.compile_promise
      ~public_input:
        (Pickles.Inductive_rule.Input_and_output (Step.Field.typ, Step.Field.typ)
        )
      ~auxiliary_typ:Step.Typ.unit
      ~max_proofs_verified:(module Pickles_types.Nat.N0)
      ~name:(sprintf "plonk-zkp%d" n) ~o1js_compatible_mode:false
      ~choices:(fun ~self:_ -> [ rule ])
      ()
  in
  let Pickles.Provers.[ prove ] = provers in
  let handler = Plonk_requests.handler witness in
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
      failwith
        (sprintf "plonk-zkp%d verify failed: %s" n (Error.to_string_hum e)) ) ;
  (output_hash, proof)

(** Compile a single circuit and return the proof, VK, and output hash.
    Used for cross-verification with nori. *)
let compile_prove_and_export ~(n : int) ~(input_hash : Step.Field.Constant.t)
    ~(witness : Plonk_requests.witness) :
    Step.Field.Constant.t
    * Pickles_types.Nat.N0.n Pickles.Proof.t
    * Pickles.Side_loaded.Verification_key.t =
  let rule = make_rule ~n in
  let tag, _cache, (module Proof), provers =
    Pickles.compile_promise
      ~public_input:
        (Pickles.Inductive_rule.Input_and_output (Step.Field.typ, Step.Field.typ)
        )
      ~auxiliary_typ:Step.Typ.unit
      ~max_proofs_verified:(module Pickles_types.Nat.N0)
      ~name:(sprintf "plonk-zkp%d" n) ~o1js_compatible_mode:false
      ~choices:(fun ~self:_ -> [ rule ])
      ()
  in
  let vk =
    Promise.block_on_async_exn (fun () ->
        Pickles.Side_loaded.Verification_key.of_compiled_promise tag )
  in
  let Pickles.Provers.[ prove ] = provers in
  let handler = Plonk_requests.handler witness in
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
      failwith
        (sprintf "plonk-zkp%d verify failed: %s" n (Error.to_string_hum e)) ) ;
  (output_hash, proof, vk)

(** Prove all 24 PLONK circuits in sequence with accumulator chaining.
    Each circuit's auxiliary_output (the post-circuit accumulator) feeds
    as the witness for the next circuit. Returns all proofs and hash pairs. *)
let compile_and_prove_all_chained ~(initial_acc : Plonk_accumulator.t_const)
    ~(initial_hash : Step.Field.Constant.t) :
    (Step.Field.Constant.t * Step.Field.Constant.t) array
    * Pickles_types.Nat.N0.n Pickles.Proof.t array =
  let current_hash = ref initial_hash in
  let current_acc = ref initial_acc in
  let hash_pairs =
    Array.create ~len:Plonk_circuits.num_circuits
      (Step.Field.Constant.zero, Step.Field.Constant.zero)
  in
  let proofs =
    Array.create ~len:Plonk_circuits.num_circuits
      (Obj.magic () : Pickles_types.Nat.N0.n Pickles.Proof.t)
  in
  for n = 0 to Plonk_circuits.num_circuits - 1 do
    let input_hash = !current_hash in
    let witness : Plonk_requests.witness =
      { Plonk_requests.empty_witness with plonk_acc = Some !current_acc }
    in
    let output_hash, acc_after, proof =
      compile_and_prove_one_with_plonk_acc ~n ~input_hash ~witness
    in
    hash_pairs.(n) <- (input_hash, output_hash) ;
    proofs.(n) <- proof ;
    current_hash := output_hash ;
    current_acc := acc_after
  done ;
  (hash_pairs, proofs)

(** Legacy: prove all with pre-computed witnesses (no chaining). *)
let compile_and_prove_all ~(witnesses : Plonk_requests.witness array) :
    Pickles_types.Nat.N0.n Pickles.Proof.t array =
  assert (Array.length witnesses = Plonk_circuits.num_circuits) ;
  let current_hash = ref Step.Field.Constant.zero in
  let proofs =
    Array.init Plonk_circuits.num_circuits ~f:(fun n ->
        let output_hash, proof =
          compile_and_prove_one ~n ~input_hash:!current_hash
            ~witness:witnesses.(n)
        in
        current_hash := output_hash ;
        proof )
  in
  proofs
