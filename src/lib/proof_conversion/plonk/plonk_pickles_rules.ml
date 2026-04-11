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
      ~cache:(Cache_config.get_cache ())
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

(** Compile and prove zkp12, returning the KZG accumulator for chaining. *)
let compile_and_prove_zkp12 ~(input_hash : Step.Field.Constant.t)
    ~(witness : Plonk_requests.witness) :
    Step.Field.Constant.t
    * Kzg_accumulator.t_const
    * Pickles_types.Nat.N0.n Pickles.Proof.t =
  let rule : _ Pickles.Inductive_rule.Promise.t =
    { identifier = "plonk-zkp12"
    ; prevs = []
    ; main =
        (fun { public_input = input_hash } ->
          Circuit_utils.dummy_constraints () ;
          let output_hash, kzg_acc = Plonk_circuits.zkp12 input_hash in
          Promise.return
            { Pickles.Inductive_rule.previous_proof_statements = []
            ; public_output = output_hash
            ; auxiliary_output = kzg_acc
            } )
    ; feature_flags = feature_flags ~n:12
    }
  in
  let _tag, _cache, (module Proof), provers =
    Pickles.compile_promise
      ~cache:(Cache_config.get_cache ())
      ~public_input:
        (Pickles.Inductive_rule.Input_and_output (Step.Field.typ, Step.Field.typ)
        )
      ~auxiliary_typ:Kzg_accumulator.typ
      ~max_proofs_verified:(module Pickles_types.Nat.N0)
      ~name:"plonk-zkp12" ~o1js_compatible_mode:false
      ~choices:(fun ~self:_ -> [ rule ])
      ()
  in
  let Pickles.Provers.[ prove ] = provers in
  let handler = Plonk_requests.handler witness in
  let output_hash, kzg_after, proof =
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
      failwith (sprintf "plonk-zkp12 verify failed: %s" (Error.to_string_hum e))
  ) ;
  (output_hash, kzg_after, proof)

(** Number of g values produced by each line-hashing circuit. *)
let zkp_lines_g_count ~circuit_index =
  let ate = Kzg_accumulator.ate_loop_count in
  let ate_len = Array.length ate in
  match circuit_index with
  | 13 ->
      ate_len - 46 - 1
  | 14 | 15 ->
      20
  | 16 ->
      ate_len - 59 + 1 (* loop iterations + 1 Frobenius *)
  | _ ->
      assert false

(** Compile and prove zkp13-16 (line hashing), returning the updated
    KZG accumulator, lines_hashes, and g values for chaining. *)
let compile_and_prove_zkp_lines ~(circuit_index : int)
    ~(input_hash : Step.Field.Constant.t) ~(witness : Plonk_requests.witness) :
    Step.Field.Constant.t
    * Kzg_accumulator.t_const
    * Step.Field.Constant.t array
    * Fp12.Constant.t array
    * Pickles_types.Nat.N0.n Pickles.Proof.t =
  assert (circuit_index >= 13 && circuit_index <= 16) ;
  let ate_loop_len = Kzg_accumulator.ate_loop_len in
  let g_count = zkp_lines_g_count ~circuit_index in
  let rule : _ Pickles.Inductive_rule.Promise.t =
    { identifier = sprintf "plonk-zkp%d" circuit_index
    ; prevs = []
    ; main =
        (fun { public_input = input_hash } ->
          Circuit_utils.dummy_constraints () ;
          let output_hash, kzg, lh, gv =
            Plonk_circuits.zkp_lines ~circuit_index input_hash
          in
          Promise.return
            { Pickles.Inductive_rule.previous_proof_statements = []
            ; public_output = output_hash
            ; auxiliary_output = ((kzg, lh), gv)
            } )
    ; feature_flags = feature_flags ~n:circuit_index
    }
  in
  let _tag, _cache, (module Proof), provers =
    Pickles.compile_promise
      ~cache:(Cache_config.get_cache ())
      ~public_input:
        (Pickles.Inductive_rule.Input_and_output (Step.Field.typ, Step.Field.typ)
        )
      ~auxiliary_typ:
        Step.Typ.(
          Kzg_accumulator.typ
          * array ~length:ate_loop_len Step.Field.typ
          * array ~length:g_count Fp12.typ)
      ~max_proofs_verified:(module Pickles_types.Nat.N0)
      ~name:(sprintf "plonk-zkp%d" circuit_index)
      ~o1js_compatible_mode:false
      ~choices:(fun ~self:_ -> [ rule ])
      ()
  in
  let Pickles.Provers.[ prove ] = provers in
  let handler = Plonk_requests.handler witness in
  let output_hash, ((kzg_after, lh_after), gv_after), proof =
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
        (sprintf "plonk-zkp%d verify failed: %s" circuit_index
           (Error.to_string_hum e) ) ) ;
  (output_hash, kzg_after, lh_after, gv_after, proof)

(** Compile and prove zkp17-22 (f-accumulation), returning the updated
    KZG accumulator for chaining. *)
let compile_and_prove_zkp_f_accum ~(circuit_index : int)
    ~(input_hash : Step.Field.Constant.t) ~(witness : Plonk_requests.witness) :
    Step.Field.Constant.t
    * Kzg_accumulator.t_const
    * Pickles_types.Nat.N0.n Pickles.Proof.t =
  assert (circuit_index >= 17 && circuit_index <= 22) ;
  let rule : _ Pickles.Inductive_rule.Promise.t =
    { identifier = sprintf "plonk-zkp%d" circuit_index
    ; prevs = []
    ; main =
        (fun { public_input = input_hash } ->
          Circuit_utils.dummy_constraints () ;
          let output_hash, kzg =
            Plonk_circuits.zkp_f_accum ~circuit_index input_hash
          in
          Promise.return
            { Pickles.Inductive_rule.previous_proof_statements = []
            ; public_output = output_hash
            ; auxiliary_output = kzg
            } )
    ; feature_flags = feature_flags ~n:circuit_index
    }
  in
  let _tag, _cache, (module Proof), provers =
    Pickles.compile_promise
      ~cache:(Cache_config.get_cache ())
      ~public_input:
        (Pickles.Inductive_rule.Input_and_output (Step.Field.typ, Step.Field.typ)
        )
      ~auxiliary_typ:Kzg_accumulator.typ
      ~max_proofs_verified:(module Pickles_types.Nat.N0)
      ~name:(sprintf "plonk-zkp%d" circuit_index)
      ~o1js_compatible_mode:false
      ~choices:(fun ~self:_ -> [ rule ])
      ()
  in
  let Pickles.Provers.[ prove ] = provers in
  let handler = Plonk_requests.handler witness in
  let output_hash, kzg_after, proof =
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
        (sprintf "plonk-zkp%d verify failed: %s" circuit_index
           (Error.to_string_hum e) ) ) ;
  (output_hash, kzg_after, proof)

(** Compile and prove a single circuit (unit auxiliary output). *)
let compile_and_prove_one ~(n : int) ~(input_hash : Step.Field.Constant.t)
    ~(witness : Plonk_requests.witness) :
    Step.Field.Constant.t * Pickles_types.Nat.N0.n Pickles.Proof.t =
  let rule = make_rule ~n in
  let _tag, _cache, (module Proof), provers =
    Pickles.compile_promise
      ~cache:(Cache_config.get_cache ())
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
      ~cache:(Cache_config.get_cache ())
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
