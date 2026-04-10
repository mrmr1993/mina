(** Pickles rules for PLONK proof conversion circuits. *)

open! Core_kernel
module Step = Pickles.Impls.Step

let make_rule ~(n : int) : _ Pickles.Inductive_rule.Promise.t =
  let body = Plonk_circuits.build_circuit_body ~circuit_index:n in
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
  ; feature_flags =
      { Pickles_types.Plonk_types.Features.none_bool with
        range_check0 = true
      ; range_check1 = true
      ; foreign_field_add = true
      ; foreign_field_mul = not @@ Array.exists ~f:(( = ) n) [| 0; 7 |]
      ; xor = Array.exists ~f:(( = ) n) [| 0; 1; 3; 7; 8; 10 |]
      }
  }

let compile_and_prove_one ~(n : int) ~(input_hash : Step.Field.Constant.t) :
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
  let output_hash, _aux, proof =
    Promise.block_on_async_exn (fun () -> prove input_hash)
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

let compile_and_prove_all () : Pickles_types.Nat.N0.n Pickles.Proof.t array =
  let current_hash = ref Step.Field.Constant.zero in
  let proofs =
    Array.init Plonk_circuits.num_circuits ~f:(fun n ->
        let output_hash, proof =
          compile_and_prove_one ~n ~input_hash:!current_hash
        in
        current_hash := output_hash ;
        proof )
  in
  proofs
