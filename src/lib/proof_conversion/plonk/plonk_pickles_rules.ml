(** Pickles rules for PLONK proof conversion circuits. *)

open! Core_kernel
module Step = Pickles.Impls.Step

let make_rule ~(n : int) : _ Pickles.Inductive_rule.Promise.t =
  let body = Plonk_circuits.build_circuit_body ~circuit_index:n in
  { identifier = sprintf "plonk-zkp%d" n
  ; prevs = []
  ; main =
      (fun { public_input = pub } ->
        Circuit_utils.dummy_constraints () ;
        let input_hash = pub.(0) in
        let output_hash = body input_hash in
        Promise.return
          { Pickles.Inductive_rule.previous_proof_statements = []
          ; public_output = [| output_hash |]
          ; auxiliary_output = ()
          } )
  ; feature_flags = Pickles_types.Plonk_types.Features.none_bool
  }

let compile_and_prove_one ~(n : int) ~(input_hash : Step.Field.Constant.t) :
    Step.Field.Constant.t * Pickles_types.Nat.N0.n Pickles.Proof.t =
  printf "  [plonk-zkp%d] compiling... %!" n ;
  let rule = make_rule ~n in
  let _tag, _cache, (module Proof), provers =
    Pickles.compile_promise
      ~public_input:
        (Pickles.Inductive_rule.Input_and_output
           (Circuit_utils.public_input_typ 1, Circuit_utils.public_input_typ 1)
        )
      ~auxiliary_typ:Step.Typ.unit
      ~max_proofs_verified:(module Pickles_types.Nat.N0)
      ~name:(sprintf "plonk-zkp%d" n) ~o1js_compatible_mode:true
      ~choices:(fun ~self:_ -> [ rule ])
      ()
  in
  let Pickles.Provers.[ prove ] = provers in
  printf "proving... %!" ;
  let output, _aux, proof =
    Promise.block_on_async_exn (fun () -> prove [| input_hash |])
  in
  let output_hash = output.(0) in
  let verified =
    Promise.block_on_async_exn (fun () ->
        Proof.verify_promise [ (([| input_hash |], [| output_hash |]), proof) ] )
  in
  ( match verified with
  | Ok () ->
      printf "verified ✓\n%!"
  | Error e ->
      printf "VERIFY FAILED: %s\n%!" (Error.to_string_hum e) ) ;
  (output_hash, proof)

let compile_and_prove_all () : Pickles_types.Nat.N0.n Pickles.Proof.t array =
  printf "Compiling and proving %d PLONK circuits (chained)...\n%!"
    Plonk_circuits.num_circuits ;
  let current_hash = ref Step.Field.Constant.zero in
  let proofs =
    Array.init Plonk_circuits.num_circuits ~f:(fun n ->
        let output_hash, proof =
          compile_and_prove_one ~n ~input_hash:!current_hash
        in
        current_hash := output_hash ;
        proof )
  in
  printf "Final PLONK chain hash: %s\n%!"
    (Kimchi_pasta.Pasta.Fp.to_string !current_hash) ;
  proofs
