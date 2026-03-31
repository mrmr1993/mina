(** Pickles inductive rules for Groth16 proof conversion.

    Each circuit uses public input = [input_hash] and
    public output = [output_hash] to chain circuits together.
    The hash is a Poseidon digest of the accumulator state. *)

open! Core_kernel
module Step = Pickles.Impls.Step

(** Build a Pickles inductive rule for circuit [n]. *)
let make_rule ~(n : int) : _ Pickles.Inductive_rule.Promise.t =
  let body = Circuits.build_circuit_body ~circuit_index:n in
  { identifier = sprintf "zkp%d" n
  ; prevs = []
  ; main =
      (fun { public_input = pub } ->
        Circuit_utils.dummy_constraints () ;
        (* pub is Field.t array of length 1 = [input_hash] *)
        let input_hash = pub.(0) in
        let output_hash = body input_hash in
        Promise.return
          { Pickles.Inductive_rule.previous_proof_statements = []
          ; public_output = [| output_hash |]
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
let compile_and_prove_one ~(n : int) ~(input_hash : Step.Field.Constant.t) :
    Step.Field.Constant.t * Pickles_types.Nat.N0.n Pickles.Proof.t =
  printf "  [zkp%d] compiling... %!" n ;
  let rule = make_rule ~n in
  let _tag, _cache, (module Proof), provers =
    Pickles.compile_promise
      ~public_input:
        (Pickles.Inductive_rule.Input_and_output
           (Circuit_utils.public_input_typ 1, Circuit_utils.public_input_typ 1)
        )
      ~auxiliary_typ:Step.Typ.unit
      ~max_proofs_verified:(module Pickles_types.Nat.N0)
      ~name:(sprintf "groth16-zkp%d" n)
      ~o1js_compatible_mode:false
      ~choices:(fun ~self:_ -> [ rule ])
      ()
  in
  let Pickles.Provers.[ prove ] = provers in
  printf "proving... %!" ;
  let output, _aux, proof =
    Promise.block_on_async_exn (fun () -> prove [| input_hash |])
  in
  let output_hash = output.(0) in
  (* Verify *)
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

(** Compile and prove all 16 circuits, chaining input/output hashes. *)
let compile_and_prove_all () : Pickles_types.Nat.N0.n Pickles.Proof.t array =
  printf "Compiling and proving %d circuits (chained)...\n%!"
    Circuits.num_circuits ;
  let current_hash = ref Step.Field.Constant.zero in
  let proofs =
    Array.init Circuits.num_circuits ~f:(fun n ->
        let output_hash, proof =
          compile_and_prove_one ~n ~input_hash:!current_hash
        in
        current_hash := output_hash ;
        proof )
  in
  printf "Final chain hash: %s\n%!"
    (Kimchi_pasta.Pasta.Fp.to_string !current_hash) ;
  proofs
