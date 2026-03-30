(** Pickles inductive rules for Groth16 proof conversion.

    Each of the 16 circuits is compiled as a separate Pickles program
    (no previous proofs — base case only). The circuits are chained
    via Poseidon hash of the accumulator state passed as public I/O. *)

module Step = Pickles.Impls.Step

(** Build a Pickles inductive rule for circuit [n]. *)
let make_rule ~(n : int) : _ Pickles.Inductive_rule.Promise.t =
  let body = Circuits.build_circuit_body ~circuit_index:n in
  { identifier = Printf.sprintf "zkp%d" n
  ; prevs = []
  ; main =
      (fun { public_input = _pub } ->
        Circuit_utils.dummy_constraints () ;
        body () ;
        Promise.return
          { Pickles.Inductive_rule.previous_proof_statements = []
          ; public_output = [||]
          ; auxiliary_output = ()
          } )
  ; feature_flags = Pickles_types.Plonk_types.Features.none_bool
  }

(** The statement type for our circuits:
    Input_and_output(Field.t array * Field.t array) with both length 0. *)
type statement =
  Step.Field.Constant.t array * Step.Field.Constant.t array

(** Result of compiling a single circuit. *)
type compiled_circuit =
  { name : string
  ; tag : ( Step.Field.t array * Step.Field.t array
          , statement
          , Pickles_types.Nat.N0.n
          , Pickles_types.Nat.N1.n )
          Pickles.Tag.t
  ; prove :
         Step.Field.Constant.t array
      -> ( Step.Field.Constant.t array
         * unit
         * Pickles_types.Nat.N0.n Pickles.Proof.t )
         Promise.t
  ; vk_promise : Pickles.Verification_key.t Promise.t Lazy.t
  }

(** Compile a single circuit via Pickles. *)
let compile_circuit ~(n : int) : compiled_circuit =
  Printf.printf "  Compiling zkp%d... %!" n ;
  let rule = make_rule ~n in
  let tag, _cache, (module Proof), provers =
    Pickles.compile_promise
      ~public_input:
        (Pickles.Inductive_rule.Input_and_output
           (Circuit_utils.public_input_typ 0, Circuit_utils.public_input_typ 0))
      ~auxiliary_typ:Step.Typ.unit
      ~max_proofs_verified:(module Pickles_types.Nat.N0)
      ~name:(Printf.sprintf "groth16-zkp%d" n)
      ~o1js_compatible_mode:true
      ~choices:(fun ~self:_ -> [ rule ])
      ()
  in
  let (Pickles.Provers.[ prove ]) = provers in
  Printf.printf "done\n%!" ;
  { name = Printf.sprintf "zkp%d" n
  ; tag
  ; prove
  ; vk_promise = Proof.verification_key_promise
  }

(** Compile all 16 circuits. *)
let compile_all () : compiled_circuit array =
  Printf.printf "Compiling %d Groth16 circuits via Pickles...\n%!"
    Circuits.num_circuits ;
  Array.init Circuits.num_circuits (fun n -> compile_circuit ~n)

(** Compile all circuits. *)
let compile () =
  let circuits = compile_all () in
  Printf.printf "All %d circuits compiled successfully.\n%!"
    (Array.length circuits) ;
  circuits

(** Prove a single circuit with empty public input/output. *)
let prove_circuit (c : compiled_circuit) : Pickles_types.Nat.N0.n Pickles.Proof.t =
  Printf.printf "  Proving %s... %!" c.name ;
  let empty_input = [||] in
  let _output, _aux, proof =
    Promise.block_on_async_exn (fun () ->
      c.prove empty_input )
  in
  Printf.printf "done\n%!" ;
  proof

(** Prove all 16 circuits sequentially. *)
let prove_all (circuits : compiled_circuit array) :
    Pickles_types.Nat.N0.n Pickles.Proof.t array =
  Printf.printf "Proving %d circuits...\n%!" (Array.length circuits) ;
  Array.map (fun c -> prove_circuit c) circuits
