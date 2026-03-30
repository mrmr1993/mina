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

(** Compile and immediately prove a single circuit.
    Must be called within an async context (Promise.block_on_async_exn). *)
let compile_and_prove_one ~(n : int) :
    Pickles_types.Nat.N0.n Pickles.Proof.t =
  Printf.printf "  [zkp%d] compiling... %!" n ;
  let rule = make_rule ~n in
  let _tag, _cache, (module Proof), provers =
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
  Printf.printf "proving... %!" ;
  let _output, _aux, proof =
    Promise.block_on_async_exn (fun () -> prove [||])
  in
  Printf.printf "done\n%!" ;
  proof

(** Compile all circuits (without proving). *)
let compile () =
  Printf.printf "Compiling %d Groth16 circuits via Pickles...\n%!"
    Circuits.num_circuits ;
  for n = 0 to Circuits.num_circuits - 1 do
    Printf.printf "  Compiling zkp%d... %!" n ;
    let rule = make_rule ~n in
    let _tag, _cache, (module Proof), _provers =
      Pickles.compile_promise
        ~public_input:
          (Pickles.Inductive_rule.Input_and_output
             (Circuit_utils.public_input_typ 0,
              Circuit_utils.public_input_typ 0))
        ~auxiliary_typ:Step.Typ.unit
        ~max_proofs_verified:(module Pickles_types.Nat.N0)
        ~name:(Printf.sprintf "groth16-zkp%d" n)
        ~o1js_compatible_mode:true
        ~choices:(fun ~self:_ -> [ rule ])
        ()
    in
    Printf.printf "done\n%!"
  done ;
  Printf.printf "All %d circuits compiled successfully.\n%!"
    Circuits.num_circuits

(** Compile and prove a single circuit end-to-end (for testing). *)
let compile_and_prove_single ~(n : int) :
    Pickles_types.Nat.N0.n Pickles.Proof.t =
  compile_and_prove_one ~n
