(** Pickles inductive rules for Groth16 proof conversion.

    Each of the 16 circuits is compiled as a separate Pickles rule
    with no previous proofs (base case). The circuits are chained
    via Poseidon hash of the accumulator state.

    The compression tree (layer1 + merge nodes) is handled separately. *)

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

(** Compile all 16 circuits via Pickles.
    Returns the tag and provers for each circuit. *)
let compile () =
  Printf.printf "Compiling %d Groth16 circuits...\n%!" Circuits.num_circuits ;
  let rules =
    Array.init Circuits.num_circuits (fun n -> make_rule ~n)
  in
  ignore rules ;
  failwith "Groth16 Pickles compilation not yet implemented"
