open Pickles.Impls.Step

module type Inputs = sig
  module Accumulator : sig
    type t

    type circuit

    val typ : (circuit, t) Typ.t
  end

  module ATE_LOOP_COUNT : sig
    val length : int
  end

  module VK : sig
    val delta_lines : 'a

    val gamma_lines : 'a
  end

  module G2Line : sig
    type t

    type circuit

    val typ : (circuit, t) Typ.t
  end

  module LineParser : sig
    val parse : int -> int -> 'a -> 'b
  end
end

module Make (Inputs : Inputs) = struct
  open Inputs

  let begin_ = 1

  let end_ = ATE_LOOP_COUNT.length - 55

  let delta_lines = LineParser.parse begin_ end_ VK.delta_lines

  let gamma_lines = LineParser.parse begin_ end_ VK.gamma_lines

  let auxiliary_input_typ =
    Typ.tuple3 Accumulator.typ
      (Typ.array ~length:ATE_LOOP_COUNT.length Field.typ)
      (Typ.array ~length:91 G2Line.typ)

  let tags, cache, proof, provers =
    Pickles.compile
      ~public_input:(Input_and_output (Field.typ, Field.typ))
      ~auxiliary_typ:Typ.unit
      ~max_proofs_verified:(module Pickles_types.Nat.N0)
      ~name:"groth16_conversion_0"
      ~choices:(fun ~self:_ ->
        [ { identifier = "groth16_conversion_0"
          ; prevs = []
          ; main =
              (fun { public_input } ->
                ignore (public_input : Field.t) ;
                { previous_proof_statements = []
                ; public_output = Field.zero (* TODO *)
                ; auxiliary_output = ()
                } )
          ; feature_flags = Pickles_types.Plonk_types.Features.none_bool
          }
        ] )
      ()
end
