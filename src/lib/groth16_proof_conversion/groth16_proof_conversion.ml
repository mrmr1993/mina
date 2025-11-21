open Pickles.Impls.Step

module type Inputs = sig
  module ATE_LOOP_COUNT : sig
    val length : int
  end

  module VK : sig
    val delta_lines : 'a

    val gamma_lines : 'a
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

  let tags, cache, proof, provers =
    Pickles.compile
      ~public_input:(Input_and_output (Typ.unit, Typ.unit))
      ~auxiliary_typ:Typ.unit
      ~max_proofs_verified:(module Pickles_types.Nat.N0)
      ~name:"groth16_conversion_0"
      ~choices:(fun ~self:_ -> [])
      ()
end
