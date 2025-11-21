open Pickles.Impls.Step

module type Inputs = sig end

module Make (Inputs : Inputs) = struct
  let tags, cache, proof, provers =
    Pickles.compile
      ~public_input:(Input_and_output (Typ.unit, Typ.unit))
      ~auxiliary_typ:Typ.unit
      ~max_proofs_verified:(module Pickles_types.Nat.N0)
      ~name:"groth16_conversion_0"
      ~choices:(fun ~self:_ -> [])
      ()
end
