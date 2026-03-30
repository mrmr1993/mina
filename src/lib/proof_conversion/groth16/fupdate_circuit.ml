(** f-update circuit body shared by zkp7-12. *)

module Step = Pickles.Impls.Step
module WT = Witness_tracker

let squarings_per_circuit = [| 10; 10; 10; 10; 10; 12 |]

let build ~(circuit_index : int) (input_hash : Step.Field.t) : Step.Field.t =
  assert (circuit_index >= 7 && circuit_index <= 12) ;
  let idx = circuit_index - 7 in
  let n_squarings = squarings_per_circuit.(idx) in
  let f =
    Step.exists Fp12.Circuit.typ ~compute:(fun () ->
        let tracker = Circuit_config.get_tracker () in
        WT.get_f tracker )
  in
  let g =
    Step.exists Fp12.Circuit.typ ~compute:(fun () ->
        let tracker = Circuit_config.get_tracker () in
        WT.get_f tracker )
  in
  let result = ref f in
  for _ = 1 to n_squarings do
    result := Fp12.cyclotomic_square !result
  done ;
  result := Fp12.mul !result g ;
  ignore (!result : Fp12.Circuit.t) ;
  Accumulator_hash.combine_hashes
    [ input_hash; Step.Field.of_int circuit_index ]
