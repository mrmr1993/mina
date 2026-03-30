(** f-update circuit body shared by zkp7-12.

    Each circuit performs a chunk of the final exponentiation's
    "hard part" computation. The hard part computes:
      f^((p^4 - p^2 + 1) / r)
    using a sequence of cyclotomic squarings, Frobenius maps,
    and multiplications.

    For the placeholder implementation, each circuit performs
    several cyclotomic squarings and conditional multiplications,
    matching the structure of the nori implementation. *)

module FF = Snarky_foreign_field.Foreign_field
module Step = Pickles.Impls.Step

(** Number of squarings per circuit for zkp7-12. *)
let squarings_per_circuit =
  [| 10; 10; 10; 10; 10; 12 |]

(** Build the f-update circuit body. *)
let build ~(circuit_index : int) (input_hash : Step.Field.t) :
    Step.Field.t =
  assert (circuit_index >= 7 && circuit_index <= 12) ;
  let idx = circuit_index - 7 in
  let n_squarings = squarings_per_circuit.(idx) in
  (* Witness the Fp12 accumulator *)
  let f : Fp12.Circuit.t =
    let w () : Fp2.Circuit.t =
      { Fp2.Circuit.c0 = FF.Field3.of_constant FF.Bignum_bigint.one
      ; c1 = FF.Field3.of_constant FF.Bignum_bigint.one }
    in
    let w6 () : Fp6.Circuit.t =
      { Fp6.Circuit.c0 = w (); c1 = w (); c2 = w () }
    in
    { Fp12.Circuit.c0 = w6 (); c1 = w6 () }
  in
  (* Witness g values for conditional multiplication *)
  let g : Fp12.Circuit.t =
    let w () : Fp2.Circuit.t =
      { Fp2.Circuit.c0 = FF.Field3.of_constant FF.Bignum_bigint.one
      ; c1 = FF.Field3.of_constant FF.Bignum_bigint.one }
    in
    let w6 () : Fp6.Circuit.t =
      { Fp6.Circuit.c0 = w (); c1 = w (); c2 = w () }
    in
    { Fp12.Circuit.c0 = w6 (); c1 = w6 () }
  in
  (* Perform cyclotomic squarings and multiplications *)
  let result = ref f in
  for _ = 1 to n_squarings do
    result := Fp12.cyclotomic_square !result
  done ;
  (* Multiply by g (conditional on ate loop bit, simplified here) *)
  result := Fp12.mul !result g ;
  ignore (!result : Fp12.Circuit.t) ;
  (* Output hash *)
  Accumulator_hash.combine_hashes
    [ input_hash; Step.Field.of_int circuit_index ]
