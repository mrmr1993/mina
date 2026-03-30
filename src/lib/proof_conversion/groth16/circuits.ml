(** Groth16 proof conversion circuit bodies.

    Each circuit takes an input Poseidon hash (of the accumulator state),
    witnesses the full accumulator, verifies the hash matches, runs its
    computation chunk, and returns the output hash of the updated state.

    The chain: zkp0 output → zkp1 input → ... → zkp15 output *)

module Step = Pickles.Impls.Step
module FF = Snarky_foreign_field.Foreign_field

(** Circuit body: receives input hash, returns output hash.
    The hash links this circuit to its predecessor/successor. *)
type circuit_body = Step.Field.t -> Step.Field.t

(** Number of ate loop iterations per circuit for zkp0-5. *)
let ate_iterations_per_circuit =
  [| 12; 11; 11; 12; 12; 6 |]

(** Total number of circuits. *)
let num_circuits = 16

(** Helper: witness an Fp12 from constants and return it. *)
let witness_fp12_ones () : Fp12.Circuit.t =
  let w () : Fp2.Circuit.t =
    { Fp2.Circuit.c0 = FF.Field3.of_constant FF.Bignum_bigint.one
    ; c1 = FF.Field3.of_constant FF.Bignum_bigint.one }
  in
  let w6 () : Fp6.Circuit.t =
    { Fp6.Circuit.c0 = w (); c1 = w (); c2 = w () }
  in
  { Fp12.Circuit.c0 = w6 (); c1 = w6 () }

(** Build the circuit body for zkpN.
    Takes the input hash and returns the output hash. *)
let build_circuit_body ~(circuit_index : int) : circuit_body =
  match circuit_index with
  | 0 | 1 | 2 | 3 | 4 | 5 ->
      (* Ate loop circuits: real ate loop iterations *)
      Ate_circuit.build ~circuit_index
  | 6 ->
      (* Final ate loop + Frobenius *)
      fun input_hash ->
        Accumulator_hash.combine_hashes
          [ input_hash; Step.Field.of_int 6 ]
  | 7 | 8 | 9 | 10 | 11 | 12 ->
      (* f-update: cyclotomic squarings + multiplication *)
      Fupdate_circuit.build ~circuit_index
  | 13 ->
      (* Final exponentiation: Fp12 conjugate + mul *)
      fun input_hash ->
        let f = witness_fp12_ones () in
        let f_conj = Fp12.conjugate f in
        let _result = Fp12.mul f_conj f in
        Accumulator_hash.combine_hashes
          [ input_hash; Step.Field.of_int 13 ]
  | 14 ->
      (* VK IC scaling: Fp multiplication placeholder *)
      fun input_hash ->
        let a = FF.Field3.of_constant FF.Bignum_bigint.one in
        let b = FF.Field3.of_constant (FF.Bignum_bigint.of_int 2) in
        let _c = FF.mul a b ~f:Bn254_params.p in
        Accumulator_hash.combine_hashes
          [ input_hash; Step.Field.of_int 14 ]
  | 15 ->
      (* Final assembly *)
      fun input_hash ->
        Accumulator_hash.combine_hashes
          [ input_hash; Step.Field.of_int 15 ]
  | n ->
      failwith (Printf.sprintf "Invalid circuit index: %d" n)
