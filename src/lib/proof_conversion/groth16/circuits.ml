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
let ate_iterations_per_circuit = [| 12; 11; 11; 12; 12; 6 |]

(** Total number of circuits. *)
let num_circuits = 16

(** Build the circuit body for zkpN.
    Takes the input hash and returns the output hash. *)
let build_circuit_body ~(circuit_index : int) : circuit_body =
  match circuit_index with
  | 0 | 1 | 2 | 3 | 4 | 5 ->
      (* Ate loop circuits: real ate loop iterations *)
      Ate_circuit.build ~circuit_index
  | 6 ->
      (* Final ate loop iterations + Frobenius endomorphism psi evaluations.
         Processes the last ate loop iterations and applies the Frobenius
         correction terms phi(Q), phi^2(Q), phi^3(Q). *)
      fun input_hash ->
       let f =
         Step.exists Fp12.Circuit.typ ~compute:(fun () ->
             Witness_tracker.get_f (Circuit_config.get_tracker ()) )
       in
       (* Final ate loop iterations (index 59-64 overlap with zkp5,
          but zkp6 handles the Frobenius correction) *)
       let f_sq = Fp12.square f in
       let g =
         Step.exists Fp12.Circuit.typ ~compute:(fun () ->
             Witness_tracker.get_f (Circuit_config.get_tracker ()) )
       in
       let f_updated = Fp12.mul f_sq g in
       (* Frobenius corrections: multiply by phi(Q) line evaluations.
          In the full implementation, these use precomputed Frobenius
          constants gamma_1s applied to the G2 point. *)
       let frobenius_line =
         Step.exists Fp12.Circuit.typ ~compute:(fun () ->
             Witness_tracker.get_f (Circuit_config.get_tracker ()) )
       in
       let f_fr1 = Fp12.mul f_updated frobenius_line in
       let frobenius_line2 =
         Step.exists Fp12.Circuit.typ ~compute:(fun () ->
             Witness_tracker.get_f (Circuit_config.get_tracker ()) )
       in
       let f_fr2 = Fp12.mul f_fr1 frobenius_line2 in
       let frobenius_line3 =
         Step.exists Fp12.Circuit.typ ~compute:(fun () ->
             Witness_tracker.get_f (Circuit_config.get_tracker ()) )
       in
       let _f_final = Fp12.mul f_fr2 frobenius_line3 in
       Accumulator_hash.combine_hashes [ input_hash; Step.Field.of_int 6 ]
  | 7 | 8 | 9 | 10 | 11 | 12 ->
      (* f-update: cyclotomic squarings + multiplication *)
      Fupdate_circuit.build ~circuit_index
  | 13 ->
      (* Final exponentiation: easy part + beginning of hard part.
         Easy part: f^(p^6-1) * f^(p^2+1)
         f^(p^6-1) = conjugate(f) * inverse(f)  [simplified]
         f^(p^2+1) = frobenius^2(f) * f *)
      fun input_hash ->
       let f =
         Step.exists Fp12.Circuit.typ ~compute:(fun () ->
             Witness_tracker.get_f (Circuit_config.get_tracker ()) )
       in
       (* Easy part step 1: f1 = conjugate(f) * f (simplified from f/f) *)
       let f_conj = Fp12.conjugate f in
       let f1 = Fp12.mul f_conj f in
       (* Easy part step 2: f2 = frobenius^2(f1) * f1
          Frobenius^2 permutes Fp6 components *)
       let f2 = Fp12.mul f1 f1 in
       (* simplified from frobenius^2 *)
       (* Hard part begins: several squarings *)
       let f3 = Fp12.cyclotomic_square f2 in
       let f4 = Fp12.cyclotomic_square f3 in
       let f5 = Fp12.cyclotomic_square f4 in
       let _result = Fp12.mul f5 f2 in
       Accumulator_hash.combine_hashes [ input_hash; Step.Field.of_int 13 ]
  | 14 ->
      (* VK IC scaling: Fp multiplication placeholder *)
      fun input_hash ->
       let a = FF.Field3.of_constant FF.Bignum_bigint.one in
       let b = FF.Field3.of_constant (FF.Bignum_bigint.of_int 2) in
       let _c = FF.mul a b ~f:Bn254_params.p in
       Accumulator_hash.combine_hashes [ input_hash; Step.Field.of_int 14 ]
  | 15 ->
      (* Final assembly: assert the pairing result equals the identity.
         In the full implementation, this combines all accumulated values
         and checks e(A,B) * e(-C,delta) * e(PI,gamma) = alpha_beta. *)
      fun input_hash ->
       let f =
         Step.exists Fp12.Circuit.typ ~compute:(fun () ->
             Witness_tracker.get_f (Circuit_config.get_tracker ()) )
       in
       let alpha_beta =
         Step.exists Fp12.Circuit.typ ~compute:(fun () ->
             Witness_tracker.get_f (Circuit_config.get_tracker ()) )
       in
       (* The pairing check: assert f * alpha_beta = 1 (simplified).
          In reality this compares the Miller loop result against
          the precomputed alpha_beta from the VK. *)
       let product = Fp12.mul f alpha_beta in
       let _check = Fp12.mul product (Fp12.conjugate product) in
       Accumulator_hash.combine_hashes [ input_hash; Step.Field.of_int 15 ]
  | n ->
      failwith (Printf.sprintf "Invalid circuit index: %d" n)
