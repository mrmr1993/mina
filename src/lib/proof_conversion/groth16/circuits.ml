(** Groth16 proof conversion circuit bodies.

    Each of the 16 circuits (zkp0-zkp15) processes a portion of the
    Groth16 verification:

    zkp0-5:   Ate loop iterations (Miller loop chunks)
    zkp6:     Final ate loop + Frobenius psi evaluations
    zkp7-12:  Fp12 exponentiation (f-update) steps
    zkp13:    Final exponentiation
    zkp14:    VK IC point scaling via MSM/GLV
    zkp15:    Final accumulator assembly

    Each circuit takes the accumulator hash as public input, witnesses
    the full accumulator, runs its computation, and outputs the
    updated accumulator hash.

    Reference: nori-proof-conversion/src/groth/recursion/prove_zkps.ts *)

module Step = Pickles.Impls.Step

(** Circuit body type: takes unit (accumulator is witnessed internally)
    and returns unit (output hash is asserted). *)
type circuit_body = unit -> unit

(** Number of ate loop iterations per circuit for zkp0-5.
    Total iterations = 64 (ATE_LOOP_COUNT length - 1). *)
let ate_iterations_per_circuit =
  [| 12; 11; 11; 12; 12; 6 |]

(** Build the circuit body for zkpN.
    Each body:
    1. Witnesses the accumulator via exists
    2. Asserts the input hash matches the witnessed accumulator
    3. Runs the circuit-specific computation
    4. Outputs the updated accumulator hash *)
let build_circuit_body ~(circuit_index : int) : circuit_body =
  match circuit_index with
  | 0 | 1 | 2 | 3 | 4 | 5 ->
      (* Ate loop circuits — witness Fp12, perform one mul as placeholder *)
      fun () ->
        let _iters = ate_iterations_per_circuit.(circuit_index) in
        (* Witness two Fp12 values and multiply them.
           This exercises the full tower field arithmetic in-circuit. *)
        let module FF = Snarky_foreign_field.Foreign_field in
        let witness_fp12 () : Fp12.Circuit.t =
          let w () : Fp2.Circuit.t =
            let w1 () =
              FF.Field3.of_constant FF.Bignum_bigint.zero
            in
            { Fp2.Circuit.c0 = w1 (); c1 = w1 () }
          in
          let w6 () : Fp6.Circuit.t =
            { Fp6.Circuit.c0 = w (); c1 = w (); c2 = w () }
          in
          { Fp12.Circuit.c0 = w6 (); c1 = w6 () }
        in
        let a = witness_fp12 () in
        let b = witness_fp12 () in
        let _c = Fp12.mul a b in
        ()
  | 6 ->
      (* Final ate loop + Frobenius — stub *)
      fun () -> ()
  | 7 | 8 | 9 | 10 | 11 | 12 ->
      (* f-update circuits — stub *)
      fun () -> ()
  | 13 ->
      (* Final exponentiation — stub *)
      fun () -> ()
  | 14 ->
      (* VK IC scaling — stub *)
      fun () -> ()
  | 15 ->
      (* Final assembly — stub *)
      fun () -> ()
  | n ->
      failwith (Printf.sprintf "Invalid circuit index: %d" n)

(** Total number of circuits in the Groth16 proof conversion. *)
let num_circuits = 16
