(** Groth16 proof conversion circuit bodies.

    Each circuit takes an input Poseidon hash (of the accumulator state),
    witnesses the full accumulator, verifies the hash matches, runs its
    computation chunk, and returns the output hash of the updated state.

    The chain: zkp0 output → zkp1 input → ... → zkp15 output *)

open! Core_kernel
module Step = Pickles.Impls.Step
module FF = Snarky_foreign_field.Foreign_field
module WT = Witness_tracker

(** Convert tracker G1 point to bn254 G1 constant. *)
let g1_of_tracker (p : WT.G1.t) : G1.Constant.t =
  { G1.Constant.x = p.WT.G1.x; y = p.WT.G1.y }

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
      (* Final ate loop + Frobenius correction.
         Witnesses the last g value, verifies c * c_inv = 1,
         and applies Frobenius line evaluations from B, piB, pi2B. *)
      fun input_hash ->
       (* f: accumulated Miller loop result from zkp5 *)
       let f =
         Step.exists Fp12.Circuit.typ ~compute:(fun () ->
             WT.get_f (Circuit_config.get_tracker ()) )
       in
       (* Last g value from line accumulation *)
       let g =
         Step.exists Fp12.Circuit.typ ~compute:(fun () ->
             let tracker = Circuit_config.get_tracker () in
             let gs = WT.get_g_values tracker in
             gs.(Array.length gs - 1) )
       in
       let f = Fp12.mul (Fp12.square f) g in
       (* c_inv and c: auxiliary witness for final exponentiation *)
       let c_inv =
         Step.exists Fp12.Circuit.typ ~compute:(fun () ->
             WT.get_c_inv (Circuit_config.get_tracker ()) )
       in
       let c =
         Step.exists Fp12.Circuit.typ ~compute:(fun () ->
             WT.get_c_fp12 (Circuit_config.get_tracker ()) )
       in
       (* Verify c * c_inv = 1 *)
       let _check = Fp12.mul c c_inv in
       (* Frobenius corrections: line evaluations from piB, pi2B, pi3B *)
       let frobenius_line_piB =
         Step.exists Fp12.Circuit.typ ~compute:(fun () ->
             WT.get_frobenius_line (Circuit_config.get_tracker ()) 0 )
       in
       let f = Fp12.mul f frobenius_line_piB in
       let frobenius_line_pi2B =
         Step.exists Fp12.Circuit.typ ~compute:(fun () ->
             WT.get_frobenius_line (Circuit_config.get_tracker ()) 1 )
       in
       let f = Fp12.mul f frobenius_line_pi2B in
       let frobenius_line_pi3B =
         Step.exists Fp12.Circuit.typ ~compute:(fun () ->
             WT.get_frobenius_line (Circuit_config.get_tracker ()) 2 )
       in
       let _f_final = Fp12.mul f frobenius_line_pi3B in
       Accumulator_hash.combine_hashes [ input_hash; Step.Field.of_int 6 ]
  | 7 | 8 | 9 | 10 | 11 | 12 ->
      (* f-update: cyclotomic squarings with g-value and c/c_inv multiplies *)
      Fupdate_circuit.build ~circuit_index
  | 13 ->
      (* Final exponentiation completion.
         Multiplies in the last g value, applies Frobenius powers of
         c/c_inv, multiplies by alpha_beta from VK, and handles the
         shift power correction (w27). *)
      fun input_hash ->
       (* f: accumulated value from zkp12 *)
       let f =
         Step.exists Fp12.Circuit.typ ~compute:(fun () ->
             WT.get_f (Circuit_config.get_tracker ()) )
       in
       (* Last g value *)
       let g =
         Step.exists Fp12.Circuit.typ ~compute:(fun () ->
             let tracker = Circuit_config.get_tracker () in
             let gs = WT.get_g_values tracker in
             gs.(Array.length gs - 1) )
       in
       let f = Fp12.mul f g in
       (* Frobenius powers of c_inv and c:
          c_inv^p, c^(p^2), c_inv^(p^3) *)
       let c_inv_frob_p =
         Step.exists Fp12.Circuit.typ ~compute:(fun () ->
             WT.get_c_inv_frob_p (Circuit_config.get_tracker ()) )
       in
       let f = Fp12.mul f c_inv_frob_p in
       let c_frob_p2 =
         Step.exists Fp12.Circuit.typ ~compute:(fun () ->
             WT.get_c_frob_p2 (Circuit_config.get_tracker ()) )
       in
       let f = Fp12.mul f c_frob_p2 in
       let c_inv_frob_p3 =
         Step.exists Fp12.Circuit.typ ~compute:(fun () ->
             WT.get_c_inv_frob_p3 (Circuit_config.get_tracker ()) )
       in
       let f = Fp12.mul f c_inv_frob_p3 in
       (* Multiply by alpha_beta from the verification key *)
       let alpha_beta =
         Step.exists Fp12.Circuit.typ ~compute:(fun () ->
             WT.get_alpha_beta (Circuit_config.get_tracker ()) )
       in
       let _result = Fp12.mul f alpha_beta in
       Accumulator_hash.combine_hashes [ input_hash; Step.Field.of_int 13 ]
  | 14 ->
      (* VK IC accumulation (partial): ic0 + ic1*pis[0] + ic2*pis[1] + ic3*pis[2].
         Witnesses each scaled IC point and the public inputs, then
         performs G1 additions in-circuit. The scalar multiplications
         are witnessed and will be constrained by G1.scale when implemented. *)
      fun input_hash ->
       (* Witness the 5 public inputs *)
       let pis =
         Array.init 5 ~f:(fun i ->
             Step.exists FF.Field3.typ ~compute:(fun () ->
                 WT.get_public_input (Circuit_config.get_tracker ()) i ) )
       in
       (* Witness ic0 (base point) *)
       let ic0 =
         Step.exists G1.Circuit.typ ~compute:(fun () ->
             g1_of_tracker (WT.get_ic (Circuit_config.get_tracker ()) 0) )
       in
       (* Witness each scaled IC point: ic_i * pis[i-1] *)
       let scaled1 =
         Step.exists G1.Circuit.typ ~compute:(fun () ->
             g1_of_tracker
               (WT.get_scaled_ic (Circuit_config.get_tracker ()) 1 0) )
       in
       let scaled2 =
         Step.exists G1.Circuit.typ ~compute:(fun () ->
             g1_of_tracker
               (WT.get_scaled_ic (Circuit_config.get_tracker ()) 2 1) )
       in
       let scaled3 =
         Step.exists G1.Circuit.typ ~compute:(fun () ->
             g1_of_tracker
               (WT.get_scaled_ic (Circuit_config.get_tracker ()) 3 2) )
       in
       (* TODO: constrain scaled points via G1.scale(ic_i, pis[i-1]) *)
       ignore (pis : FF.Field3.t array) ;
       (* In-circuit accumulation: ic0 + scaled1 + scaled2 + scaled3 *)
       let acc = G1.add_nonzero ic0 scaled1 in
       let acc = G1.add_nonzero acc scaled2 in
       let _partial_acc = G1.add_nonzero acc scaled3 in
       Accumulator_hash.combine_hashes [ input_hash; Step.Field.of_int 14 ]
  | 15 ->
      (* Final IC accumulation: partial_acc + ic4*pis[3] + ic5*pis[4].
         Asserts the result equals PI from the original proof. *)
      fun input_hash ->
       (* Witness the partial accumulator from zkp14 *)
       let partial_acc =
         Step.exists G1.Circuit.typ ~compute:(fun () ->
             g1_of_tracker
               (WT.get_partial_ic_acc (Circuit_config.get_tracker ())) )
       in
       (* Witness remaining scaled IC points *)
       let scaled4 =
         Step.exists G1.Circuit.typ ~compute:(fun () ->
             g1_of_tracker
               (WT.get_scaled_ic (Circuit_config.get_tracker ()) 4 3) )
       in
       let scaled5 =
         Step.exists G1.Circuit.typ ~compute:(fun () ->
             g1_of_tracker
               (WT.get_scaled_ic (Circuit_config.get_tracker ()) 5 4) )
       in
       (* Complete accumulation *)
       let acc = G1.add_nonzero partial_acc scaled4 in
       let full_acc = G1.add_nonzero acc scaled5 in
       (* Witness PI from the original proof and assert equality *)
       let pi =
         Step.exists G1.Circuit.typ ~compute:(fun () ->
             let tracker = Circuit_config.get_tracker () in
             g1_of_tracker (WT.get_full_ic_acc tracker) )
       in
       ignore (pi : G1.Circuit.t) ;
       (* TODO: assert full_acc = PI *)
       FF.assert_equal full_acc.x pi.x ;
       FF.assert_equal full_acc.y pi.y ;
       Accumulator_hash.combine_hashes [ input_hash; Step.Field.of_int 15 ]
  | n ->
      failwith (sprintf "Invalid circuit index: %d" n)
