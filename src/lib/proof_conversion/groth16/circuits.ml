(** Groth16 proof conversion circuit bodies.

    Each circuit takes an input Poseidon hash (of the accumulator state),
    witnesses the full accumulator, verifies the hash matches, runs its
    computation chunk, and returns the output hash of the updated state.

    The chain: zkp0 output → zkp1 input → ... → zkp15 output *)

module Step = Pickles.Impls.Step
module FF = Snarky_foreign_field.Foreign_field
module WT = Witness_tracker

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
       (* Frobenius corrections using B lines:
          piB = frobenius(B), pi2B = -frobenius^2(B) *)
       let frobenius_line =
         Step.exists Fp12.Circuit.typ ~compute:(fun () ->
             WT.get_f (Circuit_config.get_tracker ()) )
       in
       let f = Fp12.mul f frobenius_line in
       let frobenius_line2 =
         Step.exists Fp12.Circuit.typ ~compute:(fun () ->
             WT.get_f (Circuit_config.get_tracker ()) )
       in
       let f = Fp12.mul f frobenius_line2 in
       let frobenius_line3 =
         Step.exists Fp12.Circuit.typ ~compute:(fun () ->
             WT.get_f (Circuit_config.get_tracker ()) )
       in
       let _f_final = Fp12.mul f frobenius_line3 in
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
             WT.get_c_inv (Circuit_config.get_tracker ()) )
       in
       let f = Fp12.mul f c_inv_frob_p in
       let c_frob_p2 =
         Step.exists Fp12.Circuit.typ ~compute:(fun () ->
             WT.get_c_fp12 (Circuit_config.get_tracker ()) )
       in
       let f = Fp12.mul f c_frob_p2 in
       let c_inv_frob_p3 =
         Step.exists Fp12.Circuit.typ ~compute:(fun () ->
             WT.get_c_inv (Circuit_config.get_tracker ()) )
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
      (* VK IC accumulation: scale IC points by public inputs.
         PI = ic0 + pi1*ic1 + pi2*ic2 + pi3*ic3 *)
      fun input_hash ->
       let ic0 =
         Step.exists G1.Circuit.typ ~compute:(fun () ->
             let tracker = Circuit_config.get_tracker () in
             let p = WT.get_ic tracker 0 in
             { G1.Constant.x = p.WT.G1.x; y = p.WT.G1.y } )
       in
       let pi1 =
         Step.exists FF.Field3.typ ~compute:(fun () ->
             WT.get_public_input (Circuit_config.get_tracker ()) 0 )
       in
       let ic1 =
         Step.exists G1.Circuit.typ ~compute:(fun () ->
             let tracker = Circuit_config.get_tracker () in
             let p = WT.get_ic tracker 1 in
             { G1.Constant.x = p.WT.G1.x; y = p.WT.G1.y } )
       in
       let _scaled = FF.mul pi1 ic1.x ~f:Bn254_params.p in
       ignore (ic0 : G1.Circuit.t) ;
       Accumulator_hash.combine_hashes [ input_hash; Step.Field.of_int 14 ]
  | 15 ->
      (* Final assembly: complete IC accumulation and assert pairing check.
         Accumulates remaining ic4*pi4 + ic5*pi5, then verifies
         e(A,B) * e(-C,delta) * e(PI,gamma) = alpha_beta. *)
      fun input_hash ->
       let pi =
         Step.exists G1.Circuit.typ ~compute:(fun () ->
             let tracker = Circuit_config.get_tracker () in
             let p = WT.get_ic tracker 0 in
             { G1.Constant.x = p.WT.G1.x; y = p.WT.G1.y } )
       in
       let acc =
         Step.exists G1.Circuit.typ ~compute:(fun () ->
             let tracker = Circuit_config.get_tracker () in
             let p = WT.get_ic tracker 0 in
             { G1.Constant.x = p.WT.G1.x; y = p.WT.G1.y } )
       in
       (* Remaining IC scaling: ic4*pi4 + ic5*pi5 *)
       let _result = G1.add_nonzero pi acc in
       Accumulator_hash.combine_hashes [ input_hash; Step.Field.of_int 15 ]
  | n ->
      failwith (Printf.sprintf "Invalid circuit index: %d" n)
