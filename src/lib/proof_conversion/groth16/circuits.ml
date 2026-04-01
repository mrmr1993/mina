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

(** Number of ate loop iterations per circuit for zkp0-6.
    Matches nori: [1,10), [10,20), [20,30), [30,40), [40,50), [50,59), [59,65) *)
let ate_iterations_per_circuit = [| 9; 10; 10; 10; 10; 9; 6 |]

(** Total number of circuits. *)
let num_circuits = 16

(** Witness the accumulator and verify the input hash matches. *)
let witness_and_verify_acc (input_hash : Step.Field.t) : Accumulator.Circuit.t =
  let acc =
    Step.exists Accumulator.typ ~compute:(fun () ->
        WT.get_accumulator_constant (Circuit_config.get_tracker ()) )
  in
  let acc_hash = Accumulator.hash acc in
  Step.Field.Assert.equal input_hash acc_hash ;
  acc

(** Hash an accumulator with an updated f value. *)
let hash_with_updated_f (acc : Accumulator.Circuit.t) (f : Fp12.Circuit.t) :
    Step.Field.t =
  let updated : Accumulator.Circuit.t =
    { proof = acc.proof; state = { acc.state with f } }
  in
  Accumulator.hash updated

(** Conditional Fp12 selection for shift_power. *)
let select_fp12 (cond : Step.Boolean.var) (a : Fp12.Circuit.t)
    (b : Fp12.Circuit.t) : Fp12.Circuit.t =
  let sel (x : FF.Field3.t) (y : FF.Field3.t) : FF.Field3.t =
    let x0, x1, x2 = x in
    let y0, y1, y2 = y in
    ( Step.Field.if_ cond ~then_:x0 ~else_:y0
    , Step.Field.if_ cond ~then_:x1 ~else_:y1
    , Step.Field.if_ cond ~then_:x2 ~else_:y2 )
  in
  let sel_fpa (x : FF.FpA.t) (y : FF.FpA.t) : FF.FpA.t =
    FF.FpA.of_field3_unsafe (sel (FF.FpA.to_field3 x) (FF.FpA.to_field3 y))
  in
  let sel_fp2 (x : Fp2.Circuit.t) (y : Fp2.Circuit.t) : Fp2.Circuit.t =
    { Fp2.Circuit.c0 = sel_fpa x.c0 y.c0; c1 = sel_fpa x.c1 y.c1 }
  in
  let sel_fp6 (x : Fp6.Circuit.t) (y : Fp6.Circuit.t) : Fp6.Circuit.t =
    { Fp6.Circuit.c0 = sel_fp2 x.c0 y.c0
    ; c1 = sel_fp2 x.c1 y.c1
    ; c2 = sel_fp2 x.c2 y.c2
    }
  in
  { Fp12.Circuit.c0 = sel_fp6 a.c0 b.c0; c1 = sel_fp6 a.c1 b.c1 }

(** Hash a G1 point's field elements (for zkp13 → zkp14 transition).
    Matches nori's Poseidon.hashPacked(G1Affine, pi). *)
let hash_g1 (pt : G1.Circuit.t) : Step.Field.t =
  let l0_x, l1_x, l2_x = FF.FpA.to_field3 pt.x in
  let l0_y, l1_y, l2_y = FF.FpA.to_field3 pt.y in
  Accumulator_hash.poseidon_hash [| l0_x; l1_x; l2_x; l0_y; l1_y; l2_y |]

(** Convert VK constant lines to circuit constants (embedded in the
    constraint system, not witnesses).  Called at circuit definition
    time, outside the proving closure. *)
let vk_lines_to_circuit (lines : WT.Line.t array) : Lines.G2Line.t array =
  Array.map lines ~f:(fun l ->
      Lines.G2Line.of_constant (l.WT.Line.lambda, l.WT.Line.neg_mu) )

(** Build the circuit body for zkpN.
    [vk] provides precomputed VK constants (delta/gamma lines etc.)
    that are embedded as circuit constants, not witnesses.
    Takes the input hash and returns the output hash. *)
let build_circuit_body ~(vk : Vk_constants.t) ~(circuit_index : int) :
    circuit_body =
  (* Convert VK lines to circuit constants at definition time,
     matching nori's module-level: const delta_lines = LineParser.parse(...) *)
  let delta_lines_const = vk_lines_to_circuit vk.delta_lines in
  let gamma_lines_const = vk_lines_to_circuit vk.gamma_lines in
  match circuit_index with
  | 0 | 1 | 2 | 3 | 4 | 5 ->
      (* Ate loop circuits: witness all private inputs up front (matching
         nori's privateInputs: [Accumulator, Array(Field, N), Array(G2Line, 91)]),
         then run constraints and output hash. *)
      fun input_hash ->
       let acc =
         Step.exists Accumulator.typ ~compute:(fun () ->
             WT.get_accumulator_constant (Circuit_config.get_tracker ()) )
       in
       let n_total = Array.length Bn254_params.ate_loop_count in
       let lines_hashes =
         Array.init n_total ~f:(fun i ->
             Step.exists Step.Field.typ ~compute:(fun () ->
                 (WT.get_line_hashes (Circuit_config.get_tracker ())).(i) ) )
       in
       let all_b_lines =
         (* +2 for frobenius lines. *)
         Array.init (Ate_circuit.total_b_lines + 2) ~f:(fun i ->
             Step.exists Lines.G2Line.typ ~compute:(fun () ->
                 let line =
                   (WT.get_all_b_lines (Circuit_config.get_tracker ())).(i)
                 in
                 (line.WT.Line.lambda, line.WT.Line.neg_mu) ) )
       in
       let acc_hash = Accumulator.hash acc in
       Step.Field.Assert.equal input_hash acc_hash ;
       let acc =
         if circuit_index = 0 then
           { acc with state = { acc.state with t_point = acc.proof.b } }
         else acc
       in
       (* Verify lines_hashes against g_digest *)
       let digest = Array_list_hasher.hash lines_hashes in
       Step.Field.Assert.equal acc.state.g_digest digest ;
       (* Compute affine caches *)
       let a_cache = Lines.AffineCache.make acc.proof.neg_a in
       let c_cache = Lines.AffineCache.make acc.proof.c in
       let pi_cache = Lines.AffineCache.make acc.proof.pi in
       let caches : Ate_circuit.three_cache = { a_cache; c_cache; pi_cache } in
       let begin_idx, end_idx = Ate_circuit.circuit_ranges.(circuit_index) in
       let neg_b = G2.negate acc.proof.b in
       let offset = Ate_circuit.b_line_offset ~begin_idx in
       let count = Ate_circuit.b_line_count ~from:begin_idx ~to_:end_idx in
       let b_lines = Array.sub all_b_lines ~pos:offset ~len:count in
       let delta_slice = Array.sub delta_lines_const ~pos:offset ~len:count in
       let gamma_slice = Array.sub gamma_lines_const ~pos:offset ~len:count in
       let t_updated =
         Ate_circuit.run_circuit_chunk ~t_point:acc.state.t_point
           ~b_point:acc.proof.b ~neg_b ~begin_idx ~end_idx ~b_lines
           ~delta_lines:delta_slice ~gamma_lines:gamma_slice ~lines_hashes
           ~caches
       in
       (* Compute the updated g_digest *)
       let new_g_digest = Array_list_hasher.hash lines_hashes in
       let updated : Accumulator.Circuit.t =
         { proof = acc.proof
         ; state =
             { acc.state with g_digest = new_g_digest; t_point = t_updated }
         }
       in
       Accumulator.hash updated
  | 6 ->
      (* Ate loop [59,65) + Frobenius correction.
         Runs the final 6 ate iterations, then applies Frobenius line
         evaluations. Verifies c * c_inv = 1. Updates g_digest with
         both ate g values and the Frobenius g hash.
         Matches nori's zkp6.ts. *)
      fun input_hash ->
       let acc =
         Step.exists Accumulator.typ ~compute:(fun () ->
             WT.get_accumulator_constant (Circuit_config.get_tracker ()) )
       in
       let n_total = Array.length Bn254_params.ate_loop_count in
       let lines_hashes =
         Array.init n_total ~f:(fun i ->
             Step.exists Step.Field.typ ~compute:(fun () ->
                 (WT.get_line_hashes (Circuit_config.get_tracker ())).(i) ) )
       in
       let all_b_lines =
         (* +2 for frobenius lines at the end, matching nori's 91-element array *)
         Array.init (Ate_circuit.total_b_lines + 2) ~f:(fun i ->
             Step.exists Lines.G2Line.typ ~compute:(fun () ->
                 let line =
                   (WT.get_all_b_lines (Circuit_config.get_tracker ())).(i)
                 in
                 (line.WT.Line.lambda, line.WT.Line.neg_mu) ) )
       in
       let acc_hash = Accumulator.hash acc in
       Step.Field.Assert.equal input_hash acc_hash ;
       (* Verify lines_hashes against g_digest *)
       let digest = Array_list_hasher.hash lines_hashes in
       Step.Field.Assert.equal acc.state.g_digest digest ;
       (* Compute affine caches (shared between ate loop and frobenius) *)
       let a_cache = Lines.AffineCache.make acc.proof.neg_a in
       let c_cache = Lines.AffineCache.make acc.proof.c in
       let pi_cache = Lines.AffineCache.make acc.proof.pi in
       let caches : Ate_circuit.three_cache = { a_cache; c_cache; pi_cache } in
       let begin_idx, end_idx = Ate_circuit.circuit_ranges.(6) in
       let neg_b = G2.negate acc.proof.b in
       let offset = Ate_circuit.b_line_offset ~begin_idx in
       let count = Ate_circuit.b_line_count ~from:begin_idx ~to_:end_idx in
       let b_lines = Array.sub all_b_lines ~pos:offset ~len:count in
       let delta_slice = Array.sub delta_lines_const ~pos:offset ~len:count in
       let gamma_slice = Array.sub gamma_lines_const ~pos:offset ~len:count in
       (* Run ate loop iterations [59,65) *)
       let t_after_ate =
         Ate_circuit.run_circuit_chunk ~t_point:acc.state.t_point
           ~b_point:acc.proof.b ~neg_b ~begin_idx ~end_idx ~b_lines
           ~delta_lines:delta_slice ~gamma_lines:gamma_slice ~lines_hashes
           ~caches
       in
       (* Frobenius part — matches nori's zkp6.ts frobenius section.
          Uses sparse_mul (not full Fp12.mul) for line evaluations.
          Does NOT update f. *)
       let n_b = Array.length all_b_lines in
       (* Frobenius delta/gamma lines are VK constants (last 2 elements) *)
       let frob_b_lines = [| all_b_lines.(n_b - 2); all_b_lines.(n_b - 1) |] in
       let n_d = Array.length delta_lines_const in
       let frob_delta_lines =
         [| delta_lines_const.(n_d - 2); delta_lines_const.(n_d - 1) |]
       in
       let n_g = Array.length gamma_lines_const in
       let frob_gamma_lines =
         [| gamma_lines_const.(n_g - 2); gamma_lines_const.(n_g - 1) |]
       in
       (* First Frobenius line: g = psi(b) * psi(delta) * psi(gamma) *)
       let g = Lines.psi frob_b_lines.(0) a_cache in
       let g = Fp12.sparse_mul g (Lines.psi frob_delta_lines.(0) c_cache) in
       let g = Fp12.sparse_mul g (Lines.psi frob_gamma_lines.(0) pi_cache) in
       (* piB = B.frobenius(); assert line passes through (T, piB) *)
       let piB = G2.frobenius acc.proof.b in
       let t_point = t_after_ate in
       Lines.assert_is_line frob_b_lines.(0) t_point piB ;
       let t_point =
         G2.add_from_line t_point ~lambda:frob_b_lines.(0).lambda piB
       in
       (* Second Frobenius line *)
       let pi2B = piB |> G2.negative_frobenius in
       Lines.assert_is_line frob_b_lines.(1) t_point pi2B ;
       let g = Fp12.sparse_mul g (Lines.psi frob_b_lines.(1) a_cache) in
       let g = Fp12.sparse_mul g (Lines.psi frob_delta_lines.(1) c_cache) in
       let g = Fp12.sparse_mul g (Lines.psi frob_gamma_lines.(1) pi_cache) in
       (* Verify c * c_inv = 1 *)
       let product = Fp12.mul acc.proof.c_fp12 acc.proof.c_inv in
       Fp12.assert_one product ;
       (* Hash frobenius g into lines_hashes and compute final g_digest *)
       let n_total = Array.length Bn254_params.ate_loop_count in
       lines_hashes.(n_total - 1) <- Accumulator_hash.hash_fp12 g ;
       let final_g_digest = Array_list_hasher.hash lines_hashes in
       let updated : Accumulator.Circuit.t =
         { proof = acc.proof
         ; state = { acc.state with g_digest = final_g_digest; t_point }
         }
       in
       Accumulator.hash updated
  | 7 | 8 | 9 | 10 | 11 | 12 ->
      (* f-update: cyclotomic squarings with g-value and c/c_inv multiplies *)
      Fupdate_circuit.build ~circuit_index
  | 13 ->
      (* Final exponentiation completion.
         Multiplies in the last g value, applies Frobenius powers of
         c/c_inv, multiplies by alpha_beta from VK, handles shift_power.
         Outputs hash(G1Affine, acc.proof.PI) — domain transition. *)
      fun input_hash ->
       let acc = witness_and_verify_acc input_hash in
       let f = acc.state.f in
       (* Last g value — opened from g_digest *)
       let n_total = Array.length Bn254_params.ate_loop_count in
       let g_idx = n_total - 1 in
       let g =
         Step.exists Fp12.Circuit.typ ~compute:(fun () ->
             let tracker = Circuit_config.get_tracker () in
             let gs = WT.get_g_values tracker in
             gs.(Array.length gs - 1) )
       in
       (* Verify g_digest: open(lhs_64, [g], []) *)
       let lhs_hashes =
         Array.init g_idx ~f:(fun i ->
             Step.exists Step.Field.typ ~compute:(fun () ->
                 (WT.get_line_hashes (Circuit_config.get_tracker ())).(i) ) )
       in
       let opening =
         Array_list_hasher.open_ ~lhs:lhs_hashes ~opening:[| g |] ~rhs:[||]
       in
       Step.Field.Assert.equal acc.state.g_digest opening ;
       let f = Fp12.mul f g in
       (* Frobenius powers of c_inv and c *)
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
       let f = Fp12.mul f alpha_beta in
       (* Apply shift_power correction: multiply by w27^shift_power *)
       let w27 =
         Step.exists Fp12.Circuit.typ ~compute:(fun () ->
             WT.get_w27 (Circuit_config.get_tracker ()) )
       in
       let w27_sq =
         Step.exists Fp12.Circuit.typ ~compute:(fun () ->
             WT.get_w27_square (Circuit_config.get_tracker ()) )
       in
       let is_0 =
         Step.Field.equal acc.proof.shift_power (Step.Field.of_int 0)
       in
       let is_1 =
         Step.Field.equal acc.proof.shift_power (Step.Field.of_int 1)
       in
       let is_2 =
         Step.Field.equal acc.proof.shift_power (Step.Field.of_int 2)
       in
       Step.Boolean.Assert.is_true
         (Step.Boolean.( ||| ) is_0 (Step.Boolean.( ||| ) is_1 is_2)) ;
       let f_shifted_1 = Fp12.mul f w27 in
       let f_shifted_2 = Fp12.mul f w27_sq in
       let result = select_fp12 is_1 f_shifted_1 f in
       let result = select_fp12 is_2 f_shifted_2 result in
       (* Assert the final result equals Fp12.one — the pairing check *)
       Fp12.assert_one result ;
       (* Domain transition: output hash of PI point, not accumulator.
          Matches nori: return Poseidon.hashPacked(G1Affine, acc.proof.PI) *)
       hash_g1 acc.proof.pi
  | 14 ->
      (* VK IC accumulation (partial): ic0 + ic1*pis[0] + ic2*pis[1] + ic3*pis[2].
         Input is the PI hash from zkp13 (not an accumulator hash).
         Outputs hash([input, pis_hash, acc_hash]).
         Matches nori's zkp14.ts. *)
      fun input_hash ->
       (* Witness the 5 public inputs *)
       let pis =
         Array.init 5 ~f:(fun i ->
             Step.exists FF.Field3.typ ~compute:(fun () ->
                 WT.get_public_input (Circuit_config.get_tracker ()) i ) )
       in
       let pis_hash =
         Accumulator_hash.poseidon_hash
           (Array.concat_map pis ~f:(fun (l0, l1, l2) -> [| l0; l1; l2 |]))
       in
       (* Witness IC points from VK (constants) *)
       let ic0 =
         Step.exists G1.Circuit.typ ~compute:(fun () ->
             g1_of_tracker (WT.get_ic (Circuit_config.get_tracker ()) 0) )
       in
       let ic1 =
         Step.exists G1.Circuit.typ ~compute:(fun () ->
             g1_of_tracker (WT.get_ic (Circuit_config.get_tracker ()) 1) )
       in
       let ic2 =
         Step.exists G1.Circuit.typ ~compute:(fun () ->
             g1_of_tracker (WT.get_ic (Circuit_config.get_tracker ()) 2) )
       in
       let ic3 =
         Step.exists G1.Circuit.typ ~compute:(fun () ->
             g1_of_tracker (WT.get_ic (Circuit_config.get_tracker ()) 3) )
       in
       (* In-circuit scalar multiplication: ic_i * pis[i-1] *)
       let scaled1 = G1.scale ic1 pis.(0) in
       let scaled2 = G1.scale ic2 pis.(1) in
       let scaled3 = G1.scale ic3 pis.(2) in
       (* In-circuit accumulation: ic0 + scaled1 + scaled2 + scaled3 *)
       let partial_acc = G1.add_nonzero ic0 scaled1 in
       let partial_acc = G1.add_nonzero partial_acc scaled2 in
       let partial_acc = G1.add_nonzero partial_acc scaled3 in
       (* Output: hash([pi_hash, pis_hash, acc_hash]) *)
       let acc_hash = hash_g1 partial_acc in
       Accumulator_hash.poseidon_hash [| input_hash; pis_hash; acc_hash |]
  | 15 ->
      (* Final IC accumulation: partial_acc + ic4*pis[3] + ic5*pis[4].
         Asserts the result equals PI from the original proof.
         Input chains from zkp14 output.
         Matches nori's zkp15.ts. *)
      fun input_hash ->
       (* Witness PI and partial accumulator *)
       let pi =
         Step.exists G1.Circuit.typ ~compute:(fun () ->
             let tracker = Circuit_config.get_tracker () in
             g1_of_tracker (WT.get_pi tracker) )
       in
       let partial_acc =
         Step.exists G1.Circuit.typ ~compute:(fun () ->
             g1_of_tracker
               (WT.get_partial_ic_acc (Circuit_config.get_tracker ())) )
       in
       let pis =
         Array.init 5 ~f:(fun i ->
             Step.exists FF.Field3.typ ~compute:(fun () ->
                 WT.get_public_input (Circuit_config.get_tracker ()) i ) )
       in
       (* Verify input hash: hash([pi_hash, pis_hash, acc_hash]) *)
       let pi_hash = hash_g1 pi in
       let pis_hash =
         Accumulator_hash.poseidon_hash
           (Array.concat_map pis ~f:(fun (l0, l1, l2) -> [| l0; l1; l2 |]))
       in
       let acc_hash_input = hash_g1 partial_acc in
       let expected_input =
         Accumulator_hash.poseidon_hash [| pi_hash; pis_hash; acc_hash_input |]
       in
       Step.Field.Assert.equal input_hash expected_input ;
       (* In-circuit scalar multiplication for remaining IC points *)
       let ic4 =
         Step.exists G1.Circuit.typ ~compute:(fun () ->
             g1_of_tracker (WT.get_ic (Circuit_config.get_tracker ()) 4) )
       in
       let ic5 =
         Step.exists G1.Circuit.typ ~compute:(fun () ->
             g1_of_tracker (WT.get_ic (Circuit_config.get_tracker ()) 5) )
       in
       let scaled4 = G1.scale ic4 pis.(3) in
       let scaled5 = G1.scale ic5 pis.(4) in
       (* Complete accumulation *)
       let full_acc = G1.add_nonzero partial_acc scaled4 in
       let full_acc = G1.add_nonzero full_acc scaled5 in
       (* Assert computed IC accumulation equals the proof's PI *)
       FF.assert_equal (FF.FpA.to_field3 full_acc.x) (FF.FpA.to_field3 pi.x) ;
       FF.assert_equal (FF.FpA.to_field3 full_acc.y) (FF.FpA.to_field3 pi.y) ;
       (* Output pis_hash (matches nori's return value) *)
       pis_hash
  | n ->
      failwith (sprintf "Invalid circuit index: %d" n)
