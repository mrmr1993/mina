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

(** Total number of circuits. *)
let num_circuits = 16

(** Witness the accumulator and verify the input hash matches. *)
let witness_and_verify_acc (input_hash : Step.Field.t) : Accumulator.Circuit.t =
  let acc =
    Step.exists Accumulator.typ ~request:(fun () ->
        Groth16_requests.Groth16_accumulator )
  in
  let acc_hash = Accumulator.hash acc in
  Step.Field.Assert.equal input_hash acc_hash ;
  acc

(** Provable.switch for Fp12: multiply each value's fields by mask, sum.
    Matches nori's Provable.switch(mask, Fp12, values) exactly.
    When values are constants, produces zero gates (pure linear combinations). *)
let switch_fp12 (mask : Step.Boolean.var array) (values : Fp12.Circuit.t array)
    : Fp12.Circuit.t =
  (* Flatten Fp12 to 36 native fields in toFields order *)
  let to_fields (x : Fp12.Circuit.t) : Step.Field.t array =
    let fp2 (a : Fp2.Circuit.t) =
      let c0_0, c0_1, c0_2 = FF.FpA.to_field3 a.c0 in
      let c1_0, c1_1, c1_2 = FF.FpA.to_field3 a.c1 in
      [| c0_0; c0_1; c0_2; c1_0; c1_1; c1_2 |]
    in
    let fp6 (a : Fp6.Circuit.t) =
      Array.concat [ fp2 a.c0; fp2 a.c1; fp2 a.c2 ]
    in
    Array.concat [ fp6 x.c0; fp6 x.c1 ]
  in
  let n = Array.length mask in
  let value_fields = Array.map values ~f:to_fields in
  let size = Array.length value_fields.(0) in
  let fields = Array.create ~len:size Step.Field.zero in
  (* Outer loop over values, inner over fields — matching o1js iteration *)
  for i = 0 to n - 1 do
    let vf = value_fields.(i) in
    let mf = (mask.(i) :> Step.Field.t) in
    for j = 0 to size - 1 do
      let maybe = Step.Field.mul vf.(j) mf in
      fields.(j) <- Step.Field.add fields.(j) maybe
    done
  done ;
  (* Reconstruct Fp12 from 36 fields *)
  let fp2_of idx =
    { Fp2.Circuit.c0 =
        FF.FpA.of_field3_unsafe
          (fields.(idx), fields.(idx + 1), fields.(idx + 2))
    ; c1 =
        FF.FpA.of_field3_unsafe
          (fields.(idx + 3), fields.(idx + 4), fields.(idx + 5))
    }
  in
  let fp6_of idx =
    { Fp6.Circuit.c0 = fp2_of idx
    ; c1 = fp2_of (idx + 6)
    ; c2 = fp2_of (idx + 12)
    }
  in
  { Fp12.Circuit.c0 = fp6_of 0; c1 = fp6_of 18 }

(** Hash a G1 point matching nori's Poseidon.hashPacked(G1Affine, ...).
    G1Affine has 6 limbs of 88 bits each. hashPacked packs pairs of limbs
    into 176-bit fields (2 limbs fit in <255 bits), producing 3 packed
    fields instead of 6, saving one Poseidon absorption round. *)
let hash_g1 (pt : G1.Circuit.t) : Step.Field.t =
  let l0_x, l1_x, l2_x = FF.FpA.to_field3 pt.x in
  let l0_y, l1_y, l2_y = FF.FpA.to_field3 pt.y in
  let two_88 =
    Step.Field.constant
      (FF.bignum_to_field_const Bignum_bigint.(shift_left one 88))
  in
  (* Pack pairs of 88-bit limbs into 176-bit fields, matching nori's
     packToFields: currentPacked = currentPacked * 2^88 + field.
     packed0 = x0*2^88 + x1, packed1 = x2*2^88 + y0, packed2 = y1*2^88 + y2 *)
  let packed0 = Step.Field.((l0_x * two_88) + l1_x) in
  let packed1 = Step.Field.((l2_x * two_88) + l0_y) in
  let packed2 = Step.Field.((l1_y * two_88) + l2_y) in
  Accumulator_hash.poseidon_hash [| packed0; packed1; packed2 |]

(** Pack Field3 limbs for hashPacked, matching nori's packToFields.
    Groups 88-bit limbs into 176-bit packed fields. *)
let hash_packed_field3_array (pis : FF.Field3.t array) : Step.Field.t =
  let two_88 =
    Step.Field.constant
      (FF.bignum_to_field_const Bignum_bigint.(shift_left one 88))
  in
  let packed = Queue.create () in
  let cur = ref Step.Field.zero in
  let cur_size = ref 0 in
  Array.iter pis ~f:(fun (l0, l1, l2) ->
      Array.iter [| l0; l1; l2 |] ~f:(fun limb ->
          cur_size := !cur_size + 88 ;
          if !cur_size < 255 then cur := Step.Field.((!cur * two_88) + limb)
          else (
            Queue.enqueue packed !cur ;
            cur := limb ;
            cur_size := 88 ) ) ) ;
  Queue.enqueue packed !cur ;
  Accumulator_hash.poseidon_hash (Queue.to_array packed)

(** Convert VK constant lines to circuit constants (embedded in the
    constraint system, not witnesses).  Called at circuit definition
    time, outside the proving closure. *)
let vk_lines_to_circuit (lines : WT.Line.t array) : Lines.G2Line.t array =
  Array.map lines ~f:(fun l ->
      Lines.G2Line.of_constant (l.WT.Line.lambda, l.WT.Line.neg_mu) )

(** Witness the accumulator, line hashes, and b_lines; verify the
    input hash matches the accumulator hash.  Shared setup for
    circuits 0-6 (ate loop circuits). *)
let witness_ate_common (input_hash : Step.Field.t) :
    Accumulator.Circuit.t * Step.Field.t array * Lines.G2Line.t array =
  let acc =
    Step.exists Accumulator.typ ~request:(fun () ->
        Groth16_requests.Groth16_accumulator )
  in
  let n_total = Array.length Bn254_params.ate_loop_count in
  let lines_hashes =
    Step.exists (Step.Typ.array ~length:n_total Step.Field.typ)
      ~request:(fun () -> Groth16_requests.Line_hashes)
  in
  let n_b_lines = Ate_circuit.total_b_lines + 2 in
  let all_b_lines =
    Step.exists (Step.Typ.array ~length:n_b_lines Lines.G2Line.typ)
      ~request:(fun () -> Groth16_requests.B_lines)
  in
  let acc_hash = Accumulator.hash acc in
  Step.Field.Assert.equal input_hash acc_hash ;
  (acc, lines_hashes, all_b_lines)

(** Build the circuit body for zkpN.
    [vk] provides precomputed VK constants (delta/gamma lines etc.)
    that are embedded as circuit constants, not witnesses.
    Takes the input hash and returns the output hash. *)
let build_circuit_body ~(vk : Vk_constants.t) ~(circuit_index : int) :
    circuit_body =
  (* Convert VK lines to circuit constants at definition time *)
  let delta_lines_const = vk_lines_to_circuit vk.delta_lines in
  let gamma_lines_const = vk_lines_to_circuit vk.gamma_lines in
  match circuit_index with
  | 0 | 1 | 2 | 3 | 4 | 5 ->
      (* Ate loop circuits: witness all private inputs up front,
         then run constraints and output hash. *)
      fun input_hash ->
       let acc, lines_hashes, all_b_lines = witness_ate_common input_hash in
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
         Ate_circuit.run_chunk acc.state.t_point ~b_point:acc.proof.b ~neg_b
           ~begin_idx ~end_idx ~b_lines ~delta_lines:delta_slice
           ~gamma_lines:gamma_slice ~lines_hashes ~caches
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
         both ate g values and the Frobenius g hash. *)
      fun input_hash ->
       let acc, lines_hashes, all_b_lines = witness_ate_common input_hash in
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
         Ate_circuit.run_chunk acc.state.t_point ~b_point:acc.proof.b ~neg_b
           ~begin_idx ~end_idx ~b_lines ~delta_lines:delta_slice
           ~gamma_lines:gamma_slice ~lines_hashes ~caches
       in
       (* Frobenius part: uses sparse_mul (not full Fp12.mul) for line
          evaluations. Does NOT update f. *)
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
       let g =
         let inner = Lines.psi frob_delta_lines.(0) c_cache in
         Fp12.sparse_mul g inner
       in
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
       (* Hash frobenius g into lines_hashes *)
       let n_total = Array.length Bn254_params.ate_loop_count in
       lines_hashes.(n_total - 1) <- Accumulator_hash.hash_fp12 g ;
       (* Verify c_inv * c = 1 (after hashing, matching nori order) *)
       let product = Fp12.mul acc.proof.c_inv acc.proof.c_fp12 in
       Fp12.assert_one product ;
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
       (* Witness all private inputs first (matching nori's ZkProgram) *)
       let acc =
         Step.exists Accumulator.typ ~request:(fun () ->
             Groth16_requests.Groth16_accumulator )
       in
       let n_total = Array.length Bn254_params.ate_loop_count in
       let g_idx = n_total - 1 in
       let lhs_hashes =
         Step.exists (Step.Typ.array ~length:g_idx Step.Field.typ)
           ~request:(fun () -> Groth16_requests.Lhs_hashes)
       in
       let g =
         Step.exists Fp12.typ ~request:(fun () -> Groth16_requests.Final_g)
       in
       (* Circuit body — hash checks *)
       let acc_hash = Accumulator.hash acc in
       Step.Field.Assert.equal input_hash acc_hash ;
       let opening =
         Array_list_hasher.open_ ~lhs:lhs_hashes ~opening:[| g |] ~rhs:[||]
       in
       Step.Field.Assert.equal acc.state.g_digest opening ;
       (* Multiply f by g and Frobenius powers (computed in-circuit) *)
       let f = acc.state.f in
       let f = Fp12.mul f g in
       let f = Fp12.mul f (Fp12.frobenius_pow_p acc.proof.c_inv) in
       let f = Fp12.mul f (Fp12.frobenius_pow_p_squared acc.proof.c_fp12) in
       let f = Fp12.mul f (Fp12.frobenius_pow_p_cubed acc.proof.c_inv) in
       (* Multiply by alpha_beta from VK (circuit constant) *)
       let f = Fp12.mul f vk.alpha_beta in
       (* Apply shift_power: Provable.switch pattern matching nori.
          Use field_var_equal (seals diff first) to match o1js's equals()
          which calls .seal() before assertMul, avoiding redundant
          reduce_lincom sealing in each R1CS constraint. *)
       let is_0 =
         FF.field_var_equal acc.proof.shift_power (Step.Field.of_int 0)
       in
       let is_1 =
         FF.field_var_equal acc.proof.shift_power (Step.Field.of_int 1)
       in
       let is_2 =
         FF.field_var_equal acc.proof.shift_power (Step.Field.of_int 2)
       in
       let shift =
         switch_fp12 [| is_0; is_1; is_2 |] [| Fp12.one; vk.w27; vk.w27_sq |]
       in
       let f = Fp12.mul f shift in
       (* Assert final result equals Fp12.one *)
       Fp12.assert_one f ;
       (* Domain transition: output hash of PI point *)
       hash_g1 acc.proof.pi
  | 14 -> (
      fun (* VK IC accumulation (partial): ic0 + ic1*pis[0] + ic2*pis[1] + ic3*pis[2].
             Input is the PI hash from zkp13 (not an accumulator hash).
             Outputs hash([input, pis_hash, acc_hash]).
             Mirrors nori zkp14: pis witnessed as FrC (canonical over r),
             result point assertCanonical'd before hashing. *)
            input_hash ->
        FF.enable_abort () ;
        (* Witness the 5 public inputs as canonical scalars (FrC) *)
        let pis =
          Step.exists
            (Step.Typ.array ~length:5 (FF.FpC.typ ~f:Bn254_params.r))
            ~request:(fun () -> Groth16_requests.Public_inputs)
        in
        let pis_f3 = Array.map pis ~f:FF.FpC.to_field3 in
        let pis_hash = hash_packed_field3_array pis_f3 in
        (* IC points from VK (circuit constants, not witnessed) *)
        let ic0 = vk.ic.(0) in
        let ic1 = vk.ic.(1) in
        let ic2 = vk.ic.(2) in
        let ic3 = vk.ic.(3) in
        try
          (* In-circuit: acc = ic0 + ic1*pis[0] + ic2*pis[1] + ic3*pis[2] *)
          let acc = { G1.Circuit.x = ic0.x; y = ic0.y } in
          let acc = G1.add acc (G1.scale ic1 pis_f3.(0)) in
          let acc = G1.add acc (G1.scale ic2 pis_f3.(1)) in
          let partial_acc = G1.add acc (G1.scale ic3 pis_f3.(2)) in
          (* assertCanonical on result point, matching nori *)
          let acc_x = FF.FpC.assert_canonical partial_acc.x ~f:Bn254_params.p in
          let acc_y = FF.FpC.assert_canonical partial_acc.y ~f:Bn254_params.p in
          let acc_pt =
            { G1.Circuit.x = FF.FpC.to_fpa acc_x; y = FF.FpC.to_fpa acc_y }
          in
          (* Output: hash([input, pis_hash, acc_hash]) *)
          let acc_hash = hash_g1 acc_pt in
          Accumulator_hash.poseidon_hash [| input_hash; pis_hash; acc_hash |]
        with FF.Circuit_abort -> pis_hash )
  | 15 ->
      (* Final IC accumulation: partial_acc + ic4*pis[3] + ic5*pis[4].
         Asserts the result equals PI from the original proof.
         Input chains from zkp14 output.
         Mirrors nori zkp15: witnesses PI, acc, pis as separate inputs;
         result assertCanonical'd then assertEquals'd against PI. *)
      fun input_hash ->
       (* Witness PI and partial accumulator as G1Affine *)
       let pi =
         Step.exists G1.Circuit.typ ~request:(fun () ->
             Groth16_requests.Pi_point )
       in
       let partial_acc =
         Step.exists G1.Circuit.typ ~request:(fun () ->
             Groth16_requests.Partial_ic_acc )
       in
       (* Witness pis as canonical scalars (FrC) *)
       let pis =
         Step.exists
           (Step.Typ.array ~length:5 (FF.FpC.typ ~f:Bn254_params.r))
           ~request:(fun () -> Groth16_requests.Public_inputs)
       in
       let pis_f3 = Array.map pis ~f:FF.FpC.to_field3 in
       (* Verify input hash: hash([pi_hash, pis_hash, acc_hash]) *)
       let pi_hash = hash_g1 pi in
       let pis_hash = hash_packed_field3_array pis_f3 in
       let acc_hash_input = hash_g1 partial_acc in
       let expected_input =
         Accumulator_hash.poseidon_hash [| pi_hash; pis_hash; acc_hash_input |]
       in
       Step.Field.Assert.equal input_hash expected_input ;
       (* IC points from VK (circuit constants) *)
       let ic4 = vk.ic.(4) in
       let ic5 = vk.ic.(5) in
       (* In-circuit: acc + ic4*pis[3] + ic5*pis[4] *)
       let full_acc = G1.add partial_acc (G1.scale ic4 pis_f3.(3)) in
       let full_acc = G1.add full_acc (G1.scale ic5 pis_f3.(4)) in
       (* assertCanonical on result, then assertEquals against PI *)
       let res_x = FF.FpC.assert_canonical full_acc.x ~f:Bn254_params.p in
       let res_y = FF.FpC.assert_canonical full_acc.y ~f:Bn254_params.p in
       FF.assert_equal (FF.FpC.to_field3 res_x) (FF.FpA.to_field3 pi.x) ;
       FF.assert_equal (FF.FpC.to_field3 res_y) (FF.FpA.to_field3 pi.y) ;
       (* Output pis_hash *)
       pis_hash
  | n ->
      failwith (sprintf "Invalid circuit index: %d" n)

(** Build a circuit body that returns (output_hash, accumulator) for
    circuits 0-12, enabling auxiliary_output chaining.
    For circuits 13-15, returns a dummy accumulator (they don't chain). *)
let build_circuit_body_with_acc ~(vk : Vk_constants.t) ~(circuit_index : int) :
    Step.Field.t -> Step.Field.t * Accumulator.Circuit.t =
  let body = build_circuit_body ~vk ~circuit_index in
  match circuit_index with
  | 0 | 1 | 2 | 3 | 4 | 5 ->
      (* Ate loop circuits: the body internally witnesses acc and builds
         updated. We re-run the same logic but capture updated. *)
      let delta_lines_const = vk_lines_to_circuit vk.delta_lines in
      let gamma_lines_const = vk_lines_to_circuit vk.gamma_lines in
      fun input_hash ->
        let acc, lines_hashes, all_b_lines = witness_ate_common input_hash in
        let acc =
          if circuit_index = 0 then
            { acc with state = { acc.state with t_point = acc.proof.b } }
          else acc
        in
        let digest = Array_list_hasher.hash lines_hashes in
        Step.Field.Assert.equal acc.state.g_digest digest ;
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
          Ate_circuit.run_chunk acc.state.t_point ~b_point:acc.proof.b ~neg_b
            ~begin_idx ~end_idx ~b_lines ~delta_lines:delta_slice
            ~gamma_lines:gamma_slice ~lines_hashes ~caches
        in
        let new_g_digest = Array_list_hasher.hash lines_hashes in
        let updated : Accumulator.Circuit.t =
          { proof = acc.proof
          ; state =
              { acc.state with g_digest = new_g_digest; t_point = t_updated }
          }
        in
        (Accumulator.hash updated, updated)
  | 6 ->
      (* Ate loop + Frobenius: same as circuit body but returns acc. *)
      let delta_lines_const = vk_lines_to_circuit vk.delta_lines in
      let gamma_lines_const = vk_lines_to_circuit vk.gamma_lines in
      fun input_hash ->
        let acc, lines_hashes, all_b_lines = witness_ate_common input_hash in
        let digest = Array_list_hasher.hash lines_hashes in
        Step.Field.Assert.equal acc.state.g_digest digest ;
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
        let t_after_ate =
          Ate_circuit.run_chunk acc.state.t_point ~b_point:acc.proof.b ~neg_b
            ~begin_idx ~end_idx ~b_lines ~delta_lines:delta_slice
            ~gamma_lines:gamma_slice ~lines_hashes ~caches
        in
        let n_b = Array.length all_b_lines in
        let frob_b_lines = [| all_b_lines.(n_b - 2); all_b_lines.(n_b - 1) |] in
        let n_d = Array.length delta_lines_const in
        let frob_delta_lines =
          [| delta_lines_const.(n_d - 2); delta_lines_const.(n_d - 1) |]
        in
        let n_g = Array.length gamma_lines_const in
        let frob_gamma_lines =
          [| gamma_lines_const.(n_g - 2); gamma_lines_const.(n_g - 1) |]
        in
        let g = Lines.psi frob_b_lines.(0) a_cache in
        let g = Fp12.sparse_mul g (Lines.psi frob_delta_lines.(0) c_cache) in
        let g = Fp12.sparse_mul g (Lines.psi frob_gamma_lines.(0) pi_cache) in
        let piB = G2.frobenius acc.proof.b in
        let t_point = t_after_ate in
        Lines.assert_is_line frob_b_lines.(0) t_point piB ;
        let t_point =
          G2.add_from_line t_point ~lambda:frob_b_lines.(0).lambda piB
        in
        let pi2B = piB |> G2.negative_frobenius in
        Lines.assert_is_line frob_b_lines.(1) t_point pi2B ;
        let g = Fp12.sparse_mul g (Lines.psi frob_b_lines.(1) a_cache) in
        let g = Fp12.sparse_mul g (Lines.psi frob_delta_lines.(1) c_cache) in
        let g = Fp12.sparse_mul g (Lines.psi frob_gamma_lines.(1) pi_cache) in
        let n_total = Array.length Bn254_params.ate_loop_count in
        lines_hashes.(n_total - 1) <- Accumulator_hash.hash_fp12 g ;
        let product = Fp12.mul acc.proof.c_inv acc.proof.c_fp12 in
        Fp12.assert_one product ;
        let final_g_digest = Array_list_hasher.hash lines_hashes in
        let updated : Accumulator.Circuit.t =
          { proof = acc.proof
          ; state = { acc.state with g_digest = final_g_digest; t_point }
          }
        in
        (Accumulator.hash updated, updated)
  | 7 | 8 | 9 | 10 | 11 | 12 ->
      (* f-update circuits: delegate to Fupdate_circuit.build_with_acc *)
      Fupdate_circuit.build_with_acc ~circuit_index
  | _ ->
      failwith
        (sprintf "build_circuit_body_with_acc: not implemented for circuit %d"
           circuit_index )
