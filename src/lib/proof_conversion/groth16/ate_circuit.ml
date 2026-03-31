(** Ate loop circuit body shared by zkp0-6.

    Each iteration:
    1. Witnesses b_line (lambda, neg_mu)
    2. Asserts b_line is tangent to T (line passes through T, tangent condition)
    3. Evaluates b_line at negA affine cache → g
    4. Multiplies g into f
    5. Updates T = double_from_line(T, b_line.lambda)
    6. On non-zero ate bits: witnesses add b_line, asserts it passes through
       T and B (or negB), updates T, evaluates and multiplies into f and g

    Matches nori's zkp0-6 ate loop structure. *)

open! Core_kernel
module FF = Snarky_foreign_field.Foreign_field
module Step = Pickles.Impls.Step
module WT = Witness_tracker

(** Process one ate loop iteration in-circuit.
    Returns (updated_f, g, updated_T). *)
let process_iteration (f : Fp12.Circuit.t) (t_point : G2.Circuit.t)
    ~(b_point : G2.Circuit.t) ~(neg_b : G2.Circuit.t) ~(bit : int)
    ~(double_line : Lines.G2Line.t) ~(cache : Lines.AffineCache.t)
    ~(add_line : Lines.G2Line.t option) :
    Fp12.Circuit.t * Fp12.Circuit.t * G2.Circuit.t =
  (* Assert the double line is tangent to T *)
  Lines.assert_is_tangent double_line t_point ;
  let f = Fp12.square f in
  let g = Lines.eval_to_fp12 double_line cache in
  let f = Lines.mul_by_line f double_line cache in
  (* Update T by doubling *)
  let t_point = Lines.double_from_line t_point ~lambda:double_line.lambda in
  match (bit, add_line) with
  | 0, _ ->
      (f, g, t_point)
  | 1, Some add_l ->
      (* Assert add line passes through T and B *)
      Lines.assert_is_line add_l t_point b_point ;
      let g = Fp12.mul g (Lines.eval_to_fp12 add_l cache) in
      let f = Lines.mul_by_line f add_l cache in
      let t_point = Lines.add_from_line t_point ~lambda:add_l.lambda b_point in
      (f, g, t_point)
  | -1, Some add_l ->
      (* Assert add line passes through T and negB *)
      Lines.assert_is_line add_l t_point neg_b ;
      let g = Fp12.mul g (Lines.eval_to_fp12 add_l cache) in
      let f = Lines.mul_by_line f add_l cache in
      let t_point = Lines.add_from_line t_point ~lambda:add_l.lambda neg_b in
      (f, g, t_point)
  | _ ->
      (f, g, t_point)

(** Run a chunk of ate loop iterations with T point tracking.
    Returns (final_f, g_values, final_T). *)
let run_chunk (f : Fp12.Circuit.t) (t_point : G2.Circuit.t)
    ~(b_point : G2.Circuit.t) ~(neg_b : G2.Circuit.t) ~(begin_idx : int)
    ~(end_idx : int) ~(cache : Lines.AffineCache.t) :
    Fp12.Circuit.t * Fp12.Circuit.t array * G2.Circuit.t =
  let ate = Bn254_params.ate_loop_count in
  let n = end_idx - begin_idx in
  let g_values = Array.create ~len:n Fp12.one in
  let f_ref = ref f in
  let t_ref = ref t_point in
  for i = begin_idx to end_idx - 1 do
    let bit = ate.(i) in
    let double_line : Lines.G2Line.t =
      { lambda =
          Step.exists Fp2.Circuit.typ ~compute:(fun () ->
              let tracker = Circuit_config.get_tracker () in
              (WT.get_iteration tracker (i - 1)).double_line.lambda )
      ; neg_mu =
          Step.exists Fp2.Circuit.typ ~compute:(fun () ->
              let tracker = Circuit_config.get_tracker () in
              (WT.get_iteration tracker (i - 1)).double_line.neg_mu )
      }
    in
    let add_line =
      if bit <> 0 then
        Some
          { Lines.G2Line.lambda =
              Step.exists Fp2.Circuit.typ ~compute:(fun () ->
                  let tracker = Circuit_config.get_tracker () in
                  let line = (WT.get_iteration tracker (i - 1)).add_line in
                  (Option.value_exn line).lambda )
          ; neg_mu =
              Step.exists Fp2.Circuit.typ ~compute:(fun () ->
                  let tracker = Circuit_config.get_tracker () in
                  let line = (WT.get_iteration tracker (i - 1)).add_line in
                  (Option.value_exn line).neg_mu )
          }
      else None
    in
    let new_f, g, new_t =
      process_iteration !f_ref !t_ref ~b_point ~neg_b ~bit ~double_line ~cache
        ~add_line
    in
    f_ref := new_f ;
    t_ref := new_t ;
    g_values.(i - begin_idx) <- g
  done ;
  (!f_ref, g_values, !t_ref)

(** Ate loop iteration ranges per circuit, matching nori exactly.
    zkp0: [1,10), zkp1: [10,20), ..., zkp5: [50,59), zkp6: [59,65) *)
let circuit_ranges =
  [| (1, 10); (10, 20); (20, 30); (30, 40); (40, 50); (50, 59); (59, 65) |]

(** Build the circuit body for an ate loop circuit from a witnessed
    accumulator. Handles T tracking, line assertions, and g_digest.
    Returns (updated_f, updated_g_digest, updated_T). *)
let build_from_acc (acc : Accumulator.Circuit.t) ~(circuit_index : int) :
    Fp12.Circuit.t * Step.Field.t * G2.Circuit.t =
  assert (circuit_index >= 0 && circuit_index <= 6) ;
  let begin_idx, end_idx = circuit_ranges.(circuit_index) in
  let n_total = Array.length Bn254_params.ate_loop_count in
  let f = acc.state.f in
  let t_point = acc.state.t_point in
  let b_point = acc.proof.b in
  let neg_b = G2.negate b_point in
  let cache : Lines.AffineCache.t =
    { x_over_y =
        Step.exists FF.Field3.typ ~compute:(fun () ->
            let tracker = Circuit_config.get_tracker () in
            let neg_a = WT.get_neg_a tracker in
            fst (WT.compute_affine_cache neg_a) )
    ; y_inv =
        Step.exists FF.Field3.typ ~compute:(fun () ->
            let tracker = Circuit_config.get_tracker () in
            let neg_a = WT.get_neg_a tracker in
            snd (WT.compute_affine_cache neg_a) )
    }
  in
  (* Witness the full lines_hashes array and verify against g_digest *)
  let lines_hashes =
    Array.init n_total ~f:(fun i ->
        Step.exists Step.Field.typ ~compute:(fun () ->
            (WT.get_line_hashes (Circuit_config.get_tracker ())).(i) ) )
  in
  let digest = Array_list_hasher.hash lines_hashes in
  Step.Field.Assert.equal acc.state.g_digest digest ;
  (* Run the ate loop chunk with T tracking *)
  let f_updated, g_values, t_updated =
    run_chunk f t_point ~b_point ~neg_b ~begin_idx ~end_idx ~cache
  in
  (* Update lines_hashes with the computed g values *)
  for i = 0 to Array.length g_values - 1 do
    let idx = begin_idx - 1 + i in
    lines_hashes.(idx) <- Accumulator_hash.hash_fp12 g_values.(i)
  done ;
  (* Compute the updated g_digest *)
  let new_g_digest = Array_list_hasher.hash lines_hashes in
  (f_updated, new_g_digest, t_updated)
