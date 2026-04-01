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

(** Three-cache line evaluation context. *)
type three_cache =
  { a_cache : Lines.AffineCache.t  (** negA — for B-lines *)
  ; c_cache : Lines.AffineCache.t  (** C — for delta-lines *)
  ; pi_cache : Lines.AffineCache.t  (** PI — for gamma-lines *)
  }

(** Process one ate loop iteration in-circuit with 3-party line evaluation.
    Returns (updated_f, g, updated_T). *)
let process_iteration (f : Fp12.Circuit.t) (t_point : G2.Circuit.t)
    ~(b_point : G2.Circuit.t) ~(neg_b : G2.Circuit.t) ~(bit : int)
    ~(double_line : Lines.G2Line.t) ~(delta_double : Lines.G2Line.t)
    ~(gamma_double : Lines.G2Line.t) ~(caches : three_cache)
    ~(add_line : Lines.G2Line.t option) ~(delta_add : Lines.G2Line.t option)
    ~(gamma_add : Lines.G2Line.t option) :
    Fp12.Circuit.t * Fp12.Circuit.t * G2.Circuit.t =
  (* Assert the B double line is tangent to T *)
  Lines.assert_is_tangent double_line t_point ;
  let f = Fp12.square f in
  (* Evaluate all 3 double lines at their respective caches *)
  let g = Lines.eval_to_fp12 double_line caches.a_cache in
  let g = Fp12.mul g (Lines.eval_to_fp12 delta_double caches.c_cache) in
  let g = Fp12.mul g (Lines.eval_to_fp12 gamma_double caches.pi_cache) in
  let f = Lines.mul_by_line f double_line caches.a_cache in
  (* Update T by doubling *)
  let t_point = Lines.double_from_line t_point ~lambda:double_line.lambda in
  match (bit, add_line, delta_add, gamma_add) with
  | 0, _, _, _ ->
      (f, g, t_point)
  | 1, Some add_l, Some d_add, Some g_add ->
      Lines.assert_is_line add_l t_point b_point ;
      let g2 = Lines.eval_to_fp12 add_l caches.a_cache in
      let g2 = Fp12.mul g2 (Lines.eval_to_fp12 d_add caches.c_cache) in
      let g2 = Fp12.mul g2 (Lines.eval_to_fp12 g_add caches.pi_cache) in
      let g = Fp12.mul g g2 in
      let f = Lines.mul_by_line f add_l caches.a_cache in
      let t_point = Lines.add_from_line t_point ~lambda:add_l.lambda b_point in
      (f, g, t_point)
  | -1, Some add_l, Some d_add, Some g_add ->
      Lines.assert_is_line add_l t_point neg_b ;
      let g2 = Lines.eval_to_fp12 add_l caches.a_cache in
      let g2 = Fp12.mul g2 (Lines.eval_to_fp12 d_add caches.c_cache) in
      let g2 = Fp12.mul g2 (Lines.eval_to_fp12 g_add caches.pi_cache) in
      let g = Fp12.mul g g2 in
      let f = Lines.mul_by_line f add_l caches.a_cache in
      let t_point = Lines.add_from_line t_point ~lambda:add_l.lambda neg_b in
      (f, g, t_point)
  | _ ->
      (f, g, t_point)

(** Witness a G2Line from tracker iteration data. *)
let witness_line (get : WT.iteration_data -> WT.Line.t) (iter_idx : int) :
    Lines.G2Line.t =
  { Lines.G2Line.lambda =
      Step.exists Fp2.Circuit.typ ~compute:(fun () ->
          (get (WT.get_iteration (Circuit_config.get_tracker ()) iter_idx))
            .lambda )
  ; neg_mu =
      Step.exists Fp2.Circuit.typ ~compute:(fun () ->
          (get (WT.get_iteration (Circuit_config.get_tracker ()) iter_idx))
            .neg_mu )
  }

(** Witness an optional G2Line from tracker. *)
let witness_opt_line (get : WT.iteration_data -> WT.Line.t option)
    (iter_idx : int) : Lines.G2Line.t =
  { Lines.G2Line.lambda =
      Step.exists Fp2.Circuit.typ ~compute:(fun () ->
          (Option.value_exn
             (get (WT.get_iteration (Circuit_config.get_tracker ()) iter_idx)) )
            .lambda )
  ; neg_mu =
      Step.exists Fp2.Circuit.typ ~compute:(fun () ->
          (Option.value_exn
             (get (WT.get_iteration (Circuit_config.get_tracker ()) iter_idx)) )
            .neg_mu )
  }

(** Run a chunk of ate loop iterations with T tracking and 3-party lines.
    [b_lines] is the pre-witnessed slice of B-lines for this chunk
    (matching nori's LineParser.parse output).
    Hashes each g value into [lines_hashes] inline (matching nori's
    [lines_hashes[idx] = Poseidon.hashPacked(Fp12, g)] inside the loop).
    Returns (final_f, final_T). *)
let run_chunk (f : Fp12.Circuit.t) (t_point : G2.Circuit.t)
    ~(b_point : G2.Circuit.t) ~(neg_b : G2.Circuit.t) ~(begin_idx : int)
    ~(end_idx : int) ~(b_lines : Lines.G2Line.t array)
    ~(lines_hashes : Step.Field.t array) ~(caches : three_cache) :
    Fp12.Circuit.t * G2.Circuit.t =
  let ate = Bn254_params.ate_loop_count in
  let f_ref = ref f in
  let t_ref = ref t_point in
  let line_cnt = ref 0 in
  for i = begin_idx to end_idx - 1 do
    let bit = ate.(i) in
    let iter_idx = i - 1 in
    let double_line = b_lines.(!line_cnt) in
    incr line_cnt ;
    let delta_double =
      witness_line (fun d -> d.WT.delta_double_line) iter_idx
    in
    let gamma_double =
      witness_line (fun d -> d.WT.gamma_double_line) iter_idx
    in
    let add_line, delta_add, gamma_add =
      if bit <> 0 then (
        let add_l = b_lines.(!line_cnt) in
        incr line_cnt ;
        ( Some add_l
        , Some (witness_opt_line (fun d -> d.WT.delta_add_line) iter_idx)
        , Some (witness_opt_line (fun d -> d.WT.gamma_add_line) iter_idx) ) )
      else (None, None, None)
    in
    let new_f, g, new_t =
      process_iteration !f_ref !t_ref ~b_point ~neg_b ~bit ~double_line
        ~delta_double ~gamma_double ~caches ~add_line ~delta_add ~gamma_add
    in
    f_ref := new_f ;
    t_ref := new_t ;
    (* Hash g into lines_hashes inline, matching nori:
       lines_hashes[idx] = Poseidon.hashPacked(Fp12, g) *)
    lines_hashes.(iter_idx) <- Accumulator_hash.hash_fp12 g
  done ;
  (!f_ref, !t_ref)

(** Ate loop iteration ranges per circuit, matching nori exactly.
    zkp0: [1,10), zkp1: [10,20), ..., zkp5: [50,59), zkp6: [59,65) *)
let circuit_ranges =
  [| (1, 10); (10, 20); (20, 30); (30, 40); (40, 50); (50, 59); (59, 65) |]

(** Compute the number of B-lines in nori's flat array for a range of
    ate iterations.  Each iteration contributes 1 double line + 1 add
    line when the ate bit is non-zero.  Matches nori's ateCntSlice. *)
let b_line_count ~from ~to_ =
  let ate = Bn254_params.ate_loop_count in
  let n = ref 0 in
  for i = from to to_ - 1 do
    n := !n + if ate.(i) <> 0 then 2 else 1
  done ;
  !n

(** Total B-lines across all ate iterations [1,65).
    Matches nori's Provable.Array(G2Line, 91). *)
let total_b_lines =
  b_line_count ~from:1 ~to_:(Array.length Bn254_params.ate_loop_count)

(** B-line start offset in the flat array for a given circuit range. *)
let b_line_offset ~begin_idx = b_line_count ~from:1 ~to_:begin_idx

(** Build the circuit body for an ate loop circuit from pre-witnessed
    values.  [lines_hashes] and [all_b_lines] must already be witnessed
    (matching nori's privateInputs pattern).
    Returns (updated_f, updated_g_digest, updated_T). *)
let build_from_acc (acc : Accumulator.Circuit.t)
    ~(lines_hashes : Step.Field.t array) ~(all_b_lines : Lines.G2Line.t array)
    ~(circuit_index : int) : Fp12.Circuit.t * Step.Field.t * G2.Circuit.t =
  assert (circuit_index >= 0 && circuit_index <= 6) ;
  let begin_idx, end_idx = circuit_ranges.(circuit_index) in
  let f = acc.state.f in
  let t_point = acc.state.t_point in
  let b_point = acc.proof.b in
  (* Verify lines_hashes against g_digest *)
  let digest = Array_list_hasher.hash lines_hashes in
  Step.Field.Assert.equal acc.state.g_digest digest ;
  (* Slice the b_lines for this circuit's range *)
  let caches : three_cache =
    let a_cache = Lines.AffineCache.make acc.proof.neg_a in
    let c_cache = Lines.AffineCache.make acc.proof.c in
    let pi_cache = Lines.AffineCache.make acc.proof.pi in
    { a_cache; c_cache; pi_cache }
  in
  let neg_b = G2.negate b_point in
  let b_lines =
    let offset = b_line_offset ~begin_idx in
    let count = b_line_count ~from:begin_idx ~to_:end_idx in
    Array.sub all_b_lines ~pos:offset ~len:count
  in
  (* Run the ate loop chunk with T tracking.
     g values are hashed into lines_hashes inline. *)
  let f_updated, t_updated =
    run_chunk f t_point ~b_point ~neg_b ~begin_idx ~end_idx ~b_lines
      ~lines_hashes ~caches
  in
  (* Update lines_hashes with the computed g values *)
  for i = 0 to Array.length g_values - 1 do
    let idx = begin_idx - 1 + i in
    lines_hashes.(idx) <- Accumulator_hash.hash_fp12 g_values.(i)
  done ;
  (* Compute the updated g_digest *)
  let new_g_digest = Array_list_hasher.hash lines_hashes in
  (f_updated, new_g_digest, t_updated)
