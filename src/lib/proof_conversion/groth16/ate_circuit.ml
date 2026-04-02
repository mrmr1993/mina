(** Ate loop circuit body shared by zkp0-6.

    Each iteration:
    1. Witnesses b_line (lambda, neg_mu)
    2. Asserts b_line is tangent to T (line passes through T, tangent condition)
    3. Evaluates b_line at negA affine cache → g
    4. Multiplies g into f
    5. Updates T = double_from_line(T, b_line.lambda)
    6. On non-zero ate bits: witnesses add b_line, asserts it passes through
       T and B (or negB), updates T, evaluates and multiplies into f and g

*)

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
    Computes g (line evaluations) and updates T. Does NOT update f --
    that happens in zkp7-12.
    Returns (g, updated_T). *)
let process_iteration (t_point : G2.Circuit.t) ~(b_point : G2.Circuit.t)
    ~(neg_b : G2.Circuit.t) ~(bit : int) ~(double_line : Lines.G2Line.t)
    ~(delta_double : Lines.G2Line.t) ~(gamma_double : Lines.G2Line.t)
    ~(caches : three_cache) ~(add_line : Lines.G2Line.t option)
    ~(delta_add : Lines.G2Line.t option) ~(gamma_add : Lines.G2Line.t option) :
    Fp12.Circuit.t * G2.Circuit.t =
  Lines.assert_is_tangent double_line t_point ;
  (* g = b_line.psi(a_cache) *)
  let g = Lines.psi double_line caches.a_cache in
  (* g = g.sparse_mul(delta_line.psi(c_cache)) *)
  let g = Fp12.sparse_mul g (Lines.psi delta_double caches.c_cache) in
  (* g = g.sparse_mul(gamma_line.psi(pi_cache)) *)
  let g = Fp12.sparse_mul g (Lines.psi gamma_double caches.pi_cache) in
  (* T = T.double_from_line(b_line.lambda) *)
  let t_point = G2.double_from_line t_point ~lambda:double_line.lambda in
  match (bit, add_line, delta_add, gamma_add) with
  | 0, _, _, _ ->
      (g, t_point)
  | 1, Some add_l, Some d_add, Some g_add ->
      Lines.assert_is_line add_l t_point b_point ;
      let t_point = G2.add_from_line t_point ~lambda:add_l.lambda b_point in
      let g = Fp12.sparse_mul g (Lines.psi add_l caches.a_cache) in
      let g = Fp12.sparse_mul g (Lines.psi d_add caches.c_cache) in
      let g = Fp12.sparse_mul g (Lines.psi g_add caches.pi_cache) in
      (g, t_point)
  | -1, Some add_l, Some d_add, Some g_add ->
      Lines.assert_is_line add_l t_point neg_b ;
      let t_point = G2.add_from_line t_point ~lambda:add_l.lambda neg_b in
      let g = Fp12.sparse_mul g (Lines.psi add_l caches.a_cache) in
      let g = Fp12.sparse_mul g (Lines.psi d_add caches.c_cache) in
      let g = Fp12.sparse_mul g (Lines.psi g_add caches.pi_cache) in
      (g, t_point)
  | _ ->
      (g, t_point)

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
    [b_lines] is the pre-witnessed slice of B-lines for this chunk.
    [delta_lines] and [gamma_lines] are VK constant slices (not witnesses).
    Hashes each g value into [lines_hashes] inline.
    Does NOT update f -- that happens in the f-update circuits (zkp7-12).
    Returns final_T. *)
let run_chunk (t_point : G2.Circuit.t) ~(b_point : G2.Circuit.t)
    ~(neg_b : G2.Circuit.t) ~(begin_idx : int) ~(end_idx : int)
    ~(b_lines : Lines.G2Line.t array) ~(delta_lines : Lines.G2Line.t array)
    ~(gamma_lines : Lines.G2Line.t array) ~(lines_hashes : Step.Field.t array)
    ~(caches : three_cache) : G2.Circuit.t =
  let ate = Bn254_params.ate_loop_count in
  let t_ref = ref t_point in
  let line_cnt = ref 0 in
  for i = begin_idx to end_idx - 1 do
    let bit = ate.(i) in
    let iter_idx = i - 1 in
    let double_line = b_lines.(!line_cnt) in
    let delta_double = delta_lines.(!line_cnt) in
    let gamma_double = gamma_lines.(!line_cnt) in
    incr line_cnt ;
    let add_line, delta_add, gamma_add =
      if bit <> 0 then (
        let add_l = b_lines.(!line_cnt) in
        let d_add = delta_lines.(!line_cnt) in
        let g_add = gamma_lines.(!line_cnt) in
        incr line_cnt ;
        (Some add_l, Some d_add, Some g_add) )
      else (None, None, None)
    in
    let g, new_t =
      process_iteration !t_ref ~b_point ~neg_b ~bit ~double_line ~delta_double
        ~gamma_double ~caches ~add_line ~delta_add ~gamma_add
    in
    t_ref := new_t ;
    lines_hashes.(iter_idx) <- Accumulator_hash.hash_fp12 g
  done ;
  !t_ref

(** Ate loop iteration ranges per circuit.
    zkp0: [1,10), zkp1: [10,20), ..., zkp5: [50,59), zkp6: [59,65) *)
let circuit_ranges =
  [| (1, 10); (10, 20); (20, 30); (30, 40); (40, 50); (50, 59); (59, 65) |]

(** Compute the number of B-lines in the flat array for a range of
    ate iterations.  Each iteration contributes 1 double line + 1 add
    line when the ate bit is non-zero. *)
let b_line_count ~from ~to_ =
  let ate = Bn254_params.ate_loop_count in
  let n = ref 0 in
  for i = from to to_ - 1 do
    n := !n + if ate.(i) <> 0 then 2 else 1
  done ;
  !n

(** Total B-lines across all ate iterations [1,65). *)
let total_b_lines =
  b_line_count ~from:1 ~to_:(Array.length Bn254_params.ate_loop_count)

(** B-line start offset in the flat array for a given circuit range. *)
let b_line_offset ~begin_idx = b_line_count ~from:1 ~to_:begin_idx

(** Run the ate loop for a circuit range.  All setup (g_digest
    verification, cache computation, line slicing) is done by the
    caller — this just runs the iteration chunk.
    Returns updated_T. *)
let run_circuit_chunk ~(t_point : G2.Circuit.t) ~(b_point : G2.Circuit.t)
    ~(neg_b : G2.Circuit.t) ~(begin_idx : int) ~(end_idx : int)
    ~(b_lines : Lines.G2Line.t array) ~(delta_lines : Lines.G2Line.t array)
    ~(gamma_lines : Lines.G2Line.t array) ~(lines_hashes : Step.Field.t array)
    ~(caches : three_cache) : G2.Circuit.t =
  run_chunk t_point ~b_point ~neg_b ~begin_idx ~end_idx ~b_lines ~delta_lines
    ~gamma_lines ~lines_hashes ~caches
