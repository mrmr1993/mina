(** Miller loop for BN254 ate pairing.

    Computes the ate pairing e(P, Q) by iterating over the ATE_LOOP_COUNT
    bits, accumulating line evaluations into an Fp12 value. *)

open! Core_kernel

(** Run the ate loop body for one iteration.
    Given the current accumulator [f], the loop bit [bit], line coefficients
    for doubling and (optionally) addition, and the G1 affine cache,
    compute the next accumulator value.

    For each bit:
    - Always: f = f^2 * line_double(T, P)
    - If bit = 1: f = f * line_add(T, Q, P)
    - If bit = -1: f = f * line_add(T, -Q, P) *)
let ate_loop_iteration (f : Fp12.Circuit.t) ~(double_line : Lines.G2Line.t)
    ~(add_line : Lines.G2Line.t option) ~(cache : Lines.AffineCache.t)
    ~(bit : int) : Fp12.Circuit.t =
  (* f = f^2 * line_double *)
  let f = Fp12.square f in
  let f = Lines.mul_by_line f double_line cache in
  match (bit, add_line) with
  | 0, _ ->
      f
  | 1, Some add_l | -1, Some add_l ->
      Lines.mul_by_line f add_l cache
  | (1 | -1), None ->
      failwith "non-zero ate bit requires an add line"
  | _ ->
      f

(** Run the full Miller loop over the ATE_LOOP_COUNT.
    Takes precomputed line coefficients for each iteration. *)
let run ~(initial_f : Fp12.Circuit.t) ~(double_lines : Lines.G2Line.t array)
    ~(add_lines : Lines.G2Line.t option array) ~(cache : Lines.AffineCache.t) :
    Fp12.Circuit.t =
  let ate = Bn254_params.ate_loop_count in
  let n = Array.length ate in
  assert (Array.length double_lines = n - 1) ;
  assert (Array.length add_lines = n - 1) ;
  let f = ref initial_f in
  (* Skip the first bit (MSB = 1, already accounted for in initial_f) *)
  for i = 1 to n - 1 do
    f :=
      ate_loop_iteration !f
        ~double_line:double_lines.(i - 1)
        ~add_line:add_lines.(i - 1)
        ~cache ~bit:ate.(i)
  done ;
  !f
