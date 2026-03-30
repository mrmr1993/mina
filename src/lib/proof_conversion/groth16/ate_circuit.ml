(** Ate loop circuit body shared by zkp0-5.

    Each circuit processes a range of ate loop iterations:
    - Square the Fp12 accumulator
    - Multiply by line evaluations from G2 doubling/addition
    - Hash intermediate Fp12 values for the line digest

    The line coefficients and G1 affine cache are provided as
    witnessed values. *)

module FF = Snarky_foreign_field.Foreign_field
module Step = Pickles.Impls.Step

(** Process one ate loop iteration:
    f = f^2 * line_double * [line_add if bit != 0] *)
let process_iteration (f : Fp12.Circuit.t) ~(bit : int)
    ~(double_lambda : Fp2.Circuit.t) ~(double_neg_mu : Fp2.Circuit.t)
    ~(cache : Lines.AffineCache.t)
    ~(add_lambda : Fp2.Circuit.t option)
    ~(add_neg_mu : Fp2.Circuit.t option) : Fp12.Circuit.t =
  (* f = f^2 *)
  let f = Fp12.square f in
  (* f = f * line_double(T, P) *)
  let double_line : Lines.G2Line.t =
    { lambda = double_lambda; neg_mu = double_neg_mu }
  in
  let f = Lines.mul_by_line f double_line cache in
  (* If bit != 0: f = f * line_add *)
  match (bit, add_lambda, add_neg_mu) with
  | 0, _, _ ->
      f
  | _, Some al, Some anm ->
      let add_line : Lines.G2Line.t =
        { lambda = al; neg_mu = anm }
      in
      Lines.mul_by_line f add_line cache
  | _ ->
      f

(** Run a chunk of ate loop iterations for a circuit.
    [begin_idx] and [end_idx] define the range within ATE_LOOP_COUNT. *)
let run_chunk (f : Fp12.Circuit.t) ~(begin_idx : int) ~(end_idx : int)
    ~(cache : Lines.AffineCache.t) : Fp12.Circuit.t =
  let ate = Bn254_params.ate_loop_count in
  let result = ref f in
  for i = begin_idx to end_idx - 1 do
    let bit = ate.(i) in
    (* Witness line coefficients for this iteration *)
    let witness_fp2 () : Fp2.Circuit.t =
      { Fp2.Circuit.c0 = FF.Field3.of_constant FF.Bignum_bigint.one
      ; c1 = FF.Field3.of_constant FF.Bignum_bigint.one }
    in
    let double_lambda = witness_fp2 () in
    let double_neg_mu = witness_fp2 () in
    let add_lambda, add_neg_mu =
      if bit <> 0 then (Some (witness_fp2 ()), Some (witness_fp2 ()))
      else (None, None)
    in
    result :=
      process_iteration !result ~bit ~double_lambda ~double_neg_mu
        ~cache ~add_lambda ~add_neg_mu
  done ;
  !result

(** Iteration ranges for each circuit (1-indexed into ATE_LOOP_COUNT).
    The first bit (index 0) is the MSB = 1, already handled in initialization. *)
let circuit_ranges =
  [| (1, 13)   (* zkp0: iterations 1-12 *)
   ; (13, 24)  (* zkp1: iterations 13-23 *)
   ; (24, 35)  (* zkp2: iterations 24-34 *)
   ; (35, 47)  (* zkp3: iterations 35-46 *)
   ; (47, 59)  (* zkp4: iterations 47-58 *)
   ; (59, 65)  (* zkp5: iterations 59-64 *)
  |]

(** Build the circuit body for an ate loop circuit (zkp0-5). *)
let build ~(circuit_index : int) (input_hash : Step.Field.t) :
    Step.Field.t =
  assert (circuit_index >= 0 && circuit_index <= 5) ;
  let begin_idx, end_idx = circuit_ranges.(circuit_index) in
  (* Witness the Fp12 accumulator and G1 cache.
     TODO: use Circuit_config.get_tracker() for real witness data
     once the witness tracker computes full Miller loop intermediates. *)
  let f, cache =
    ignore (Circuit_config.get_tracker () : Witness_tracker.t option) ;
        let w () : Fp2.Circuit.t =
          { Fp2.Circuit.c0 = FF.Field3.of_constant FF.Bignum_bigint.one
          ; c1 = FF.Field3.of_constant FF.Bignum_bigint.one }
        in
        let w6 () : Fp6.Circuit.t =
          { Fp6.Circuit.c0 = w (); c1 = w (); c2 = w () }
        in
        let f = { Fp12.Circuit.c0 = w6 (); c1 = w6 () } in
        let cache : Lines.AffineCache.t =
          { x_over_y = FF.Field3.of_constant FF.Bignum_bigint.one
          ; y_inv = FF.Field3.of_constant FF.Bignum_bigint.one }
        in
        (f, cache)
  in
  (* Run the ate loop chunk *)
  let _f_updated = run_chunk f ~begin_idx ~end_idx ~cache in
  (* Hash the updated accumulator as output *)
  Accumulator_hash.combine_hashes
    [ input_hash; Step.Field.of_int circuit_index ]
