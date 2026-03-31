(** Ate loop circuit body shared by zkp0-5. *)

open! Core_kernel
module FF = Snarky_foreign_field.Foreign_field
module Step = Pickles.Impls.Step
module WT = Witness_tracker

(** Process one ate loop iteration in-circuit.
    Returns (updated_f, g) where g is the line evaluation product. *)
let process_iteration (f : Fp12.Circuit.t) ~(bit : int)
    ~(double_lambda : Fp2.Circuit.t) ~(double_neg_mu : Fp2.Circuit.t)
    ~(cache : Lines.AffineCache.t) ~(add_lambda : Fp2.Circuit.t option)
    ~(add_neg_mu : Fp2.Circuit.t option) : Fp12.Circuit.t * Fp12.Circuit.t =
  let f = Fp12.square f in
  let double_line : Lines.G2Line.t =
    { lambda = double_lambda; neg_mu = double_neg_mu }
  in
  let g = Lines.eval_to_fp12 double_line cache in
  let f = Lines.mul_by_line f double_line cache in
  match (bit, add_lambda, add_neg_mu) with
  | 0, _, _ ->
      (f, g)
  | _, Some al, Some anm ->
      let add_line : Lines.G2Line.t = { lambda = al; neg_mu = anm } in
      let g = Fp12.mul g (Lines.eval_to_fp12 add_line cache) in
      let f = Lines.mul_by_line f add_line cache in
      (f, g)
  | _ ->
      (f, g)

(** Run a chunk of ate loop iterations.
    Returns (final_f, g_values) where g_values[i] is the per-iteration
    line evaluation product for iteration begin_idx+i. *)
let run_chunk (f : Fp12.Circuit.t) ~(begin_idx : int) ~(end_idx : int)
    ~(cache : Lines.AffineCache.t) : Fp12.Circuit.t * Fp12.Circuit.t array =
  let ate = Bn254_params.ate_loop_count in
  let n = end_idx - begin_idx in
  let g_values = Array.create ~len:n Fp12.one in
  let result = ref f in
  for i = begin_idx to end_idx - 1 do
    let bit = ate.(i) in
    let double_lambda =
      Step.exists Fp2.Circuit.typ ~compute:(fun () ->
          let tracker = Circuit_config.get_tracker () in
          (WT.get_iteration tracker (i - 1)).double_line.lambda )
    in
    let double_neg_mu =
      Step.exists Fp2.Circuit.typ ~compute:(fun () ->
          let tracker = Circuit_config.get_tracker () in
          (WT.get_iteration tracker (i - 1)).double_line.neg_mu )
    in
    let add_lambda, add_neg_mu =
      if bit <> 0 then
        let al =
          Step.exists Fp2.Circuit.typ ~compute:(fun () ->
              let tracker = Circuit_config.get_tracker () in
              let line = (WT.get_iteration tracker (i - 1)).add_line in
              (Option.value_exn line).lambda )
        in
        let anm =
          Step.exists Fp2.Circuit.typ ~compute:(fun () ->
              let tracker = Circuit_config.get_tracker () in
              let line = (WT.get_iteration tracker (i - 1)).add_line in
              (Option.value_exn line).neg_mu )
        in
        (Some al, Some anm)
      else (None, None)
    in
    let new_f, g =
      process_iteration !result ~bit ~double_lambda ~double_neg_mu ~cache
        ~add_lambda ~add_neg_mu
    in
    result := new_f ;
    g_values.(i - begin_idx) <- g
  done ;
  (!result, g_values)

(** Ate loop iteration ranges per circuit, matching nori exactly.
    zkp0: [1,10), zkp1: [10,20), ..., zkp5: [50,59), zkp6: [59,65) *)
let circuit_ranges =
  [| (1, 10); (10, 20); (20, 30); (30, 40); (40, 50); (50, 59); (59, 65) |]

(** Build the circuit body for an ate loop circuit from a witnessed
    accumulator. Handles g_digest verification and update.
    Returns (updated_f, updated_g_digest). *)
let build_from_acc (acc : Accumulator.Circuit.t) ~(circuit_index : int) :
    Fp12.Circuit.t * Step.Field.t =
  assert (circuit_index >= 0 && circuit_index <= 6) ;
  let begin_idx, end_idx = circuit_ranges.(circuit_index) in
  let n_total = Array.length Bn254_params.ate_loop_count in
  let f = acc.state.f in
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
  (* Run the ate loop chunk *)
  let f_updated, g_values = run_chunk f ~begin_idx ~end_idx ~cache in
  (* Update lines_hashes with the computed g values.
     Each g is hashed and written to lines_hashes[begin_idx-1+i]
     (nori uses idx = i - 1 where i is the ate loop index). *)
  for i = 0 to Array.length g_values - 1 do
    let idx = begin_idx - 1 + i in
    lines_hashes.(idx) <- Accumulator_hash.hash_fp12 g_values.(i)
  done ;
  (* Compute the updated g_digest *)
  let new_g_digest = Array_list_hasher.hash lines_hashes in
  (f_updated, new_g_digest)
