(** Ate loop circuit body shared by zkp0-5. *)

open! Core_kernel
module FF = Snarky_foreign_field.Foreign_field
module Step = Pickles.Impls.Step
module WT = Witness_tracker

(** Process one ate loop iteration in-circuit. *)
let process_iteration (f : Fp12.Circuit.t) ~(bit : int)
    ~(double_lambda : Fp2.Circuit.t) ~(double_neg_mu : Fp2.Circuit.t)
    ~(cache : Lines.AffineCache.t) ~(add_lambda : Fp2.Circuit.t option)
    ~(add_neg_mu : Fp2.Circuit.t option) : Fp12.Circuit.t =
  let f = Fp12.square f in
  let double_line : Lines.G2Line.t =
    { lambda = double_lambda; neg_mu = double_neg_mu }
  in
  let f = Lines.mul_by_line f double_line cache in
  match (bit, add_lambda, add_neg_mu) with
  | 0, _, _ ->
      f
  | _, Some al, Some anm ->
      Lines.mul_by_line f { lambda = al; neg_mu = anm } cache
  | _ ->
      f

(** Run a chunk of ate loop iterations. *)
let run_chunk (f : Fp12.Circuit.t) ~(begin_idx : int) ~(end_idx : int)
    ~(cache : Lines.AffineCache.t) : Fp12.Circuit.t =
  let ate = Bn254_params.ate_loop_count in
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
    result :=
      process_iteration !result ~bit ~double_lambda ~double_neg_mu ~cache
        ~add_lambda ~add_neg_mu
  done ;
  !result

let circuit_ranges =
  [| (1, 13); (13, 24); (24, 35); (35, 47); (47, 59); (59, 65) |]

(** Build the circuit body for an ate loop circuit (zkp0-5). *)
let build ~(circuit_index : int) (input_hash : Step.Field.t) : Step.Field.t =
  assert (circuit_index >= 0 && circuit_index <= 5) ;
  let begin_idx, end_idx = circuit_ranges.(circuit_index) in
  let f =
    Step.exists Fp12.Circuit.typ ~compute:(fun () ->
        Circuit_witness.get_ate_initial_f ~circuit_index )
  in
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
  let _f_updated = run_chunk f ~begin_idx ~end_idx ~cache in
  Accumulator_hash.combine_hashes
    [ input_hash; Step.Field.of_int circuit_index ]
