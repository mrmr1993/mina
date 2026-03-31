(** f-update circuit body shared by zkp7-12.

    Each circuit performs cyclotomic squarings on f, multiplying in
    g values from the line accumulation and conditionally multiplying
    by c or c_inv based on the ate loop count bits.

    Matches nori's zkp7.ts through zkp12.ts. *)

open! Core_kernel
module Step = Pickles.Impls.Step
module WT = Witness_tracker

(** Number of ate loop iterations processed per f-update circuit.
    zkp7: ATE[1..9], zkp8: ATE[10..20], ..., zkp12: ATE[54..64]. *)
let iterations_per_circuit = [| 9; 11; 11; 11; 11; 11 |]

(** Starting g-value index for each f-update circuit. *)
let g_start_per_circuit = [| 0; 9; 20; 31; 42; 53 |]

let build ~(circuit_index : int) (input_hash : Step.Field.t) : Step.Field.t =
  assert (circuit_index >= 7 && circuit_index <= 12) ;
  let idx = circuit_index - 7 in
  let n_iters = iterations_per_circuit.(idx) in
  let g_start = g_start_per_circuit.(idx) in
  let ate = Bn254_params.ate_loop_count in
  let acc =
    Step.exists Accumulator.typ ~compute:(fun () ->
        WT.get_accumulator_constant (Circuit_config.get_tracker ()) )
  in
  let acc_hash = Accumulator.hash acc in
  Step.Field.Assert.equal input_hash acc_hash ;
  let g_chunk =
    Array.init n_iters ~f:(fun i ->
        Step.exists Fp12.Circuit.typ ~compute:(fun () ->
            WT.get_g (Circuit_config.get_tracker ()) (g_start + i) ) )
  in
  let lhs_hashes =
    Array.init g_start ~f:(fun i ->
        Step.exists Step.Field.typ ~compute:(fun () ->
            let tracker = Circuit_config.get_tracker () in
            (WT.get_line_hashes tracker).(i) ) )
  in
  let n_total = Array.length Bn254_params.ate_loop_count in
  let rhs_start = g_start + n_iters in
  let rhs_hashes =
    Array.init (n_total - rhs_start) ~f:(fun i ->
        Step.exists Step.Field.typ ~compute:(fun () ->
            let tracker = Circuit_config.get_tracker () in
            (WT.get_line_hashes tracker).(rhs_start + i) ) )
  in
  let opening =
    Array_list_hasher.open_ ~lhs:lhs_hashes ~opening:g_chunk ~rhs:rhs_hashes
  in
  Step.Field.Assert.equal acc.state.g_digest opening ;
  Fp12._marker_fn :=
    (fun x ->
      Step.assert_
        (Raw
           { kind = Zero
           ; values = [| Step.Field.zero; Step.Field.zero; Step.Field.zero |]
           ; coeffs =
               Array.map ~f:Step.Field.Constant.of_int
                 [| x; 1; 2; 3; 4; 5; 6 |]
           } ) ) ;
  let f = if circuit_index = 7 then acc.proof.c_inv else acc.state.f in
  let result = ref f in
  for i = 0 to n_iters - 1 do
    result := Fp12.cyclotomic_square !result ;
    result := Fp12.mul !result g_chunk.(i) ;
    let ate_idx = g_start + i + 1 in
    if ate_idx < Array.length ate then
      let bit = ate.(ate_idx) in
      if bit = 1 then result := Fp12.mul !result acc.proof.c_inv
      else if bit = -1 then result := Fp12.mul !result acc.proof.c_fp12
  done ;
  let updated_acc : Accumulator.Circuit.t =
    { proof = acc.proof; state = { acc.state with f = !result } }
  in
  Accumulator.hash updated_acc
