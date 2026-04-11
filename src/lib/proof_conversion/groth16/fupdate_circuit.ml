(** f-update circuit body shared by zkp7-12.

    Each circuit performs cyclotomic squarings on f, multiplying in
    g values from the line accumulation and conditionally multiplying
    by c or c_inv based on the ate loop count bits.

*)

open! Core_kernel
module Step = Pickles.Impls.Step
module WT = Witness_tracker

(** Number of ate loop iterations processed per f-update circuit.
    zkp7: ATE[1..9], zkp8: ATE[10..20], ..., zkp12: ATE[54..64].
    g_start values are cumulative sums of iterations_per_circuit. *)
let iterations_per_circuit = [| 9; 11; 11; 11; 11; 11 |]

let g_start_per_circuit =
  let starts = Array.create ~len:(Array.length iterations_per_circuit) 0 in
  for i = 1 to Array.length starts - 1 do
    starts.(i) <- starts.(i - 1) + iterations_per_circuit.(i - 1)
  done ;
  starts

let build ~(circuit_index : int) (input_hash : Step.Field.t) : Step.Field.t =
  assert (circuit_index >= 7 && circuit_index <= 12) ;
  let idx = circuit_index - 7 in
  let n_iters = iterations_per_circuit.(idx) in
  let g_start = g_start_per_circuit.(idx) in
  let ate = Bn254_params.ate_loop_count in
  (* Witness ALL private inputs first (matching nori's ZkProgram parameter
     witnessing, which happens before the method body runs). *)
  let acc =
    Step.exists Accumulator.typ ~request:(fun () ->
        Groth16_requests.Groth16_accumulator )
  in
  let g_chunk =
    Step.exists (Step.Typ.array ~length:n_iters Fp12.typ) ~request:(fun () ->
        Groth16_requests.G_chunk )
  in
  let lhs_hashes =
    Step.exists (Step.Typ.array ~length:g_start Step.Field.typ)
      ~request:(fun () -> Groth16_requests.Lhs_hashes)
  in
  let n_total = Array.length Bn254_params.ate_loop_count in
  let rhs_start = g_start + n_iters in
  let rhs_len = n_total - rhs_start in
  let rhs_hashes =
    Step.exists (Step.Typ.array ~length:rhs_len Step.Field.typ)
      ~request:(fun () -> Groth16_requests.Rhs_hashes)
  in
  (* Now compute hashes and assertions (method body). *)
  let acc_hash = Accumulator.hash acc in
  Step.Field.Assert.equal input_hash acc_hash ;
  let opening =
    Array_list_hasher.open_ ~lhs:lhs_hashes ~opening:g_chunk ~rhs:rhs_hashes
  in
  Step.Field.Assert.equal acc.state.g_digest opening ;
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

(** Same as [build] but returns (hash, updated_acc) for aux_output chaining. *)
let build_with_acc ~(circuit_index : int) (input_hash : Step.Field.t) :
    Step.Field.t * Accumulator.Circuit.t =
  assert (circuit_index >= 7 && circuit_index <= 12) ;
  let idx = circuit_index - 7 in
  let n_iters = iterations_per_circuit.(idx) in
  let g_start = g_start_per_circuit.(idx) in
  let ate = Bn254_params.ate_loop_count in
  let acc =
    Step.exists Accumulator.typ ~request:(fun () ->
        Groth16_requests.Groth16_accumulator )
  in
  let g_chunk =
    Step.exists (Step.Typ.array ~length:n_iters Fp12.typ) ~request:(fun () ->
        Groth16_requests.G_chunk )
  in
  let lhs_hashes =
    Step.exists (Step.Typ.array ~length:g_start Step.Field.typ)
      ~request:(fun () -> Groth16_requests.Lhs_hashes)
  in
  let n_total = Array.length Bn254_params.ate_loop_count in
  let rhs_start = g_start + n_iters in
  let rhs_len = n_total - rhs_start in
  let rhs_hashes =
    Step.exists (Step.Typ.array ~length:rhs_len Step.Field.typ)
      ~request:(fun () -> Groth16_requests.Rhs_hashes)
  in
  let acc_hash = Accumulator.hash acc in
  Step.Field.Assert.equal input_hash acc_hash ;
  let opening =
    Array_list_hasher.open_ ~lhs:lhs_hashes ~opening:g_chunk ~rhs:rhs_hashes
  in
  Step.Field.Assert.equal acc.state.g_digest opening ;
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
  (Accumulator.hash updated_acc, updated_acc)
