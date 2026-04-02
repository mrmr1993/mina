(** Precomputed verification key constants for Groth16 circuits.

    Line coefficients are precomputed from the VK's delta and gamma
    G2 points at circuit definition time, and embedded as circuit
    constants (not witnesses).

    The flat line arrays contain, for each ate iteration, a double
    line followed by an add line (when the ate bit is non-zero),
    plus 2 frobenius lines at the end. *)

open! Core_kernel
module WT = Witness_tracker

type t =
  { delta_lines : WT.Line.t array  (** All delta line coefficients (91 entries) *)
  ; gamma_lines : WT.Line.t array  (** All gamma line coefficients (91 entries) *)
  ; alpha_beta : Fp12.Constant.t
  ; w27 : Fp12.Constant.t
  ; ic : G1.Constant.t array
  }

(** Compute all line coefficients from a G2 point.  Produces the
    flat array: for each ate
    iteration i in [1,65), a double line + optional add line,
    then 2 frobenius lines at the end. *)
let compute_line_coeffs (pt : WT.G2.t) : WT.Line.t array =
  let ate = Bn254_params.ate_loop_count in
  let neg_pt = WT.G2.negate pt in
  let lines = Queue.create () in
  let current = ref pt in
  for i = 1 to Array.length ate - 1 do
    let double_line, new_pt = WT.compute_double_line !current in
    current := new_pt ;
    Queue.enqueue lines double_line ;
    let bit = ate.(i) in
    if bit = 1 then (
      let add_line, new_pt = WT.compute_add_line !current pt in
      current := new_pt ;
      Queue.enqueue lines add_line )
    else if bit = -1 then (
      let add_line, new_pt = WT.compute_add_line !current neg_pt in
      current := new_pt ;
      Queue.enqueue lines add_line )
  done ;
  (* Frobenius lines *)
  let pi_pt = WT.G2.frobenius pt in
  let frob_line1, after1 = WT.compute_add_line !current pi_pt in
  Queue.enqueue lines frob_line1 ;
  let pi2_pt = WT.G2.negative_frobenius pi_pt in
  let frob_line2, _after2 = WT.compute_add_line after1 pi2_pt in
  Queue.enqueue lines frob_line2 ;
  Queue.to_array lines

(** Create VK constants from a parsed verification key. *)
let create (vk : Proof_json.vk) : t =
  let delta = WT.G2.of_proof_json vk.delta in
  let gamma = WT.G2.of_proof_json vk.gamma in
  { delta_lines = compute_line_coeffs delta
  ; gamma_lines = compute_line_coeffs gamma
  ; alpha_beta = vk.alpha_beta
  ; w27 = vk.w27
  ; ic = vk.ic
  }
