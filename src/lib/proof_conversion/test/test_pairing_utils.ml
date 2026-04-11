(** Debug: step-by-step g[0] computation matching nori's trace. *)
open Core_kernel

module BI = Bignum_bigint
module WT = Proof_conversion.Witness_tracker

let () =
  let proof =
    Proof_conversion.Proof_json.load_proof "/tmp/groth16_test/proof.json"
  in
  let vk = Proof_conversion.Proof_json.load_vk "/tmp/groth16_test/vk.json" in
  let aux =
    Proof_conversion.Proof_json.load_aux_witness
      "/tmp/groth16_test/aux_witness.json"
  in
  let tracker = WT.create ~proof ~vk ~aux in
  let iter0 = WT.get_iteration tracker 0 in
  (* Replicate nori's step-by-step evaluation *)
  let neg_a = WT.get_neg_a tracker in
  let c_g1 = WT.get_c tracker in
  let pi_g1 = WT.get_pi tracker in
  let x_over_y_a, y_inv_a = WT.compute_affine_cache neg_a in
  let x_over_y_c, y_inv_c = WT.compute_affine_cache c_g1 in
  let x_over_y_pi, y_inv_pi = WT.compute_affine_cache pi_g1 in
  Printf.eprintf "negA: x=%s y=%s\n%!" (BI.to_string neg_a.x)
    (BI.to_string neg_a.y) ;
  Printf.eprintf "x_over_y_a = %s\n%!" (BI.to_string x_over_y_a) ;
  Printf.eprintf "y_inv_a = %s\n%!" (BI.to_string y_inv_a) ;
  (* Test Fp.neg directly *)
  let neg_x = WT.Fp.neg neg_a.x in
  Printf.eprintf "Fp.neg(negA.x) = %s\n%!" (BI.to_string neg_x) ;
  Printf.eprintf
    "expected       = \
     5423043772130670931547852745232333088645280792537984573734451532401466023180\n\
     %!" ;
  let manual_xoy = WT.Fp.mul neg_x y_inv_a in
  Printf.eprintf "manual neg_x * y_inv = %s\n%!" (BI.to_string manual_xoy) ;
  let eval line ~xoy ~yinv = WT.evaluate_line line ~x_over_y:xoy ~y_inv:yinv in
  (* Step 1: b_double at negA *)
  let b_double = eval iter0.double_line ~xoy:x_over_y_a ~yinv:y_inv_a in
  let ((g00, _), _, _), _ = b_double in
  Printf.eprintf "After b_double: g00 = %s\n%!" (BI.to_string g00) ;
  (* Step 2: * delta_double at C *)
  let delta_double =
    eval iter0.delta_double_line ~xoy:x_over_y_c ~yinv:y_inv_c
  in
  let g0 = WT.Fp12.mul b_double delta_double in
  let ((g00, _), _, _), _ = g0 in
  Printf.eprintf "After * delta_double: g00 = %s\n%!" (BI.to_string g00) ;
  (* Step 3: * gamma_double at PI *)
  let gamma_double =
    eval iter0.gamma_double_line ~xoy:x_over_y_pi ~yinv:y_inv_pi
  in
  let g0 = WT.Fp12.mul g0 gamma_double in
  let ((g00, _), _, _), _ = g0 in
  Printf.eprintf "After * gamma_double: g00 = %s\n%!" (BI.to_string g00) ;
  (* Step 4: * b_add at negA *)
  let b_add =
    eval (Option.value_exn iter0.add_line) ~xoy:x_over_y_a ~yinv:y_inv_a
  in
  let ( ((ba00, ba01), (ba10, ba11), (ba20, ba21))
      , ((bb00, bb01), (bb10, bb11), (bb20, bb21)) ) =
    b_add
  in
  Printf.eprintf "b_add eval: g00=%s g01=%s h00=%s h01=%s h10=%s h11=%s\n%!"
    (BI.to_string ba00) (BI.to_string ba01) (BI.to_string bb00)
    (BI.to_string bb01) (BI.to_string bb10) (BI.to_string bb11) ;
  Printf.eprintf "  g10=%s g11=%s g20=%s g21=%s h20=%s h21=%s\n%!"
    (BI.to_string ba10) (BI.to_string ba11) (BI.to_string ba20)
    (BI.to_string ba21) (BI.to_string bb20) (BI.to_string bb21) ;
  let g0 = WT.Fp12.mul g0 b_add in
  let ((g00, _), _, _), _ = g0 in
  Printf.eprintf "After * b_add: g00 = %s\n%!" (BI.to_string g00) ;
  (* Step 5: * delta_add at C *)
  let delta_add =
    eval (Option.value_exn iter0.delta_add_line) ~xoy:x_over_y_c ~yinv:y_inv_c
  in
  let g0 = WT.Fp12.mul g0 delta_add in
  let ((g00, _), _, _), _ = g0 in
  Printf.eprintf "After * delta_add: g00 = %s\n%!" (BI.to_string g00) ;
  (* Step 6: * gamma_add at PI *)
  let gamma_add =
    eval (Option.value_exn iter0.gamma_add_line) ~xoy:x_over_y_pi ~yinv:y_inv_pi
  in
  let g0 = WT.Fp12.mul g0 gamma_add in
  let ((g00, _), _, _), _ = g0 in
  Printf.eprintf "After * gamma_add (FINAL): g00 = %s\n%!" (BI.to_string g00) ;
  Printf.eprintf
    "\n\
     Expected g[0].g00 = \
     9540063242468609762263434931656028753839003313656528339925282735494360041259\n\
     %!" ;
  Printf.eprintf "Done.\n%!"
