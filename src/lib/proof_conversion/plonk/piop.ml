(** PLONK Polynomial IOP verification functions.

    Implements the algebraic checks for the PLONK verifier, matching
    nori's plonk_utils.ts function-by-function.

    All Fr arithmetic uses FF.mul/add/sub with ~f:Bn254_params.r.
    EC point operations use G1.scale/G1.add from the Groth16 infra.

    Reference: nori-proof-conversion/src/plonk/piop/plonk_utils.ts *)

open! Core_kernel
module Step = Pickles.Impls.Step
module FF = Snarky_foreign_field.Foreign_field

let r = Bn254_params.r
let p = Bn254_params.p

(** Canonical assertion on Fr: equivalent to .assertCanonical() in nori. *)
let assert_canonical_fr (x : FF.Field3.t) : FF.FpA.t =
  let fpu = FF.FpU.of_field3_unsafe x in
  match FF.FpA.assert_almost_reduced [ fpu ] ~f:r () with
  | [ a ] ->
      let c = FF.FpC.assert_canonical a ~f:r in
      FF.FpC.to_fpa c
  | _ -> assert false

(** Canonical assertion on Fp. *)
let assert_canonical_fp (x : FF.Field3.t) : FF.FpA.t =
  let fpu = FF.FpU.of_field3_unsafe x in
  match FF.FpA.assert_almost_reduced [ fpu ] ~f:p () with
  | [ a ] ->
      let c = FF.FpC.assert_canonical a ~f:p in
      FF.FpC.to_fpa c
  | _ -> assert false

(** FrC multiply + assertCanonical.
    Matches nori: a.mul(b).assertCanonical() *)
let mul_fr (a : FF.FpA.t) (b : FF.FpA.t) : FF.FpA.t =
  let result = FF.mul (FF.FpA.to_field3 a) (FF.FpA.to_field3 b) ~f:r in
  assert_canonical_fr result

(** FrC add + assertCanonical. *)
let add_fr (a : FF.FpA.t) (b : FF.FpA.t) : FF.FpA.t =
  let result = FF.add (FF.FpA.to_field3 a) (FF.FpA.to_field3 b) ~f:r in
  assert_canonical_fr result

(** FrC sub + assertCanonical. *)
let sub_fr (a : FF.FpA.t) (b : FF.FpA.t) : FF.FpA.t =
  let result = FF.sub (FF.FpA.to_field3 a) (FF.FpA.to_field3 b) ~f:r in
  assert_canonical_fr result

(** FrC negate + assertCanonical. *)
let neg_fr (a : FF.FpA.t) : FF.FpA.t =
  let result = FF.negate (FF.FpA.to_field3 a) ~f:r in
  assert_canonical_fr result

(** Witness the inverse of x, verify by asserting x * inv = 1.
    Matches nori: Provable.witness(FrC, () => x.inv().assertCanonical())
    followed by x.mul(inv).assertEquals(FrC.from(1n)) *)
let inv_fr (x : FF.FpA.t) : FF.FpA.t =
  (* Witness the inverse: allocate 3 limbs *)
  let inv_limbs =
    Array.init 3 ~f:(fun limb_idx ->
      Step.exists Step.Field.typ ~compute:(fun () ->
          let l0, l1, l2 = FF.FpA.to_field3 x in
          let lv0 = FF.field_const_to_bignum (Step.As_prover.read_var l0) in
          let lv1 = FF.field_const_to_bignum (Step.As_prover.read_var l1) in
          let lv2 = FF.field_const_to_bignum (Step.As_prover.read_var l2) in
          let xv = FF.Field3.Constant.combine (lv0, lv1, lv2) in
          let inv_v =
            match FF.bignum_mod_inverse xv ~f:r with
            | Some v -> v
            | None -> Bignum_bigint.zero
          in
          let limbs = FF.Field3.Constant.split inv_v in
          let l0_v, l1_v, l2_v = limbs in
          let v = match limb_idx with
            | 0 -> l0_v | 1 -> l1_v | 2 -> l2_v | _ -> assert false
          in
          FF.bignum_to_field_const v ) )
  in
  let inv_fpu =
    FF.FpU.of_field3_unsafe (inv_limbs.(0), inv_limbs.(1), inv_limbs.(2))
  in
  let inv =
    match FF.FpA.assert_almost_reduced [ inv_fpu ] ~f:r () with
    | [ a ] -> a
    | _ -> assert false
  in
  let product = FF.mul (FF.FpA.to_field3 x) (FF.FpA.to_field3 inv) ~f:r in
  FF.assert_equal product (FF.Field3.of_constant Bignum_bigint.one) ;
  inv

(** Compute zeta^n using binary exponentiation.
    [exp] is the bit decomposition of the exponent (MSB first),
    matching nori's powFr(zeta, vk.domain_size).

    For SP1 domain_size = 2^24, the bit array is [1, 0, 0, ..., 0] (25 elements). *)
let pow_fr (base : FF.FpA.t) ~(exp_bits : int array) : FF.FpA.t =
  let result = ref base in
  for i = 1 to Array.length exp_bits - 1 do
    result := mul_fr !result !result ;
    if exp_bits.(i) = 1 then
      result := mul_fr !result base
  done ;
  !result

(** Evaluate vanishing polynomial: returns (zeta^n, zeta^n - 1).
    Matches nori evalVanishing. *)
let eval_vanishing (zeta : FF.FpA.t) ~(domain_size_bits : int array) :
    FF.FpA.t * FF.FpA.t =
  let zeta_pow_n = pow_fr zeta ~exp_bits:domain_size_bits in
  let one = FF.FpA.of_constant Bignum_bigint.one in
  let zh_eval = sub_fr zeta_pow_n one in
  (zeta_pow_n, zh_eval)

(** Compute alpha^2 * L_0(zeta).
    Matches nori compute_alpha_square_lagrange_0. *)
let compute_alpha_square_lagrange_0 ~(zh_eval : FF.FpA.t) ~(zeta : FF.FpA.t)
    ~(alpha : FF.FpA.t) ~(inv_domain_size : FF.FpA.t) : FF.FpA.t =
  let one = FF.FpA.of_constant Bignum_bigint.one in
  let zeta_minus_1 = sub_fr zeta one in
  let den = inv_fr zeta_minus_1 in
  let den = mul_fr den inv_domain_size in
  let den = mul_fr den alpha in
  let den = mul_fr den alpha in
  mul_fr den zh_eval

(** Fold quotient polynomial (split 0): combine h0, h1, h2 without zh_eval.
    Returns (hx, hy) as circuit point coordinates.
    Matches nori fold_quotient_split_0. *)
let fold_quotient_split_0
    ~(h0_x : FF.FpA.t) ~(h0_y : FF.FpA.t)
    ~(h1_x : FF.FpA.t) ~(h1_y : FF.FpA.t)
    ~(h2_x : FF.FpA.t) ~(h2_y : FF.FpA.t)
    ~(zeta : FF.FpA.t) ~(zeta_pow_n : FF.FpA.t) :
    FF.FpA.t * FF.FpA.t =
  let h0 = { G1.Circuit.x = h0_x; y = h0_y } in
  let h1 = { G1.Circuit.x = h1_x; y = h1_y } in
  let h2 = { G1.Circuit.x = h2_x; y = h2_y } in
  (* zeta_pow_n_plus_2 = zeta_pow_n * zeta * zeta *)
  let zpn2 = mul_fr (mul_fr zeta_pow_n zeta) zeta in
  let zpn2_f3 = FF.FpA.to_field3 zpn2 in
  (* acc = h2.scale(zpn2) *)
  let acc = G1.scale h2 zpn2_f3 in
  let acc = G1.add acc h1 in
  let acc = G1.scale acc zpn2_f3 in
  let acc = G1.add acc h0 in
  let rx = assert_canonical_fp (FF.FpA.to_field3 acc.x) in
  let ry = assert_canonical_fp (FF.FpA.to_field3 acc.y) in
  (rx, ry)

(** Fold quotient polynomial (split 1): scale by zh_eval.
    Matches nori fold_quotient_split_1. *)
let fold_quotient_split_1
    ~(hx : FF.FpA.t) ~(hy : FF.FpA.t)
    ~(zh_eval : FF.FpA.t) :
    FF.FpA.t * FF.FpA.t =
  let acc = { G1.Circuit.x = hx; y = hy } in
  let acc = G1.scale acc (FF.FpA.to_field3 zh_eval) in
  let rx = assert_canonical_fp (FF.FpA.to_field3 acc.x) in
  let ry = assert_canonical_fp (FF.FpA.to_field3 acc.y) in
  (rx, ry)

(** Batch evaluate Lagrange polynomials L_i(zeta) for i = 0..n-1.
    Matches nori batch_eval_lagrange. *)
let batch_eval_lagrange ~(zeta : FF.FpA.t) ~(zh_eval : FF.FpA.t)
    ~(domain_inv : FF.FpA.t) ~(omega : FF.FpA.t) ~(count : int) :
    FF.FpA.t array =
  let one = FF.FpA.of_constant Bignum_bigint.one in
  let common = mul_fr zh_eval domain_inv in
  if count = 0 then [||]
  else begin
    let den_inv = sub_fr zeta one in
    let den = inv_fr den_inv in
    let l0 = mul_fr common den in
    let evals = Array.create ~len:count l0 in
    let wi = ref omega in
    for i = 1 to count - 1 do
      let nom = mul_fr !wi common in
      let den_inv_i = sub_fr zeta !wi in
      let den_i = inv_fr den_inv_i in
      let li = mul_fr nom den_i in
      evals.(i) <- li ;
      wi := mul_fr !wi omega
    done ;
    evals
  end

(** Public input contribution: PI(zeta) = sum_i pi_i * L_i(zeta).
    Matches nori pi_contribution. *)
let pi_contribution ~(pub_inputs : FF.FpA.t array)
    ~(zeta : FF.FpA.t) ~(zh_eval : FF.FpA.t)
    ~(domain_inv : FF.FpA.t) ~(omega : FF.FpA.t) : FF.FpA.t =
  let li_evals =
    batch_eval_lagrange ~zeta ~zh_eval ~domain_inv ~omega
      ~count:(Array.length pub_inputs)
  in
  let acc = ref (mul_fr li_evals.(0) pub_inputs.(0)) in
  for i = 1 to Array.length pub_inputs - 1 do
    let term = mul_fr li_evals.(i) pub_inputs.(i) in
    acc := add_fr !acc term
  done ;
  !acc

(** Custom PI Lagrange for the custom gate commitment.
    Matches nori customPiLagrange.
    Computes: L_i(zeta) * hash_fr(x, y)
    where hash_fr uses BSB22-PLONK hash-to-field.

    TODO: implement hash_fr properly. For now uses a placeholder. *)
let custom_pi_lagrange ~(zeta : FF.FpA.t) ~(zh_eval : FF.FpA.t)
    ~(qcp_wire_x : FF.FpA.t) ~(qcp_wire_y : FF.FpA.t)
    ~(omega_pow_i : FF.FpA.t) ~(omega_pow_i_div_n : FF.FpA.t) : FF.FpA.t =
  (* TODO: HashFr.hash(qcp_wire_x, qcp_wire_y)
     For now, we need to implement the BSB22 hash-to-field.
     This requires 3 SHA-256 hashes + XOR + bit manipulation. *)
  let _h_fr =
    ignore (qcp_wire_x : FF.FpA.t) ;
    ignore (qcp_wire_y : FF.FpA.t) ;
    FF.FpA.of_constant Bignum_bigint.zero (* placeholder *)
  in
  let den_inv = sub_fr zeta omega_pow_i in
  let den = inv_fr den_inv in
  let li = mul_fr (mul_fr zh_eval omega_pow_i_div_n) den in
  mul_fr li _h_fr

(** Opening of the linearized polynomial.
    Matches nori opening_of_linearized_polynomial. *)
let opening_of_linearized_polynomial
    ~(proof : Plonk_accumulator.circuit_proof)
    ~(alpha : FF.FpA.t) ~(beta : FF.FpA.t) ~(gamma : FF.FpA.t)
    ~(pi : FF.FpA.t) ~(alpha_2_l0 : FF.FpA.t) : FF.FpA.t =
  (* s1 = (l(ζ)+β*s1(ζ)+γ) *)
  let s1 =
    add_fr (add_fr (mul_fr proof.s1_at_zeta beta) gamma) proof.l_at_zeta
  in
  (* s2 = (r(ζ)+β*s2(ζ)+γ) *)
  let s2 =
    add_fr (add_fr (mul_fr proof.s2_at_zeta beta) gamma) proof.r_at_zeta
  in
  (* o = (o(ζ)+γ) *)
  let o = add_fr proof.o_at_zeta gamma in
  (* α*Z(μζ)*(l(ζ)+β*s1(ζ)+γ)*(r(ζ)+β*s2(ζ)+γ)*(o(ζ)+γ) *)
  let acc = mul_fr alpha s1 in
  let acc = mul_fr acc proof.grand_product_at_omega_zeta in
  let acc = mul_fr acc s2 in
  let acc = mul_fr acc o in
  (* - [PI(ζ) - α²*L₁(ζ) + α(...)] *)
  let acc = add_fr acc pi in
  let acc = sub_fr acc alpha_2_l0 in
  neg_fr acc

(** Linearized commitment (split 0): ql*l + qr*r + qm*(l*r).
    Matches nori compute_commitment_linearized_polynomial_split_0. *)
let compute_commitment_linearized_polynomial_split_0
    ~(proof : Plonk_accumulator.circuit_proof)
    ~(vk : Plonk_proof.vk) : FF.FpA.t * FF.FpA.t =
  let ql = { G1.Circuit.x = FF.FpA.of_constant vk.ql.x
           ; y = FF.FpA.of_constant vk.ql.y } in
  let qr = { G1.Circuit.x = FF.FpA.of_constant vk.qr.x
           ; y = FF.FpA.of_constant vk.qr.y } in
  let qm = { G1.Circuit.x = FF.FpA.of_constant vk.qm.x
           ; y = FF.FpA.of_constant vk.qm.y } in
  let lcm = G1.scale ql (FF.FpA.to_field3 proof.l_at_zeta) in
  let lcm = G1.add lcm (G1.scale qr (FF.FpA.to_field3 proof.r_at_zeta)) in
  let rl = mul_fr proof.l_at_zeta proof.r_at_zeta in
  let lcm = G1.add lcm (G1.scale qm (FF.FpA.to_field3 rl)) in
  let rx = assert_canonical_fp (FF.FpA.to_field3 lcm.x) in
  let ry = assert_canonical_fp (FF.FpA.to_field3 lcm.y) in
  (rx, ry)

(** Linearized commitment (split 1): add qo, qk, qcp_0, s3 terms.
    Matches nori compute_commitment_linearized_polynomial_split_1. *)
let compute_commitment_linearized_polynomial_split_1
    ~(lcm_x : FF.FpA.t) ~(lcm_y : FF.FpA.t)
    ~(proof : Plonk_accumulator.circuit_proof)
    ~(vk : Plonk_proof.vk)
    ~(beta : FF.FpA.t) ~(gamma : FF.FpA.t) ~(alpha : FF.FpA.t) :
    FF.FpA.t * FF.FpA.t =
  let lcm = { G1.Circuit.x = lcm_x; y = lcm_y } in
  let qo = { G1.Circuit.x = FF.FpA.of_constant vk.qo.x
           ; y = FF.FpA.of_constant vk.qo.y } in
  let qk = { G1.Circuit.x = FF.FpA.of_constant vk.qk.x
           ; y = FF.FpA.of_constant vk.qk.y } in
  let lcm = G1.add lcm (G1.scale qo (FF.FpA.to_field3 proof.o_at_zeta)) in
  let lcm = G1.add lcm qk in
  let qcp_0 = { G1.Circuit.x = proof.qcp_0_wire_x
              ; y = proof.qcp_0_wire_y } in
  let lcm = G1.add lcm (G1.scale qcp_0 (FF.FpA.to_field3 proof.qcp_0_at_zeta)) in
  (* s1 coefficient *)
  let p1 = add_fr (add_fr (mul_fr proof.s1_at_zeta beta) gamma) proof.l_at_zeta in
  let p2 = add_fr (add_fr (mul_fr proof.s2_at_zeta beta) gamma) proof.r_at_zeta in
  let s1_coeff = mul_fr (mul_fr (mul_fr (mul_fr p1 p2) beta) alpha)
      proof.grand_product_at_omega_zeta in
  let s3 = { G1.Circuit.x = FF.FpA.of_constant vk.s3.x
           ; y = FF.FpA.of_constant vk.s3.y } in
  let lcm = G1.add lcm (G1.scale s3 (FF.FpA.to_field3 s1_coeff)) in
  let rx = assert_canonical_fp (FF.FpA.to_field3 lcm.x) in
  let ry = assert_canonical_fp (FF.FpA.to_field3 lcm.y) in
  (rx, ry)

(** Linearized commitment (split 2): grand product + neg folded quotient.
    Matches nori compute_commitment_linearized_polynomial_split_2. *)
let compute_commitment_linearized_polynomial_split_2
    ~(lcm_x : FF.FpA.t) ~(lcm_y : FF.FpA.t)
    ~(proof : Plonk_accumulator.circuit_proof)
    ~(vk : Plonk_proof.vk)
    ~(beta : FF.FpA.t) ~(gamma : FF.FpA.t) ~(alpha : FF.FpA.t)
    ~(zeta : FF.FpA.t) ~(alpha_2_l0 : FF.FpA.t)
    ~(hx : FF.FpA.t) ~(hy : FF.FpA.t) : FF.FpA.t * FF.FpA.t =
  let lcm = { G1.Circuit.x = lcm_x; y = lcm_y } in
  let coset = FF.FpA.of_constant vk.coset_shift in
  let r1 = add_fr (add_fr (mul_fr zeta beta) proof.l_at_zeta) gamma in
  let r2 = add_fr (add_fr (mul_fr (mul_fr beta coset) zeta) proof.r_at_zeta) gamma in
  let r3 = add_fr
    (add_fr (mul_fr (mul_fr (mul_fr beta coset) coset) zeta) proof.o_at_zeta) gamma in
  let s2_coeff =
    add_fr (neg_fr (mul_fr (mul_fr (mul_fr alpha r1) r2) r3)) alpha_2_l0 in
  let gp = { G1.Circuit.x = proof.grand_product_x
           ; y = proof.grand_product_y } in
  let lcm = G1.add lcm (G1.scale gp (FF.FpA.to_field3 s2_coeff)) in
  (* Subtract folded quotient *)
  let neg_hq = G1.negate_constant_y { G1.Circuit.x = hx; y = hy } in
  let lcm = G1.add lcm neg_hq in
  let rx = assert_canonical_fp (FF.FpA.to_field3 lcm.x) in
  let ry = assert_canonical_fp (FF.FpA.to_field3 lcm.y) in
  (rx, ry)

(** Fold state (split 0): accumulate l, r commitments + all openings.
    Matches nori fold_state_0. *)
let fold_state_0
    ~(proof : Plonk_accumulator.circuit_proof)
    ~(lcm_x : FF.FpA.t) ~(lcm_y : FF.FpA.t)
    ~(lcm_opening : FF.FpA.t) ~(gamma_kzg : FF.FpA.t) :
    FF.FpA.t * FF.FpA.t * FF.FpA.t =
  let g2 = mul_fr gamma_kzg gamma_kzg in
  let g3 = mul_fr gamma_kzg g2 in
  let g4 = mul_fr gamma_kzg g3 in
  let g5 = mul_fr gamma_kzg g4 in
  let g6 = mul_fr gamma_kzg g5 in
  let l_pt = { G1.Circuit.x = proof.l_com_x; y = proof.l_com_y } in
  let r_pt = { G1.Circuit.x = proof.r_com_x; y = proof.r_com_y } in
  let cm = { G1.Circuit.x = lcm_x; y = lcm_y } in
  let cm = G1.add cm (G1.scale l_pt (FF.FpA.to_field3 gamma_kzg)) in
  let cm = G1.add cm (G1.scale r_pt (FF.FpA.to_field3 g2)) in
  (* Openings accumulation *)
  let op = ref lcm_opening in
  op := add_fr (mul_fr proof.l_at_zeta gamma_kzg) !op ;
  op := add_fr (mul_fr proof.r_at_zeta g2) !op ;
  op := add_fr (mul_fr proof.o_at_zeta g3) !op ;
  op := add_fr (mul_fr proof.s1_at_zeta g4) !op ;
  op := add_fr (mul_fr proof.s2_at_zeta g5) !op ;
  op := add_fr (mul_fr proof.qcp_0_at_zeta g6) !op ;
  let rx = assert_canonical_fp (FF.FpA.to_field3 cm.x) in
  let ry = assert_canonical_fp (FF.FpA.to_field3 cm.y) in
  (rx, ry, !op)

(** Fold state (split 1): add o, s1, s2 commitments.
    Matches nori fold_state_1. *)
let fold_state_1
    ~(proof : Plonk_accumulator.circuit_proof) ~(vk : Plonk_proof.vk)
    ~(cm_x : FF.FpA.t) ~(cm_y : FF.FpA.t)
    ~(gamma_kzg : FF.FpA.t) : FF.FpA.t * FF.FpA.t =
  let g2 = mul_fr gamma_kzg gamma_kzg in
  let g3 = mul_fr gamma_kzg g2 in
  let g4 = mul_fr gamma_kzg g3 in
  let g5 = mul_fr gamma_kzg g4 in
  let o_pt = { G1.Circuit.x = proof.o_com_x; y = proof.o_com_y } in
  let s1_pt = { G1.Circuit.x = FF.FpA.of_constant vk.s1.x
              ; y = FF.FpA.of_constant vk.s1.y } in
  let s2_pt = { G1.Circuit.x = FF.FpA.of_constant vk.s2.x
              ; y = FF.FpA.of_constant vk.s2.y } in
  let cm = { G1.Circuit.x = cm_x; y = cm_y } in
  let cm = G1.add cm (G1.scale o_pt (FF.FpA.to_field3 g3)) in
  let cm = G1.add cm (G1.scale s1_pt (FF.FpA.to_field3 g4)) in
  let cm = G1.add cm (G1.scale s2_pt (FF.FpA.to_field3 g5)) in
  let rx = assert_canonical_fp (FF.FpA.to_field3 cm.x) in
  let ry = assert_canonical_fp (FF.FpA.to_field3 cm.y) in
  (rx, ry)

(** Fold state (split 2): add qcp_0 commitment.
    Matches nori fold_state_2. *)
let fold_state_2
    ~(vk : Plonk_proof.vk)
    ~(cm_x : FF.FpA.t) ~(cm_y : FF.FpA.t)
    ~(gamma_kzg : FF.FpA.t) : FF.FpA.t * FF.FpA.t =
  let g2 = mul_fr gamma_kzg gamma_kzg in
  let g3 = mul_fr gamma_kzg g2 in
  let g4 = mul_fr gamma_kzg g3 in
  let g5 = mul_fr gamma_kzg g4 in
  let g6 = mul_fr gamma_kzg g5 in
  let qcp_0_pt =
    match vk.qcp_0 with
    | Some pt -> { G1.Circuit.x = FF.FpA.of_constant pt.x
                 ; y = FF.FpA.of_constant pt.y }
    | None -> failwith "fold_state_2: VK missing qcp_0"
  in
  let cm = { G1.Circuit.x = cm_x; y = cm_y } in
  let cm = G1.add cm (G1.scale qcp_0_pt (FF.FpA.to_field3 g6)) in
  let rx = assert_canonical_fp (FF.FpA.to_field3 cm.x) in
  let ry = assert_canonical_fp (FF.FpA.to_field3 cm.y) in
  (rx, ry)

(** Prepare pairing (split 0): batch openings + commitments + evals.
    Matches nori preparePairing_0. *)
let prepare_pairing_0
    ~(vk : Plonk_proof.vk)
    ~(proof : Plonk_accumulator.circuit_proof)
    ~(random : FF.FpA.t)
    ~(cm_x : FF.FpA.t) ~(cm_y : FF.FpA.t)
    ~(cm_opening : FF.FpA.t) :
    FF.FpA.t * FF.FpA.t * FF.FpA.t * FF.FpA.t =
  (* Quotients part *)
  let batch_shifted = { G1.Circuit.x = proof.batch_opening_at_zeta_omega_x
                      ; y = proof.batch_opening_at_zeta_omega_y } in
  let folded_q = { G1.Circuit.x = proof.batch_opening_at_zeta_x
                 ; y = proof.batch_opening_at_zeta_y } in
  let folded_q = G1.add folded_q (G1.scale batch_shifted (FF.FpA.to_field3 random)) in
  let neg_folded_q = G1.negate_constant_y folded_q in
  (* Commitment part *)
  let gp = { G1.Circuit.x = proof.grand_product_x
           ; y = proof.grand_product_y } in
  let folded_cm = { G1.Circuit.x = cm_x; y = cm_y } in
  let folded_cm = G1.add folded_cm (G1.scale gp (FF.FpA.to_field3 random)) in
  (* Evals part *)
  let gen = { G1.Circuit.x = FF.FpA.of_constant vk.g1_gen.x
            ; y = FF.FpA.of_constant vk.g1_gen.y } in
  let folded_evals = add_fr (mul_fr proof.grand_product_at_omega_zeta random)
      cm_opening in
  let neg_fe_curve = G1.negate_constant_y
      (G1.scale gen (FF.FpA.to_field3 folded_evals)) in
  let folded_cm = G1.add folded_cm neg_fe_curve in
  ( assert_canonical_fp (FF.FpA.to_field3 folded_cm.x)
  , assert_canonical_fp (FF.FpA.to_field3 folded_cm.y)
  , assert_canonical_fp (FF.FpA.to_field3 neg_folded_q.x)
  , assert_canonical_fp (FF.FpA.to_field3 neg_folded_q.y) )

(** Prepare pairing (split 1): add quotients_g1.
    Matches nori preparePairing_1. *)
let prepare_pairing_1
    ~(vk : Plonk_proof.vk)
    ~(proof : Plonk_accumulator.circuit_proof)
    ~(random : FF.FpA.t)
    ~(folded_cm_x : FF.FpA.t) ~(folded_cm_y : FF.FpA.t)
    ~(zeta : FF.FpA.t) : FF.FpA.t * FF.FpA.t =
  let folded_cm = { G1.Circuit.x = folded_cm_x; y = folded_cm_y } in
  let batch_z = { G1.Circuit.x = proof.batch_opening_at_zeta_x
                ; y = proof.batch_opening_at_zeta_y } in
  let batch_wz = { G1.Circuit.x = proof.batch_opening_at_zeta_omega_x
                 ; y = proof.batch_opening_at_zeta_omega_y } in
  let omega_fr = FF.FpA.of_constant vk.omega in
  let zeta_omega = mul_fr omega_fr zeta in
  let random_zeta_omega = mul_fr random zeta_omega in
  let quotients_g1 = G1.scale batch_z (FF.FpA.to_field3 zeta) in
  let quotients_g1 =
    G1.add quotients_g1
      (G1.scale batch_wz (FF.FpA.to_field3 random_zeta_omega)) in
  let folded_cm = G1.add folded_cm quotients_g1 in
  ( assert_canonical_fp (FF.FpA.to_field3 folded_cm.x)
  , assert_canonical_fp (FF.FpA.to_field3 folded_cm.y) )
