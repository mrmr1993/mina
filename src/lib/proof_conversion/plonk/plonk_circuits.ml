(** PLONK proof conversion circuit bodies (24 circuits).

    zkp0:     Squeeze gamma from Fiat-Shamir transcript (SHA-256)
    zkp1:     Squeeze alpha/zeta, compute zeta^n, vanishing eval
    zkp2-6:   Fold quotient polynomial, linearized commitment
    zkp7-11:  KZG accumulation and pairing preparation
    zkp12:    Initialize KZG accumulator (shift_power, c)
    zkp13-16: Hash line coefficients into digest
    zkp17-23: Miller loop computation (shared with Groth16)

    Reference: nori-proof-conversion/src/plonk/recursion/prove_zkps.ts *)

open! Core_kernel
module Step = Pickles.Impls.Step
module FF = Snarky_foreign_field.Foreign_field

type circuit_body = Step.Field.t -> Step.Field.t

let num_circuits = 24

(** SP1 PLONK domain size (2^24). *)
let sp1_domain_size = 16777216

(** Construct a dummy Fp12 circuit value (all-ones). *)
let dummy_fp12 () : Fp12.Circuit.t =
  let fp2 () : Fp2.Circuit.t =
    { Fp2.Circuit.c0 = FF.FpA.of_constant FF.Bignum_bigint.one
    ; c1 = FF.FpA.of_constant FF.Bignum_bigint.one
    }
  in
  let fp6 () : Fp6.Circuit.t =
    { Fp6.Circuit.c0 = fp2 (); c1 = fp2 (); c2 = fp2 () }
  in
  { Fp12.Circuit.c0 = fp6 (); c1 = fp6 () }

(** Placeholder PLONK VK with zero values.
    TODO: Load actual VK constants from SP1 Verifier contract. *)
(** SP1 PLONK domain size as bit array (MSB first): 2^24 = [1, 0, ..., 0]. *)
let domain_size_bits = Array.init 25 ~f:(fun i -> if i = 0 then 1 else 0)

let plonk_vk : Plonk_proof.vk =
  let zero_g1 = { G1.Constant.x = Bignum_bigint.zero; y = Bignum_bigint.zero } in
  { domain_size = sp1_domain_size
  ; domain_size_bits
  ; inv_domain_size =
      Bignum_bigint.of_string
        "21888241567198334088790460357988866238279339518792980768180410072331574733841"
  ; omega = Bignum_bigint.zero  (* TODO: fill from VK *)
  ; coset_shift = Bignum_bigint.zero  (* TODO *)
  ; g1_gen = zero_g1  (* TODO *)
  ; ql = zero_g1
  ; qr = zero_g1
  ; qm = zero_g1
  ; qo = zero_g1
  ; qk = zero_g1
  ; s1 = zero_g1
  ; s2 = zero_g1
  ; s3 = zero_g1
  ; qcp_0 = Some zero_g1
  ; omega_pow_i = Bignum_bigint.zero  (* TODO *)
  ; omega_pow_i_div_n = Bignum_bigint.zero  (* TODO *)
  }

(** Witness a full PLONK Accumulator as private input.
    All fields are witnessed as fresh variables. *)
let witness_accumulator () : Plonk_accumulator.t =
  let witness_fpa () =
    let limbs = Array.init 3 ~f:(fun _ ->
      Step.exists Step.Field.typ
        ~compute:(fun () -> Step.Field.Constant.zero)) in
    FF.FpA.of_field3_unsafe (limbs.(0), limbs.(1), limbs.(2))
  in
  let witness_bytes32 () =
    Array.init 32 ~f:(fun _ ->
        Step.exists Step.Field.typ
          ~compute:(fun () -> Step.Field.Constant.zero) )
  in
  let witness_uint32 () =
    Step.exists Step.Field.typ
      ~compute:(fun () -> Step.Field.Constant.zero)
  in
  let proof : Plonk_accumulator.circuit_proof =
    { l_com_x = witness_fpa ()
    ; l_com_y = witness_fpa ()
    ; r_com_x = witness_fpa ()
    ; r_com_y = witness_fpa ()
    ; o_com_x = witness_fpa ()
    ; o_com_y = witness_fpa ()
    ; h0_x = witness_fpa ()
    ; h0_y = witness_fpa ()
    ; h1_x = witness_fpa ()
    ; h1_y = witness_fpa ()
    ; h2_x = witness_fpa ()
    ; h2_y = witness_fpa ()
    ; l_at_zeta = witness_fpa ()
    ; r_at_zeta = witness_fpa ()
    ; o_at_zeta = witness_fpa ()
    ; s1_at_zeta = witness_fpa ()
    ; s2_at_zeta = witness_fpa ()
    ; grand_product_x = witness_fpa ()
    ; grand_product_y = witness_fpa ()
    ; grand_product_at_omega_zeta = witness_fpa ()
    ; batch_opening_at_zeta_x = witness_fpa ()
    ; batch_opening_at_zeta_y = witness_fpa ()
    ; batch_opening_at_zeta_omega_x = witness_fpa ()
    ; batch_opening_at_zeta_omega_y = witness_fpa ()
    ; qcp_0_at_zeta = witness_fpa ()
    ; qcp_0_wire_x = witness_fpa ()
    ; qcp_0_wire_y = witness_fpa ()
    }
  in
  let fs : Plonk_accumulator.circuit_fs =
    { gamma_digest = witness_bytes32 ()
    ; gamma = witness_fpa ()
    ; beta_digest = witness_bytes32 ()
    ; beta = witness_fpa ()
    ; alpha_digest = witness_bytes32 ()
    ; alpha = witness_fpa ()
    ; zeta_digest = witness_bytes32 ()
    ; zeta = witness_fpa ()
    ; gamma_kzg_digest = witness_bytes32 ()
    ; gamma_kzg = witness_fpa ()
    }
  in
  let state : Plonk_accumulator.circuit_state =
    { pi0 = witness_fpa ()
    ; pi1 = witness_fpa ()
    ; zeta_pow_n = witness_fpa ()
    ; zh_eval = witness_fpa ()
    ; alpha_2_l0 = witness_fpa ()
    ; hx = witness_fpa ()
    ; hy = witness_fpa ()
    ; pi = witness_fpa ()
    ; linearized_opening = witness_fpa ()
    ; lcm_x = witness_fpa ()
    ; lcm_y = witness_fpa ()
    ; cm_x = witness_fpa ()
    ; cm_y = witness_fpa ()
    ; cm_opening = witness_fpa ()
    ; kzg_random = witness_fpa ()
    ; kzg_cm_x = witness_fpa ()
    ; kzg_cm_y = witness_fpa ()
    ; neg_fq_x = witness_fpa ()
    ; neg_fq_y = witness_fpa ()
    ; h_state = Array.init 8 ~f:(fun _ -> witness_uint32 ())
    }
  in
  { proof; fs; state }

let build_circuit_body ~(circuit_index : int) : circuit_body =
  match circuit_index with
  | 0 ->
      (* Squeeze gamma and beta: Fiat-Shamir SHA-256 challenges.
         Matches nori zkp0: hash accumulator, squeezeGamma, squeezeBeta,
         hash updated accumulator. *)
      fun input_hash ->
       (* Witness the full Accumulator as private input *)
       let acc = witness_accumulator () in
       (* Verify input hash — generate the Equal constraint.
          Note: during domain computation the prover values are dummy,
          so we use assert_ directly to avoid prover-time check. *)
       let in_digest = Plonk_accumulator.hash_packed acc in
       Step.assert_ (Equal (in_digest, input_hash)) ;
       (* Squeeze gamma and beta *)
       Fiat_shamir.squeeze_gamma acc.fs ~proof:acc.proof
         ~pi0:acc.state.pi0 ~pi1:acc.state.pi1
         ~vk:plonk_vk ;
       Fiat_shamir.squeeze_beta acc.fs ;
       (* Hash updated accumulator for output *)
       Plonk_accumulator.hash_packed acc
  | 1 ->
      (* Squeeze alpha/zeta, compute zeta^n, vanishing eval, alpha^2*L_0.
         Matches nori zkp1. *)
      fun input_hash ->
       let acc = witness_accumulator () in
       let in_digest = Plonk_accumulator.hash_packed acc in
       Step.assert_ (Equal (in_digest, input_hash)) ;
       (* squeezeAlpha and squeezeZeta — TODO: implement in fiat_shamir.ml.
          For now, use the fs.alpha/zeta values already in the accumulator. *)
       (* Compute zeta^n and vanishing evaluation *)
       let zeta_pow_n, zh_eval =
         Piop.eval_vanishing acc.fs.zeta
           ~domain_size_bits:plonk_vk.domain_size_bits
       in
       let inv_domain_size =
         FF.FpA.of_constant plonk_vk.inv_domain_size
       in
       let alpha_2_l0 =
         Piop.compute_alpha_square_lagrange_0
           ~zh_eval ~zeta:acc.fs.zeta ~alpha:acc.fs.alpha
           ~inv_domain_size
       in
       acc.state.zeta_pow_n <- zeta_pow_n ;
       acc.state.zh_eval <- zh_eval ;
       acc.state.alpha_2_l0 <- alpha_2_l0 ;
       Plonk_accumulator.hash_packed acc
  | 2 ->
      (* Fold quotient polynomial (split 0): combine h0, h1, h2.
         Matches nori zkp2. *)
      fun input_hash ->
       let acc = witness_accumulator () in
       let in_digest = Plonk_accumulator.hash_packed acc in
       Step.assert_ (Equal (in_digest, input_hash)) ;
       let hx, hy =
         Piop.fold_quotient_split_0
           ~h0_x:acc.proof.h0_x ~h0_y:acc.proof.h0_y
           ~h1_x:acc.proof.h1_x ~h1_y:acc.proof.h1_y
           ~h2_x:acc.proof.h2_x ~h2_y:acc.proof.h2_y
           ~zeta:acc.fs.zeta ~zeta_pow_n:acc.state.zeta_pow_n
       in
       acc.state.hx <- hx ;
       acc.state.hy <- hy ;
       Plonk_accumulator.hash_packed acc
  | 3 ->
      (* Fold quotient (split 1) + PI contribution + linearized opening.
         Matches nori zkp3. *)
      fun input_hash ->
       let acc = witness_accumulator () in
       let in_digest = Plonk_accumulator.hash_packed acc in
       Step.assert_ (Equal (in_digest, input_hash)) ;
       (* Scale folded quotient by zh_eval *)
       let hx, hy =
         Piop.fold_quotient_split_1
           ~hx:acc.state.hx ~hy:acc.state.hy
           ~zh_eval:acc.state.zh_eval
       in
       acc.state.hx <- hx ;
       acc.state.hy <- hy ;
       (* Public input contribution *)
       let inv_domain_size =
         FF.FpA.of_constant plonk_vk.inv_domain_size
       in
       let omega = FF.FpA.of_constant plonk_vk.omega in
       let pis =
         Piop.pi_contribution
           ~pub_inputs:[| acc.state.pi0; acc.state.pi1 |]
           ~zeta:acc.fs.zeta ~zh_eval:acc.state.zh_eval
           ~domain_inv:inv_domain_size ~omega
       in
       (* Custom PI Lagrange *)
       let omega_pow_i = FF.FpA.of_constant plonk_vk.omega_pow_i in
       let omega_pow_i_div_n =
         FF.FpA.of_constant plonk_vk.omega_pow_i_div_n
       in
       let l_pi_commit =
         Piop.custom_pi_lagrange ~zeta:acc.fs.zeta
           ~zh_eval:acc.state.zh_eval
           ~qcp_wire_x:acc.proof.qcp_0_wire_x
           ~qcp_wire_y:acc.proof.qcp_0_wire_y
           ~omega_pow_i ~omega_pow_i_div_n
       in
       let pi = Piop.add_fr pis l_pi_commit in
       (* Opening of linearized polynomial *)
       let linearized_opening =
         Piop.opening_of_linearized_polynomial
           ~proof:acc.proof
           ~alpha:acc.fs.alpha ~beta:acc.fs.beta ~gamma:acc.fs.gamma
           ~pi ~alpha_2_l0:acc.state.alpha_2_l0
       in
       acc.state.pi <- pi ;
       acc.state.linearized_opening <- linearized_opening ;
       Plonk_accumulator.hash_packed acc
  | 4 ->
      (* Linearized commitment (split 0): ql*l + qr*r + qm*(l*r).
         Matches nori zkp4. *)
      fun input_hash ->
       let acc = witness_accumulator () in
       let in_digest = Plonk_accumulator.hash_packed acc in
       Step.assert_ (Equal (in_digest, input_hash)) ;
       let lcm_x, lcm_y =
         Piop.compute_commitment_linearized_polynomial_split_0
           ~proof:acc.proof ~vk:plonk_vk
       in
       acc.state.lcm_x <- lcm_x ;
       acc.state.lcm_y <- lcm_y ;
       Plonk_accumulator.hash_packed acc
  | 5 ->
      (* Linearized commitment (split 1): add qo, qk, qcp_0, s3.
         Matches nori zkp5. *)
      fun input_hash ->
       let acc = witness_accumulator () in
       let in_digest = Plonk_accumulator.hash_packed acc in
       Step.assert_ (Equal (in_digest, input_hash)) ;
       let lcm_x, lcm_y =
         Piop.compute_commitment_linearized_polynomial_split_1
           ~lcm_x:acc.state.lcm_x ~lcm_y:acc.state.lcm_y
           ~proof:acc.proof ~vk:plonk_vk
           ~beta:acc.fs.beta ~gamma:acc.fs.gamma ~alpha:acc.fs.alpha
       in
       acc.state.lcm_x <- lcm_x ;
       acc.state.lcm_y <- lcm_y ;
       Plonk_accumulator.hash_packed acc
  | 6 ->
      (* Linearized commitment (split 2): grand product + neg quotient.
         Matches nori zkp6. *)
      fun input_hash ->
       let acc = witness_accumulator () in
       let in_digest = Plonk_accumulator.hash_packed acc in
       Step.assert_ (Equal (in_digest, input_hash)) ;
       let lcm_x, lcm_y =
         Piop.compute_commitment_linearized_polynomial_split_2
           ~lcm_x:acc.state.lcm_x ~lcm_y:acc.state.lcm_y
           ~proof:acc.proof ~vk:plonk_vk
           ~beta:acc.fs.beta ~gamma:acc.fs.gamma ~alpha:acc.fs.alpha
           ~zeta:acc.fs.zeta ~alpha_2_l0:acc.state.alpha_2_l0
           ~hx:acc.state.hx ~hy:acc.state.hy
       in
       acc.state.lcm_x <- lcm_x ;
       acc.state.lcm_y <- lcm_y ;
       Plonk_accumulator.hash_packed acc
  | 7 ->
      (* KZG digest part 0: first 11 blocks of SHA-256 for gamma_kzg.
         TODO: implement gammaKzgDigest_part0. Uses partial SHA-256. *)
      fun input_hash ->
       let acc = witness_accumulator () in
       let in_digest = Plonk_accumulator.hash_packed acc in
       Step.assert_ (Equal (in_digest, input_hash)) ;
       (* TODO: acc.fs.gammaKzgDigest_part0(...) → acc.state.H *)
       Plonk_accumulator.hash_packed acc
  | 8 ->
      (* KZG digest part 1 + fold state 0.
         TODO: implement gammaKzgDigest_part1 + squeezeGammaKzgFromDigest. *)
      fun input_hash ->
       let acc = witness_accumulator () in
       let in_digest = Plonk_accumulator.hash_packed acc in
       Step.assert_ (Equal (in_digest, input_hash)) ;
       (* TODO: gammaKzgDigest_part1, squeezeGammaKzgFromDigest *)
       let cm_x, cm_y, cm_opening =
         Piop.fold_state_0
           ~proof:acc.proof
           ~lcm_x:acc.state.lcm_x ~lcm_y:acc.state.lcm_y
           ~lcm_opening:acc.state.linearized_opening
           ~gamma_kzg:acc.fs.gamma_kzg
       in
       acc.state.cm_x <- cm_x ;
       acc.state.cm_y <- cm_y ;
       acc.state.cm_opening <- cm_opening ;
       Plonk_accumulator.hash_packed acc
  | 9 ->
      (* Fold state 1: add o, s1, s2 commitments.
         Matches nori zkp9. *)
      fun input_hash ->
       let acc = witness_accumulator () in
       let in_digest = Plonk_accumulator.hash_packed acc in
       Step.assert_ (Equal (in_digest, input_hash)) ;
       let cm_x, cm_y =
         Piop.fold_state_1
           ~proof:acc.proof ~vk:plonk_vk
           ~cm_x:acc.state.cm_x ~cm_y:acc.state.cm_y
           ~gamma_kzg:acc.fs.gamma_kzg
       in
       acc.state.cm_x <- cm_x ;
       acc.state.cm_y <- cm_y ;
       Plonk_accumulator.hash_packed acc
  | 10 ->
      (* Fold state 2 + squeeze KZG random.
         Matches nori zkp10.
         TODO: implement squeezeRandomForKzg. *)
      fun input_hash ->
       let acc = witness_accumulator () in
       let in_digest = Plonk_accumulator.hash_packed acc in
       Step.assert_ (Equal (in_digest, input_hash)) ;
       let cm_x, cm_y =
         Piop.fold_state_2
           ~vk:plonk_vk
           ~cm_x:acc.state.cm_x ~cm_y:acc.state.cm_y
           ~gamma_kzg:acc.fs.gamma_kzg
       in
       (* TODO: kzg_random = squeezeRandomForKzg(proof, cm_x, cm_y) *)
       acc.state.cm_x <- cm_x ;
       acc.state.cm_y <- cm_y ;
       Plonk_accumulator.hash_packed acc
  | 11 ->
      (* Prepare pairing (split 0).
         Matches nori zkp11. *)
      fun input_hash ->
       let acc = witness_accumulator () in
       let in_digest = Plonk_accumulator.hash_packed acc in
       Step.assert_ (Equal (in_digest, input_hash)) ;
       let kzg_cm_x, kzg_cm_y, neg_fq_x, neg_fq_y =
         Piop.prepare_pairing_0
           ~vk:plonk_vk ~proof:acc.proof
           ~random:acc.state.kzg_random
           ~cm_x:acc.state.cm_x ~cm_y:acc.state.cm_y
           ~cm_opening:acc.state.cm_opening
       in
       acc.state.kzg_cm_x <- kzg_cm_x ;
       acc.state.kzg_cm_y <- kzg_cm_y ;
       acc.state.neg_fq_x <- neg_fq_x ;
       acc.state.neg_fq_y <- neg_fq_y ;
       Plonk_accumulator.hash_packed acc
  | 12 ->
      (* Initialize KZG accumulator *)
      fun input_hash ->
       let c = dummy_fp12 () in
       let _c_inv = Fp12.conjugate c in
       Accumulator_hash.combine_hashes [ input_hash; Step.Field.of_int 12 ]
  | 13 | 14 | 15 | 16 ->
      (* Hash line coefficients: Fp12 values → Poseidon digest *)
      fun input_hash ->
       let g = dummy_fp12 () in
       let _hash = Accumulator_hash.hash_fp12 g in
       Accumulator_hash.combine_hashes
         [ input_hash; Step.Field.of_int circuit_index ]
  | 17 | 18 | 19 | 20 | 21 | 22 | 23 ->
      (* Miller loop computation (shared structure with Groth16) *)
      fun input_hash ->
       let f = dummy_fp12 () in
       let g = dummy_fp12 () in
       let f_sq = Fp12.square f in
       let _result = Fp12.mul f_sq g in
       Accumulator_hash.combine_hashes
         [ input_hash; Step.Field.of_int circuit_index ]
  | n ->
      failwith (sprintf "Invalid PLONK circuit index: %d" n)
