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
  Step.exists Plonk_accumulator.typ
    ~compute:(fun () -> Plonk_accumulator.default_const)

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
       Circuit_utils.marker 9001 ;
       let in_digest = Plonk_accumulator.hash_packed acc in
       Step.assert_ (Equal (in_digest, input_hash)) ;
       Circuit_utils.marker 9002 ;
       let cm_x, cm_y =
         Piop.fold_state_1
           ~proof:acc.proof ~vk:plonk_vk
           ~cm_x:acc.state.cm_x ~cm_y:acc.state.cm_y
           ~gamma_kzg:acc.fs.gamma_kzg
       in
       Circuit_utils.marker 9003 ;
       acc.state.cm_x <- cm_x ;
       acc.state.cm_y <- cm_y ;
       Circuit_utils.marker 9004 ;
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
      (* Prepare pairing (split 1) + KZG accumulator initialization.
         Matches nori zkp12. Transitions from Accumulator to KzgAccumulator. *)
      fun input_hash ->
       let acc = witness_accumulator () in
       let in_digest = Plonk_accumulator.hash_packed acc in
       Step.assert_ (Equal (in_digest, input_hash)) ;
       let kzg_cm_x, kzg_cm_y =
         Piop.prepare_pairing_1
           ~vk:plonk_vk ~proof:acc.proof
           ~random:acc.state.kzg_random
           ~folded_cm_x:acc.state.kzg_cm_x
           ~folded_cm_y:acc.state.kzg_cm_y
           ~zeta:acc.fs.zeta
       in
       (* Witness c (Fp12) and compute c_inv = conjugate(c) *)
       let c = Fp12.witness () in
       let c_inv = Fp12.conjugate c in
       (* Witness shift_power *)
       let shift_power =
         Step.exists Step.Field.typ
           ~compute:(fun () -> Step.Field.Constant.zero)
       in
       (* Build KzgAccumulator *)
       let kzg_acc : Kzg_accumulator.t =
         { proof =
             { a_x = kzg_cm_x; a_y = kzg_cm_y
             ; neg_b_x = acc.state.neg_fq_x; neg_b_y = acc.state.neg_fq_y
             ; shift_power
             ; c; c_inv
             ; pi0 = acc.state.pi0; pi1 = acc.state.pi1
             }
         ; state =
             { f = c_inv
             ; lines_hashes_digest = Step.Field.zero
             }
         }
       in
       Kzg_accumulator.hash_packed kzg_acc
  | 13 | 14 | 15 | 16 ->
      (* Miller loop line computation (4 chunks).
         zkp13: ATE[1..19], zkp14: ATE[19..39], zkp15: ATE[39..59], zkp16: ATE[59..65]+Frobenius.
         Witnesses KzgAccumulator + lines_hashes, computes g values from
         precomputed lines, hashes g into lines_hashes, updates digest.
         TODO: LineParser/G2Line.psi/sparse_mul for exact line computation.
         For now: witness g values and hash them. *)
      fun input_hash ->
       let kzg = Kzg_accumulator.witness () in
       let in_digest = Kzg_accumulator.hash_packed kzg in
       Step.assert_ (Equal (in_digest, input_hash)) ;
       (* Witness lines_hashes array (ATE_LOOP_COUNT.length fields) *)
       let lines_hashes =
         Array.init Kzg_accumulator.ate_loop_len ~f:(fun _ ->
             Step.exists Step.Field.typ
               ~compute:(fun () -> Step.Field.Constant.zero) )
       in
       (* Verify lines_hashes digest *)
       let lines_digest = Accumulator_hash.poseidon_hash lines_hashes in
       Step.assert_ (Equal (kzg.state.lines_hashes_digest, lines_digest)) ;
       (* TODO: compute g values from precomputed lines.
          For now, use witnessed g values (hashed into lines_hashes). *)
       (* Update digest *)
       kzg.state.lines_hashes_digest <- Accumulator_hash.poseidon_hash lines_hashes ;
       Kzg_accumulator.hash_packed kzg
  | 17 ->
      (* Miller loop f-accumulation: iterations 1-9.
         Matches nori zkp17. *)
      fun input_hash ->
       let kzg = Kzg_accumulator.witness () in
       let in_digest = Kzg_accumulator.hash_packed kzg in
       Step.assert_ (Equal (in_digest, input_hash)) ;
       let ate = Kzg_accumulator.ate_loop_count in
       (* Witness g_chunk: 9 Fp12 values *)
       let g_chunk = Array.init 9 ~f:(fun _ -> Fp12.witness ()) in
       (* f-update loop: for i = 1 to 9 *)
       let f = ref kzg.state.f in
       for i = 0 to 8 do
         f := Fp12.mul (Fp12.square !f) g_chunk.(i) ;
         if ate.(i + 1) = 1 then
           f := Fp12.mul !f kzg.proof.c_inv
         else if ate.(i + 1) = -1 then
           f := Fp12.mul !f kzg.proof.c
       done ;
       kzg.state.f <- !f ;
       Kzg_accumulator.hash_packed kzg
  | 18 ->
      (* Miller loop f-accumulation: iterations 10-20. *)
      fun input_hash ->
       let kzg = Kzg_accumulator.witness () in
       let in_digest = Kzg_accumulator.hash_packed kzg in
       Step.assert_ (Equal (in_digest, input_hash)) ;
       let ate = Kzg_accumulator.ate_loop_count in
       let g_chunk = Array.init 11 ~f:(fun _ -> Fp12.witness ()) in
       let f = ref kzg.state.f in
       for i = 0 to 10 do
         f := Fp12.mul (Fp12.square !f) g_chunk.(i) ;
         if ate.(i + 10) = 1 then f := Fp12.mul !f kzg.proof.c_inv
         else if ate.(i + 10) = -1 then f := Fp12.mul !f kzg.proof.c
       done ;
       kzg.state.f <- !f ;
       Kzg_accumulator.hash_packed kzg
  | 19 ->
      (* Miller loop f-accumulation: iterations 21-31. *)
      fun input_hash ->
       let kzg = Kzg_accumulator.witness () in
       let in_digest = Kzg_accumulator.hash_packed kzg in
       Step.assert_ (Equal (in_digest, input_hash)) ;
       let ate = Kzg_accumulator.ate_loop_count in
       let g_chunk = Array.init 11 ~f:(fun _ -> Fp12.witness ()) in
       let f = ref kzg.state.f in
       for i = 0 to 10 do
         f := Fp12.mul (Fp12.square !f) g_chunk.(i) ;
         if ate.(i + 21) = 1 then f := Fp12.mul !f kzg.proof.c_inv
         else if ate.(i + 21) = -1 then f := Fp12.mul !f kzg.proof.c
       done ;
       kzg.state.f <- !f ;
       Kzg_accumulator.hash_packed kzg
  | 20 ->
      (* Miller loop f-accumulation: iterations 32-42. *)
      fun input_hash ->
       let kzg = Kzg_accumulator.witness () in
       let in_digest = Kzg_accumulator.hash_packed kzg in
       Step.assert_ (Equal (in_digest, input_hash)) ;
       let ate = Kzg_accumulator.ate_loop_count in
       let g_chunk = Array.init 11 ~f:(fun _ -> Fp12.witness ()) in
       let f = ref kzg.state.f in
       for i = 0 to 10 do
         f := Fp12.mul (Fp12.square !f) g_chunk.(i) ;
         if ate.(i + 32) = 1 then f := Fp12.mul !f kzg.proof.c_inv
         else if ate.(i + 32) = -1 then f := Fp12.mul !f kzg.proof.c
       done ;
       kzg.state.f <- !f ;
       Kzg_accumulator.hash_packed kzg
  | 21 ->
      (* Miller loop f-accumulation: iterations 43-53. *)
      fun input_hash ->
       let kzg = Kzg_accumulator.witness () in
       let in_digest = Kzg_accumulator.hash_packed kzg in
       Step.assert_ (Equal (in_digest, input_hash)) ;
       let ate = Kzg_accumulator.ate_loop_count in
       let g_chunk = Array.init 11 ~f:(fun _ -> Fp12.witness ()) in
       let f = ref kzg.state.f in
       for i = 0 to 10 do
         f := Fp12.mul (Fp12.square !f) g_chunk.(i) ;
         if ate.(i + 43) = 1 then f := Fp12.mul !f kzg.proof.c_inv
         else if ate.(i + 43) = -1 then f := Fp12.mul !f kzg.proof.c
       done ;
       kzg.state.f <- !f ;
       Kzg_accumulator.hash_packed kzg
  | 22 ->
      (* Miller loop f-accumulation: iterations 54-64. *)
      fun input_hash ->
       let kzg = Kzg_accumulator.witness () in
       let in_digest = Kzg_accumulator.hash_packed kzg in
       Step.assert_ (Equal (in_digest, input_hash)) ;
       let ate = Kzg_accumulator.ate_loop_count in
       let g_chunk = Array.init 11 ~f:(fun _ -> Fp12.witness ()) in
       let f = ref kzg.state.f in
       for i = 0 to 10 do
         f := Fp12.mul (Fp12.square !f) g_chunk.(i) ;
         if ate.(i + 54) = 1 then f := Fp12.mul !f kzg.proof.c_inv
         else if ate.(i + 54) = -1 then f := Fp12.mul !f kzg.proof.c
       done ;
       kzg.state.f <- !f ;
       Kzg_accumulator.hash_packed kzg
  | 23 ->
      (* Final pairing check: multiply final g, Frobenius, shift power, verify f=1.
         Matches nori zkp23. *)
      fun input_hash ->
       let kzg = Kzg_accumulator.witness () in
       let in_digest = Kzg_accumulator.hash_packed kzg in
       Step.assert_ (Equal (in_digest, input_hash)) ;
       let g_last = Fp12.witness () in
       let f = ref (Fp12.mul kzg.state.f g_last) in
       (* Frobenius endomorphisms *)
       f := Fp12.mul !f (Fp12.frobenius_pow_p kzg.proof.c_inv) ;
       f := Fp12.mul !f (Fp12.frobenius_pow_p_squared kzg.proof.c) ;
       f := Fp12.mul !f (Fp12.frobenius_pow_p_cubed kzg.proof.c_inv) ;
       (* TODO: shift power selection via Provable.switch *)
       (* Verify f = 1 *)
       Fp12.assert_one !f ;
       kzg.state.f <- !f ;
       (* Output: hash of [pi0, pi1] as packed fields *)
       let pi_input : Step.Field.t Random_oracle_input.Chunked.t =
         { field_elements = [||]
         ; packeds =
             (let l = 88 in
              let add_fpa acc (x : FF.FpA.t) =
                let l0, l1, l2 = FF.FpA.to_field3 x in
                (l0, l) :: (l1, l) :: (l2, l) :: acc
              in
              let ps = add_fpa (add_fpa [] kzg.proof.pi1) kzg.proof.pi0 in
              Array.of_list ps)
         }
       in
       let packed_fields = Random_oracle.Checked.pack_input pi_input in
       Random_oracle.Checked.hash packed_fields
  | n ->
      failwith (sprintf "Invalid PLONK circuit index: %d" n)
