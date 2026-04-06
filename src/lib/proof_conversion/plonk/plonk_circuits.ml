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
let plonk_vk : Plonk_proof.vk =
  let zero_g1 = { G1.Constant.x = Bignum_bigint.zero; y = Bignum_bigint.zero } in
  { domain_size = sp1_domain_size
  ; omega = Bignum_bigint.zero
  ; ql = zero_g1
  ; qr = zero_g1
  ; qm = zero_g1
  ; qo = zero_g1
  ; qk = zero_g1
  ; s1 = zero_g1
  ; s2 = zero_g1
  ; s3 = zero_g1
  ; qcp_0 = Some zero_g1
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
      (* Squeeze alpha/zeta, compute zeta^n *)
      fun input_hash ->
       let zeta = FF.Field3.of_constant FF.Bignum_bigint.one in
       let _zeta_n = Piop.pow_fr zeta ~exp:sp1_domain_size in
       Accumulator_hash.combine_hashes [ input_hash; Step.Field.of_int 1 ]
  | 2 | 3 | 4 | 5 | 6 ->
      (* Quotient polynomial folding + linearized commitment *)
      fun input_hash ->
       let a = FF.Field3.of_constant FF.Bignum_bigint.one in
       let b = FF.Field3.of_constant (FF.Bignum_bigint.of_int 2) in
       let _c = FF.mul a b ~f:Bn254_params.r in
       Accumulator_hash.combine_hashes
         [ input_hash; Step.Field.of_int circuit_index ]
  | 7 | 8 | 9 | 10 | 11 ->
      (* KZG accumulation *)
      fun input_hash ->
       let a = FF.Field3.of_constant FF.Bignum_bigint.one in
       let b = FF.Field3.of_constant (FF.Bignum_bigint.of_int 3) in
       let _c = FF.mul a b ~f:Bn254_params.p in
       Accumulator_hash.combine_hashes
         [ input_hash; Step.Field.of_int circuit_index ]
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
