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

(** SP1 PLONK domain size as bit array (MSB first): 2^24 = [1, 0, ..., 0]. *)
let domain_size_bits = Array.init 25 ~f:(fun i -> if i = 0 then 1 else 0)

(** SP1 PLONK verification key, matching nori vk.ts.
    Source: https://github.com/succinctlabs/sp1-contracts/blob/main/contracts/src/v5.0.0/PlonkVerifier.sol *)
let plonk_vk : Plonk_proof.vk =
  let bi = Bignum_bigint.of_string in
  let g1 x y = { G1.Constant.x = bi x; y = bi y } in
  { domain_size = sp1_domain_size
  ; domain_size_bits
  ; inv_domain_size = bi
      "21888241567198334088790460357988866238279339518792980768180410072331574733841"
  ; omega = bi
      "5709868443893258075976348696661355716898495876243883251619397131511003808859"
  ; coset_shift = bi "5"
  ; g1_gen = g1
      "14312776538779914388377568895031746459131577658076416373430523308756343304251"
      "11763105256161367503191792604679297387056316997144156930871823008787082098465"
  ; ql = g1
      "2714773032566361735398260413518107570706289019141573602093747023461681138141"
      "10207220609888567477852282724812707756861966294950666667119692155077205992894"
  ; qr = g1
      "17919274808167168584263187859012763816365260341587621260815379357637476029962"
      "14558165337321799812085033100515533981610351056305142204990949940017867076397"
  ; qm = g1
      "1814703450159964740292891910795980721108620081843240976053374083376051887455"
      "11252528960397523304289223453506717847025678682133692300385063157160041127070"
  ; qo = g1
      "20843277058771674275997213106654908867381045039357421108797602213552545033079"
      "9646775541123942436366130063934415659078920798926708026864638413383214238671"
  ; qk = g1
      "5484717465597821820411103650564499774744032473047103693751158150047197753654"
      "5561799343038529497262757012400750786503050088440144551259537360162821571059"
  ; s1 = g1
      "16111562061301112215931665617877464360548491176332584512747295033804502769274"
      "15035232142063390140879951391784254536324051421746307325879221184372296043705"
  ; s2 = g1
      "899944321381010541211546037826620464002745326050515852312919625047231523882"
      "61717668739330555376092528203839789132705738484346798874082062974863965392"
  ; s3 = g1
      "9316901462569250008665217603385561854185385862824092362271612343176126127375"
      "13799900238612879579721466063922041459340434537392216736920805107993374657577"
  ; qcp_0 = Some (g1
      "21578473557091588309361521643625606794648013014197133181947992670819103775934"
      "18236588362476326695195531997097392315059481348147701548685746610417604595065")
  ; omega_pow_i = bi
      "15264034983190160489087025353457580488037346987271988310592699973668284917022"
  ; omega_pow_i_div_n = bi
      "16425161602643719872686085382713730563148030929298303959135645596481976986620"
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
       Fiat_shamir.squeeze_alpha acc.fs ~proof:acc.proof ;
       Fiat_shamir.squeeze_zeta acc.fs ~proof:acc.proof ;
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
         Matches nori zkp7. *)
      fun input_hash ->
       let acc = witness_accumulator () in
       let in_digest = Plonk_accumulator.hash_packed acc in
       Step.assert_ (Equal (in_digest, input_hash)) ;
       let h = Fiat_shamir.gamma_kzg_digest_part0 acc.fs
         ~proof:acc.proof ~vk:plonk_vk
         ~linearized_cm_x:acc.state.lcm_x
         ~linearized_cm_y:acc.state.lcm_y
         ~linearized_opening:acc.state.linearized_opening in
       acc.state.h_state <- h ;
       Plonk_accumulator.hash_packed acc
  | 8 ->
      (* KZG digest part 1 + squeeze gamma_kzg + fold state 0.
         Matches nori zkp8. *)
      fun input_hash ->
       let acc = witness_accumulator () in
       let in_digest = Plonk_accumulator.hash_packed acc in
       Step.assert_ (Equal (in_digest, input_hash)) ;
       Fiat_shamir.gamma_kzg_digest_part1 acc.fs
         ~proof:acc.proof ~h_state:acc.state.h_state ;
       Fiat_shamir.squeeze_gamma_kzg_from_digest acc.fs ;
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
         Matches nori zkp10. *)
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
       let kzg_random = Fiat_shamir.squeeze_random_for_kzg acc.fs
         ~proof:acc.proof ~cm_x ~cm_y in
       acc.state.cm_x <- cm_x ;
       acc.state.cm_y <- cm_y ;
       acc.state.kzg_random <- kzg_random ;
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
       (* Nori witnesses all private inputs [Accumulator, Field, Fp12] at start *)
       let acc = witness_accumulator () in
       let shift_power =
         Step.exists Step.Field.typ
           ~compute:(fun () -> Step.Field.Constant.zero)
       in
       let c = Fp12.witness () in
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
       let c_inv = Fp12.inverse c in
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
             ; lines_hashes_digest = Kzg_accumulator.array_list_hasher_empty
             }
         }
       in
       Kzg_accumulator.hash_packed kzg_acc
  | 13 | 14 | 15 | 16 ->
      (* Miller loop line computation (4 chunks).
         zkp13: ATE[1..ATE_LEN-46], zkp14: ATE[ATE_LEN-46..ATE_LEN-26],
         zkp15: ATE[ATE_LEN-26..ATE_LEN-6], zkp16: ATE[ATE_LEN-6..ATE_LEN-1]+Frobenius.
         Matches nori zkp13-16. *)
      let ate = Kzg_accumulator.ate_loop_count in
      let ate_len = Array.length ate in
      let from_, to_ = match circuit_index with
        | 13 -> (1, ate_len - 46)
        | 14 -> (ate_len - 46, ate_len - 26)
        | 15 -> (ate_len - 26, ate_len - 6)
        | 16 -> (ate_len - 6, ate_len)
        | _ -> assert false
      in
      (* Load precomputed lines for this chunk *)
      let data_dir = "src/lib/proof_conversion/plonk/data" in
      let all_g2 = Plonk_lines.load_lines_from_json
        (data_dir ^ "/g2_lines.json") in
      let all_tau = Plonk_lines.load_lines_from_json
        (data_dir ^ "/tau_lines.json") in
      let g2_lines = Plonk_lines.parse_g2 all_g2 ~from:from_ ~to_:to_ in
      let tau_lines = Plonk_lines.parse_tau all_tau ~from:from_ ~to_:to_ in
      fun input_hash ->
       let kzg = Kzg_accumulator.witness () in
       let in_digest = Kzg_accumulator.hash_packed kzg in
       Step.assert_ (Equal (in_digest, input_hash)) ;
       (* Witness lines_hashes array *)
       let lines_hashes =
         Array.init Kzg_accumulator.ate_loop_len ~f:(fun _ ->
             Step.exists Step.Field.typ
               ~compute:(fun () -> Step.Field.Constant.zero) )
       in
       let lines_digest = Accumulator_hash.poseidon_hash lines_hashes in
       Step.assert_ (Equal (kzg.state.lines_hashes_digest, lines_digest)) ;
       (* Create affine caches *)
       let a_cache = Lines.AffineCache.make
         { G1.Circuit.x = kzg.proof.a_x; y = kzg.proof.a_y } in
       let b_cache = Lines.AffineCache.make
         { G1.Circuit.x = kzg.proof.neg_b_x; y = kzg.proof.neg_b_y } in
       (* Compute g values from precomputed lines *)
       let line_cnt = ref 0 in
       for i = from_ to to_ - 1 do
         let idx = i - 1 in
         let g_line = Lines.G2Line.of_constant g2_lines.(!line_cnt) in
         let tau_line = Lines.G2Line.of_constant tau_lines.(!line_cnt) in
         incr line_cnt ;
         let g = Lines.psi g_line a_cache in
         let g = Fp12.sparse_mul g (Lines.psi tau_line b_cache) in
         let g =
           if ate.(i) = 1 || ate.(i) = -1 then begin
             let g_line2 = Lines.G2Line.of_constant g2_lines.(!line_cnt) in
             let tau_line2 = Lines.G2Line.of_constant tau_lines.(!line_cnt) in
             incr line_cnt ;
             let g = Fp12.sparse_mul g (Lines.psi g_line2 a_cache) in
             Fp12.sparse_mul g (Lines.psi tau_line2 b_cache)
           end else g
         in
         lines_hashes.(idx) <- Accumulator_hash.hash_fp12 g
       done ;
       (* Handle Frobenius for zkp16 *)
       ( if circuit_index = 16 then begin
         let frob_g2_1, frob_g2_2 = Plonk_lines.frobenius_lines all_g2 in
         let frob_tau_1, frob_tau_2 = Plonk_lines.frobenius_lines all_tau in
         let g2_1 = Lines.G2Line.of_constant frob_g2_1 in
         let tau_1 = Lines.G2Line.of_constant frob_tau_1 in
         let g2_2 = Lines.G2Line.of_constant frob_g2_2 in
         let tau_2 = Lines.G2Line.of_constant frob_tau_2 in
         let g = Lines.psi g2_1 a_cache in
         let g = Fp12.sparse_mul g (Lines.psi tau_1 b_cache) in
         let g = Fp12.sparse_mul g (Lines.psi g2_2 a_cache) in
         let g = Fp12.sparse_mul g (Lines.psi tau_2 b_cache) in
         lines_hashes.(ate_len - 1) <- Accumulator_hash.hash_fp12 g
       end ) ;
       (* Update digest *)
       kzg.state.lines_hashes_digest <- Accumulator_hash.poseidon_hash lines_hashes ;
       Kzg_accumulator.hash_packed kzg
  | 17 | 18 | 19 | 20 | 21 | 22 ->
      (* Miller loop f-accumulation chunks.
         zkp17: ATE[1..10), zkp18: ATE[10..21), zkp19: ATE[21..32),
         zkp20: ATE[32..43), zkp21: ATE[43..54), zkp22: ATE[54..65).
         Matches nori zkp17-22. *)
      let ate = Kzg_accumulator.ate_loop_count in
      let ate_len = Array.length ate in
      let from_i, to_i, chunk_size, lhs_size = match circuit_index with
        | 17 -> (1, 10, 9, 0)
        | 18 -> (10, 21, 11, 9)
        | 19 -> (21, 32, 11, 20)
        | 20 -> (32, 43, 11, 31)
        | 21 -> (43, 54, 11, 42)
        | 22 -> (54, 65, 11, 53)
        | _ -> assert false
      in
      let rhs_size = ate_len - lhs_size - chunk_size in
      fun input_hash ->
       (* Nori witnesses all private inputs at start:
          [KzgAccumulator, Array(Fp12, chunk_size), Array(Field, ate_len-chunk_size)] *)
       let kzg = Kzg_accumulator.witness () in
       let g_chunk = Array.init chunk_size ~f:(fun _ -> Fp12.witness ()) in
       let remaining = ate_len - chunk_size in
       let flat_hashes = Array.init remaining ~f:(fun _ ->
           Step.exists Step.Field.typ ~compute:(fun () -> Step.Field.Constant.zero)) in
       let lhs_hashes = Array.sub flat_hashes ~pos:0 ~len:lhs_size in
       let rhs_hashes = Array.sub flat_hashes ~pos:lhs_size ~len:rhs_size in
       let in_digest = Kzg_accumulator.hash_packed kzg in
       Step.assert_ (Equal (in_digest, input_hash)) ;
       (* ArrayListHasher.open: hash g_chunk, concat lhs ++ opening_hashes ++ rhs, hash all *)
       let opening_hashes = Array.map g_chunk ~f:Accumulator_hash.hash_fp12 in
       let full_arr = Array.concat [ lhs_hashes; opening_hashes; rhs_hashes ] in
       let opening = Accumulator_hash.poseidon_hash full_arr in
       Step.assert_ (Equal (kzg.state.lines_hashes_digest, opening)) ;
       (* f-update loop *)
       let f = ref kzg.state.f in
       for i = from_i to to_i - 1 do
         let idx = i - from_i in
         f := Fp12.mul (Fp12.square !f) g_chunk.(idx) ;
         if ate.(i) = 1 then f := Fp12.mul !f kzg.proof.c_inv
         else if ate.(i) = -1 then f := Fp12.mul !f kzg.proof.c
       done ;
       kzg.state.f <- !f ;
       Kzg_accumulator.hash_packed kzg
  | 23 ->
      (* Final pairing check: multiply final g, Frobenius, shift power, verify f=1.
         Matches nori zkp23. *)
      let ate_len = Array.length Kzg_accumulator.ate_loop_count in
      fun input_hash ->
       (* Nori witnesses all private inputs at start:
          [KzgAccumulator, Array(Field, 64), Array(Fp12, 1)] *)
       let kzg = Kzg_accumulator.witness () in
       let lhs_hashes = Array.init (ate_len - 1) ~f:(fun _ ->
           Step.exists Step.Field.typ ~compute:(fun () -> Step.Field.Constant.zero)) in
       let g_chunk = Array.init 1 ~f:(fun _ -> Fp12.witness ()) in
       let in_digest = Kzg_accumulator.hash_packed kzg in
       Step.assert_ (Equal (in_digest, input_hash)) ;
       let opening_hashes = Array.map g_chunk ~f:Accumulator_hash.hash_fp12 in
       let full_arr = Array.concat [ lhs_hashes; opening_hashes ] in
       let opening = Accumulator_hash.poseidon_hash full_arr in
       Step.assert_ (Equal (kzg.state.lines_hashes_digest, opening)) ;
       (* f = f.mul(g_chunk[0]) *)
       let f = ref (Fp12.mul kzg.state.f g_chunk.(0)) in
       (* Frobenius endomorphisms *)
       f := Fp12.mul !f (Fp12.frobenius_pow_p kzg.proof.c_inv) ;
       f := Fp12.mul !f (Fp12.frobenius_pow_p_squared kzg.proof.c) ;
       f := Fp12.mul !f (Fp12.frobenius_pow_p_cubed kzg.proof.c_inv) ;
       (* Shift power selection: Provable.switch *)
       let w27 = Fp12.of_constant (Bn254_params.w27 ()) in
       let w27_sq = Fp12.of_constant (Bn254_params.w27_sq ()) in
       (* Nori: shift_power.equals(Field(k)) — direct seal + assertMul,
          NOT chunked equality like Step.Field.equal *)
       let field_equals x c =
         let module FF = Snarky_foreign_field.Foreign_field in
         let diff = FF.seal Step.Field.(x - constant (Step.Field.Constant.of_int c)) in
         let b = Step.exists Step.Field.typ ~compute:(fun () ->
             let xv = Step.As_prover.read_var x in
             if Step.Field.Constant.(equal xv (of_int c)) then Step.Field.Constant.one
             else Step.Field.Constant.zero) in
         let z = Step.exists Step.Field.typ ~compute:(fun () ->
             let dv = Step.As_prover.read_var diff in
             if Step.Field.Constant.(equal dv zero) then Step.Field.Constant.zero
             else Step.Field.Constant.(one / dv)) in
         (* b * diff = 0 *)
         Step.assert_ (R1CS (b, diff, Step.Field.zero)) ;
         (* z * diff = 1 - b *)
         Step.assert_ (R1CS (z, diff, Step.Field.(sub (of_int 1) b))) ;
         b
       in
       let is_0 = field_equals kzg.proof.shift_power 0 in
       let is_1 = field_equals kzg.proof.shift_power 1 in
       let is_2 = field_equals kzg.proof.shift_power 2 in
       let shift = Circuit_utils.provable_switch Fp12.typ
         [| is_0; is_1; is_2 |]
         [| Fp12.one; w27; w27_sq |] in
       f := Fp12.mul !f shift ;
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
