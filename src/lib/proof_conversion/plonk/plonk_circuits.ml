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
  ; inv_domain_size =
      bi
        "21888241567198334088790460357988866238279339518792980768180410072331574733841"
  ; omega =
      bi
        "5709868443893258075976348696661355716898495876243883251619397131511003808859"
  ; coset_shift = bi "5"
  ; g1_gen =
      g1
        "14312776538779914388377568895031746459131577658076416373430523308756343304251"
        "11763105256161367503191792604679297387056316997144156930871823008787082098465"
  ; ql =
      g1
        "2714773032566361735398260413518107570706289019141573602093747023461681138141"
        "10207220609888567477852282724812707756861966294950666667119692155077205992894"
  ; qr =
      g1
        "17919274808167168584263187859012763816365260341587621260815379357637476029962"
        "14558165337321799812085033100515533981610351056305142204990949940017867076397"
  ; qm =
      g1
        "1814703450159964740292891910795980721108620081843240976053374083376051887455"
        "11252528960397523304289223453506717847025678682133692300385063157160041127070"
  ; qo =
      g1
        "20843277058771674275997213106654908867381045039357421108797602213552545033079"
        "9646775541123942436366130063934415659078920798926708026864638413383214238671"
  ; qk =
      g1
        "5484717465597821820411103650564499774744032473047103693751158150047197753654"
        "5561799343038529497262757012400750786503050088440144551259537360162821571059"
  ; s1 =
      g1
        "16111562061301112215931665617877464360548491176332584512747295033804502769274"
        "15035232142063390140879951391784254536324051421746307325879221184372296043705"
  ; s2 =
      g1
        "899944321381010541211546037826620464002745326050515852312919625047231523882"
        "61717668739330555376092528203839789132705738484346798874082062974863965392"
  ; s3 =
      g1
        "9316901462569250008665217603385561854185385862824092362271612343176126127375"
        "13799900238612879579721466063922041459340434537392216736920805107993374657577"
  ; qcp_0 =
      Some
        (g1
           "21578473557091588309361521643625606794648013014197133181947992670819103775934"
           "18236588362476326695195531997097392315059481348147701548685746610417604595065" )
  ; omega_pow_i =
      bi
        "15264034983190160489087025353457580488037346987271988310592699973668284917022"
  ; omega_pow_i_div_n =
      bi
        "16425161602643719872686085382713730563148030929298303959135645596481976986620"
  }

(** Witness a full PLONK Accumulator as private input via request. *)
let witness_accumulator () : Plonk_accumulator.t =
  Step.exists Plonk_accumulator.typ ~request:(fun () ->
      Plonk_requests.Plonk_accumulator )

(** Witness a full KZG Accumulator as private input via request. *)
let witness_kzg_accumulator () : Kzg_accumulator.t =
  Step.exists Kzg_accumulator.typ ~request:(fun () ->
      Plonk_requests.Kzg_accumulator )

(** Circuits 0-11: witness Plonk_accumulator, mutate, return (hash, acc).
    The [inner] function performs the circuit-specific mutations. *)
let plonk_acc_body (inner : Plonk_accumulator.t -> unit) input_hash :
    Step.Field.t * Plonk_accumulator.t =
  let acc = witness_accumulator () in
  let in_digest = Plonk_accumulator.hash_packed acc in
  Step.assert_ (Equal (in_digest, input_hash)) ;
  inner acc ;
  (Plonk_accumulator.hash_packed acc, acc)

(** zkp0: Squeeze gamma and beta. *)
let zkp0 input_hash =
  plonk_acc_body
    (fun acc ->
      Fiat_shamir.squeeze_gamma acc.fs ~proof:acc.proof ~pi0:acc.state.pi0
        ~pi1:acc.state.pi1 ~vk:plonk_vk ;
      Fiat_shamir.squeeze_beta acc.fs )
    input_hash

(** zkp1: Squeeze alpha/zeta, compute vanishing eval, alpha^2*L_0. *)
let zkp1 input_hash =
  plonk_acc_body
    (fun acc ->
      Fiat_shamir.squeeze_alpha acc.fs ~proof:acc.proof ;
      Fiat_shamir.squeeze_zeta acc.fs ~proof:acc.proof ;
      let zeta_pow_n, zh_eval =
        Piop.eval_vanishing acc.fs.zeta
          ~domain_size_bits:plonk_vk.domain_size_bits
      in
      let inv_domain_size = FF.FpA.of_constant plonk_vk.inv_domain_size in
      let alpha_2_l0 =
        Piop.compute_alpha_square_lagrange_0 ~zh_eval ~zeta:acc.fs.zeta
          ~alpha:acc.fs.alpha ~inv_domain_size
      in
      acc.state.zeta_pow_n <- zeta_pow_n ;
      acc.state.zh_eval <- zh_eval ;
      acc.state.alpha_2_l0 <- alpha_2_l0 )
    input_hash

(** zkp2: Fold quotient polynomial (split 0). *)
let zkp2 input_hash =
  plonk_acc_body
    (fun acc ->
      let hx, hy =
        Piop.fold_quotient_split_0 ~h0_x:acc.proof.h0_x ~h0_y:acc.proof.h0_y
          ~h1_x:acc.proof.h1_x ~h1_y:acc.proof.h1_y ~h2_x:acc.proof.h2_x
          ~h2_y:acc.proof.h2_y ~zeta:acc.fs.zeta
          ~zeta_pow_n:acc.state.zeta_pow_n
      in
      acc.state.hx <- hx ;
      acc.state.hy <- hy )
    input_hash

(** zkp3: Fold quotient (split 1), PI contribution, linearized opening. *)
let zkp3 input_hash =
  plonk_acc_body
    (fun acc ->
      let hx, hy =
        Piop.fold_quotient_split_1 ~hx:acc.state.hx ~hy:acc.state.hy
          ~zh_eval:acc.state.zh_eval
      in
      acc.state.hx <- hx ;
      acc.state.hy <- hy ;
      let inv_domain_size = FF.FpA.of_constant plonk_vk.inv_domain_size in
      let omega = FF.FpA.of_constant plonk_vk.omega in
      let pis =
        Piop.pi_contribution
          ~pub_inputs:[| acc.state.pi0; acc.state.pi1 |]
          ~zeta:acc.fs.zeta ~zh_eval:acc.state.zh_eval
          ~domain_inv:inv_domain_size ~omega
      in
      let omega_pow_i = FF.FpA.of_constant plonk_vk.omega_pow_i in
      let omega_pow_i_div_n = FF.FpA.of_constant plonk_vk.omega_pow_i_div_n in
      let l_pi_commit =
        Piop.custom_pi_lagrange ~zeta:acc.fs.zeta ~zh_eval:acc.state.zh_eval
          ~qcp_wire_x:acc.proof.qcp_0_wire_x ~qcp_wire_y:acc.proof.qcp_0_wire_y
          ~omega_pow_i ~omega_pow_i_div_n
      in
      let pi = Piop.add_fr pis l_pi_commit in
      let linearized_opening =
        Piop.opening_of_linearized_polynomial ~proof:acc.proof
          ~alpha:acc.fs.alpha ~beta:acc.fs.beta ~gamma:acc.fs.gamma ~pi
          ~alpha_2_l0:acc.state.alpha_2_l0
      in
      acc.state.pi <- pi ;
      acc.state.linearized_opening <- linearized_opening )
    input_hash

(** zkp4: Linearized commitment (split 0). *)
let zkp4 input_hash =
  plonk_acc_body
    (fun acc ->
      let lcm_x, lcm_y =
        Piop.compute_commitment_linearized_polynomial_split_0 ~proof:acc.proof
          ~vk:plonk_vk
      in
      acc.state.lcm_x <- lcm_x ;
      acc.state.lcm_y <- lcm_y )
    input_hash

(** zkp5: Linearized commitment (split 1). *)
let zkp5 input_hash =
  plonk_acc_body
    (fun acc ->
      let lcm_x, lcm_y =
        Piop.compute_commitment_linearized_polynomial_split_1
          ~lcm_x:acc.state.lcm_x ~lcm_y:acc.state.lcm_y ~proof:acc.proof
          ~vk:plonk_vk ~beta:acc.fs.beta ~gamma:acc.fs.gamma ~alpha:acc.fs.alpha
      in
      acc.state.lcm_x <- lcm_x ;
      acc.state.lcm_y <- lcm_y )
    input_hash

(** zkp6: Linearized commitment (split 2). *)
let zkp6 input_hash =
  plonk_acc_body
    (fun acc ->
      let lcm_x, lcm_y =
        Piop.compute_commitment_linearized_polynomial_split_2
          ~lcm_x:acc.state.lcm_x ~lcm_y:acc.state.lcm_y ~proof:acc.proof
          ~vk:plonk_vk ~beta:acc.fs.beta ~gamma:acc.fs.gamma ~alpha:acc.fs.alpha
          ~zeta:acc.fs.zeta ~alpha_2_l0:acc.state.alpha_2_l0 ~hx:acc.state.hx
          ~hy:acc.state.hy
      in
      acc.state.lcm_x <- lcm_x ;
      acc.state.lcm_y <- lcm_y )
    input_hash

(** zkp7: KZG digest part 0. *)
let zkp7 input_hash =
  plonk_acc_body
    (fun acc ->
      let h =
        Fiat_shamir.gamma_kzg_digest_part0 acc.fs ~proof:acc.proof ~vk:plonk_vk
          ~linearized_cm_x:acc.state.lcm_x ~linearized_cm_y:acc.state.lcm_y
          ~linearized_opening:acc.state.linearized_opening
      in
      acc.state.h_state <- h )
    input_hash

(** zkp8: KZG digest part 1, squeeze gamma_kzg, fold state 0. *)
let zkp8 input_hash =
  plonk_acc_body
    (fun acc ->
      Fiat_shamir.gamma_kzg_digest_part1 acc.fs ~proof:acc.proof
        ~h_state:acc.state.h_state ;
      Fiat_shamir.squeeze_gamma_kzg_from_digest acc.fs ;
      let cm_x, cm_y, cm_opening =
        Piop.fold_state_0 ~proof:acc.proof ~lcm_x:acc.state.lcm_x
          ~lcm_y:acc.state.lcm_y ~lcm_opening:acc.state.linearized_opening
          ~gamma_kzg:acc.fs.gamma_kzg
      in
      acc.state.cm_x <- cm_x ;
      acc.state.cm_y <- cm_y ;
      acc.state.cm_opening <- cm_opening )
    input_hash

(** zkp9: Fold state 1. *)
let zkp9 input_hash =
  plonk_acc_body
    (fun acc ->
      let cm_x, cm_y =
        Piop.fold_state_1 ~proof:acc.proof ~vk:plonk_vk ~cm_x:acc.state.cm_x
          ~cm_y:acc.state.cm_y ~gamma_kzg:acc.fs.gamma_kzg
      in
      acc.state.cm_x <- cm_x ;
      acc.state.cm_y <- cm_y )
    input_hash

(** zkp10: Fold state 2, squeeze KZG random. *)
let zkp10 input_hash =
  plonk_acc_body
    (fun acc ->
      let cm_x, cm_y =
        Piop.fold_state_2 ~vk:plonk_vk ~cm_x:acc.state.cm_x ~cm_y:acc.state.cm_y
          ~gamma_kzg:acc.fs.gamma_kzg
      in
      let kzg_random =
        Fiat_shamir.squeeze_random_for_kzg acc.fs ~proof:acc.proof ~cm_x ~cm_y
      in
      acc.state.cm_x <- cm_x ;
      acc.state.cm_y <- cm_y ;
      acc.state.kzg_random <- kzg_random )
    input_hash

(** zkp11: Prepare pairing (split 0). *)
let zkp11 input_hash =
  plonk_acc_body
    (fun acc ->
      let kzg_cm_x, kzg_cm_y, neg_fq_x, neg_fq_y =
        Piop.prepare_pairing_0 ~vk:plonk_vk ~proof:acc.proof
          ~random:acc.state.kzg_random ~cm_x:acc.state.cm_x ~cm_y:acc.state.cm_y
          ~cm_opening:acc.state.cm_opening
      in
      acc.state.kzg_cm_x <- kzg_cm_x ;
      acc.state.kzg_cm_y <- kzg_cm_y ;
      acc.state.neg_fq_x <- neg_fq_x ;
      acc.state.neg_fq_y <- neg_fq_y )
    input_hash

(** zkp12: Prepare pairing (split 1) + KZG accumulator initialization.
    Transitions from Plonk_accumulator to Kzg_accumulator.
    Returns (output_hash, kzg_acc) for chaining to zkp13+. *)
let zkp12 input_hash : Step.Field.t * Kzg_accumulator.t =
  let acc = witness_accumulator () in
  let shift_power =
    Step.exists Step.Field.typ ~request:(fun () -> Plonk_requests.Shift_power)
  in
  let c = Step.exists Fp12.typ ~request:(fun () -> Plonk_requests.C_fp12) in
  let in_digest = Plonk_accumulator.hash_packed acc in
  Step.assert_ (Equal (in_digest, input_hash)) ;
  let kzg_cm_x, kzg_cm_y =
    Piop.prepare_pairing_1 ~vk:plonk_vk ~proof:acc.proof
      ~random:acc.state.kzg_random ~folded_cm_x:acc.state.kzg_cm_x
      ~folded_cm_y:acc.state.kzg_cm_y ~zeta:acc.fs.zeta
  in
  let c_inv = Fp12.inverse c in
  let kzg_acc : Kzg_accumulator.t =
    { proof =
        { a_x = kzg_cm_x
        ; a_y = kzg_cm_y
        ; neg_b_x = acc.state.neg_fq_x
        ; neg_b_y = acc.state.neg_fq_y
        ; shift_power
        ; c
        ; c_inv
        ; pi0 = acc.state.pi0
        ; pi1 = acc.state.pi1
        }
    ; state =
        { f = c_inv
        ; lines_hashes_digest = Kzg_accumulator.array_list_hasher_empty
        }
    }
  in
  (Kzg_accumulator.hash_packed kzg_acc, kzg_acc)

(** zkp13-16: Miller loop line computation.
    Each circuit computes g values from precomputed lines for a chunk of
    the ATE loop, then hashes them into lines_hashes.
    Returns (hash, kzg, lines_hashes, g_values) — the g_values are the
    raw Fp12 line evaluations needed by zkp17-23. *)
let zkp_lines ~circuit_index input_hash :
    Step.Field.t * Kzg_accumulator.t * Step.Field.t array * Fp12.Circuit.t array
    =
  let ate = Kzg_accumulator.ate_loop_count in
  let ate_len = Array.length ate in
  let from_, to_ =
    match circuit_index with
    | 13 ->
        (1, ate_len - 46)
    | 14 ->
        (ate_len - 46, ate_len - 26)
    | 15 ->
        (ate_len - 26, ate_len - 6)
    | 16 ->
        (ate_len - 6, ate_len)
    | _ ->
        assert false
  in
  let data_dir = "src/lib/proof_conversion/plonk/data" in
  let all_g2 = Plonk_lines.load_lines_from_json (data_dir ^ "/g2_lines.json") in
  let all_tau =
    Plonk_lines.load_lines_from_json (data_dir ^ "/tau_lines.json")
  in
  let g2_lines = Plonk_lines.parse_g2 all_g2 ~from:from_ ~to_ in
  let tau_lines = Plonk_lines.parse_tau all_tau ~from:from_ ~to_ in
  let kzg = witness_kzg_accumulator () in
  let in_digest = Kzg_accumulator.hash_packed kzg in
  Step.assert_ (Equal (in_digest, input_hash)) ;
  let lines_hashes =
    Step.exists
      (Step.Typ.array ~length:Kzg_accumulator.ate_loop_len Step.Field.typ)
      ~request:(fun () -> Plonk_requests.Lines_hashes)
  in
  let lines_digest = Accumulator_hash.poseidon_hash lines_hashes in
  Step.assert_ (Equal (kzg.state.lines_hashes_digest, lines_digest)) ;
  let a_cache =
    Lines.AffineCache.make { G1.Circuit.x = kzg.proof.a_x; y = kzg.proof.a_y }
  in
  let b_cache =
    Lines.AffineCache.make
      { G1.Circuit.x = kzg.proof.neg_b_x; y = kzg.proof.neg_b_y }
  in
  (* Collect g values for use by zkp17-23 *)
  let g_values = Queue.create () in
  let line_cnt = ref 0 in
  for i = from_ to to_ - 1 do
    let idx = i - 1 in
    let g_line = Lines.G2Line.of_constant g2_lines.(!line_cnt) in
    let tau_line = Lines.G2Line.of_constant tau_lines.(!line_cnt) in
    incr line_cnt ;
    let g = Lines.psi g_line a_cache in
    let g = Fp12.sparse_mul g (Lines.psi tau_line b_cache) in
    let g =
      if ate.(i) = 1 || ate.(i) = -1 then (
        let g_line2 = Lines.G2Line.of_constant g2_lines.(!line_cnt) in
        let tau_line2 = Lines.G2Line.of_constant tau_lines.(!line_cnt) in
        incr line_cnt ;
        let g = Fp12.sparse_mul g (Lines.psi g_line2 a_cache) in
        Fp12.sparse_mul g (Lines.psi tau_line2 b_cache) )
      else g
    in
    Queue.enqueue g_values g ;
    lines_hashes.(idx) <- Accumulator_hash.hash_fp12 g
  done ;
  if circuit_index = 16 then (
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
    Queue.enqueue g_values g ;
    lines_hashes.(ate_len - 1) <- Accumulator_hash.hash_fp12 g ) ;
  kzg.state.lines_hashes_digest <- Accumulator_hash.poseidon_hash lines_hashes ;
  (Kzg_accumulator.hash_packed kzg, kzg, lines_hashes, Queue.to_array g_values)

(** zkp17-22: Miller loop f-accumulation chunks.
    Returns (output_hash, kzg_acc) for chaining. *)
let zkp_f_accum ~circuit_index input_hash : Step.Field.t * Kzg_accumulator.t =
  let ate = Kzg_accumulator.ate_loop_count in
  let ate_len = Array.length ate in
  let from_i, to_i, chunk_size, lhs_size =
    match circuit_index with
    | 17 ->
        (1, 10, 9, 0)
    | 18 ->
        (10, 21, 11, 9)
    | 19 ->
        (21, 32, 11, 20)
    | 20 ->
        (32, 43, 11, 31)
    | 21 ->
        (43, 54, 11, 42)
    | 22 ->
        (54, 65, 11, 53)
    | _ ->
        assert false
  in
  let rhs_size = ate_len - lhs_size - chunk_size in
  let kzg = witness_kzg_accumulator () in
  let g_chunk =
    Step.exists (Step.Typ.array ~length:chunk_size Fp12.typ) ~request:(fun () ->
        Plonk_requests.G_chunk )
  in
  let remaining = ate_len - chunk_size in
  let flat_hashes =
    Step.exists (Step.Typ.array ~length:remaining Step.Field.typ)
      ~request:(fun () -> Plonk_requests.Flat_hashes)
  in
  let lhs_hashes = Array.sub flat_hashes ~pos:0 ~len:lhs_size in
  let rhs_hashes = Array.sub flat_hashes ~pos:lhs_size ~len:rhs_size in
  let in_digest = Kzg_accumulator.hash_packed kzg in
  Step.assert_ (Equal (in_digest, input_hash)) ;
  let opening_hashes = Array.map g_chunk ~f:Accumulator_hash.hash_fp12 in
  let full_arr = Array.concat [ lhs_hashes; opening_hashes; rhs_hashes ] in
  let opening = Accumulator_hash.poseidon_hash full_arr in
  Step.assert_ (Equal (kzg.state.lines_hashes_digest, opening)) ;
  let f = ref kzg.state.f in
  for i = from_i to to_i - 1 do
    let idx = i - from_i in
    f := Fp12.mul (Fp12.square !f) g_chunk.(idx) ;
    if ate.(i) = 1 then f := Fp12.mul !f kzg.proof.c_inv
    else if ate.(i) = -1 then f := Fp12.mul !f kzg.proof.c
  done ;
  kzg.state.f <- !f ;
  (Kzg_accumulator.hash_packed kzg, kzg)

(** zkp23: Final pairing check — Frobenius, shift power, verify f=1. *)
let zkp23 input_hash : Step.Field.t =
  let ate_len = Array.length Kzg_accumulator.ate_loop_count in
  let kzg = witness_kzg_accumulator () in
  let lhs_hashes =
    Step.exists
      (Step.Typ.array ~length:(ate_len - 1) Step.Field.typ)
      ~request:(fun () -> Plonk_requests.Lhs_hashes)
  in
  let g_chunk =
    Step.exists (Step.Typ.array ~length:1 Fp12.typ) ~request:(fun () ->
        Plonk_requests.G_chunk )
  in
  let in_digest = Kzg_accumulator.hash_packed kzg in
  Step.assert_ (Equal (in_digest, input_hash)) ;
  let opening_hashes = Array.map g_chunk ~f:Accumulator_hash.hash_fp12 in
  let full_arr = Array.concat [ lhs_hashes; opening_hashes ] in
  let opening = Accumulator_hash.poseidon_hash full_arr in
  Step.assert_ (Equal (kzg.state.lines_hashes_digest, opening)) ;
  let f = ref (Fp12.mul kzg.state.f g_chunk.(0)) in
  f := Fp12.mul !f (Fp12.frobenius_pow_p kzg.proof.c_inv) ;
  f := Fp12.mul !f (Fp12.frobenius_pow_p_squared kzg.proof.c) ;
  f := Fp12.mul !f (Fp12.frobenius_pow_p_cubed kzg.proof.c_inv) ;
  let w27 = Fp12.of_constant (Bn254_params.w27 ()) in
  let w27_sq = Fp12.of_constant (Bn254_params.w27_sq ()) in
  let field_equals x c =
    let module FF = Snarky_foreign_field.Foreign_field in
    let diff =
      FF.seal Step.Field.(x - constant (Step.Field.Constant.of_int c))
    in
    let b =
      Step.exists Step.Field.typ ~compute:(fun () ->
          let xv = Step.As_prover.read_var x in
          if Step.Field.Constant.(equal xv (of_int c)) then
            Step.Field.Constant.one
          else Step.Field.Constant.zero )
    in
    let z =
      Step.exists Step.Field.typ ~compute:(fun () ->
          let dv = Step.As_prover.read_var diff in
          if Step.Field.Constant.(equal dv zero) then Step.Field.Constant.zero
          else Step.Field.Constant.(one / dv) )
    in
    Step.assert_ (R1CS (b, diff, Step.Field.zero)) ;
    Step.assert_ (R1CS (z, diff, Step.Field.(sub (of_int 1) b))) ;
    b
  in
  let is_0 = field_equals kzg.proof.shift_power 0 in
  let is_1 = field_equals kzg.proof.shift_power 1 in
  let is_2 = field_equals kzg.proof.shift_power 2 in
  let shift =
    Circuit_utils.provable_switch Fp12.typ [| is_0; is_1; is_2 |]
      [| Fp12.one; w27; w27_sq |]
  in
  f := Fp12.mul !f shift ;
  Fp12.assert_one !f ;
  kzg.state.f <- !f ;
  let pi_input : Step.Field.t Random_oracle_input.Chunked.t =
    { field_elements = [||]
    ; packeds =
        (let l = 88 in
         let add_fpa acc (x : FF.FpA.t) =
           let l0, l1, l2 = FF.FpA.to_field3 x in
           (l0, l) :: (l1, l) :: (l2, l) :: acc
         in
         let ps = add_fpa (add_fpa [] kzg.proof.pi1) kzg.proof.pi0 in
         Array.of_list ps )
    }
  in
  let packed_fields = Random_oracle.Checked.pack_input pi_input in
  Random_oracle.Checked.hash packed_fields

(** Dispatch table: circuit index → body function.
    Each function takes input_hash and returns output_hash. *)
let circuit_body (n : int) : Step.Field.t -> Step.Field.t =
  match n with
  | 0 ->
      fun h -> fst (zkp0 h)
  | 1 ->
      fun h -> fst (zkp1 h)
  | 2 ->
      fun h -> fst (zkp2 h)
  | 3 ->
      fun h -> fst (zkp3 h)
  | 4 ->
      fun h -> fst (zkp4 h)
  | 5 ->
      fun h -> fst (zkp5 h)
  | 6 ->
      fun h -> fst (zkp6 h)
  | 7 ->
      fun h -> fst (zkp7 h)
  | 8 ->
      fun h -> fst (zkp8 h)
  | 9 ->
      fun h -> fst (zkp9 h)
  | 10 ->
      fun h -> fst (zkp10 h)
  | 11 ->
      fun h -> fst (zkp11 h)
  | 12 ->
      fun h -> fst (zkp12 h)
  | 13 | 14 | 15 | 16 ->
      fun h ->
        let hash, _kzg, _lh, _gv = zkp_lines ~circuit_index:n h in
        hash
  | 17 | 18 | 19 | 20 | 21 | 22 ->
      fun h -> fst (zkp_f_accum ~circuit_index:n h)
  | 23 ->
      zkp23
  | n ->
      failwith (sprintf "Invalid PLONK circuit index: %d" n)

(* ==== Fast variants for compute-state ==== *)

(** Fast body for circuits 0-11: inject accumulator as constants (no exists),
    run inner mutation, skip both Poseidon hashes.  Returns evolved acc. *)
let plonk_acc_body_fast (inner : Plonk_accumulator.t -> unit)
    (acc_const : Plonk_accumulator.t_const) : Plonk_accumulator.t =
  let acc = Plonk_accumulator.of_constant acc_const in
  inner acc ;
  acc

let zkp0_fast acc = plonk_acc_body_fast (fun acc ->
    Fiat_shamir.squeeze_gamma acc.fs ~proof:acc.proof ~pi0:acc.state.pi0
      ~pi1:acc.state.pi1 ~vk:plonk_vk ;
    Fiat_shamir.squeeze_beta acc.fs) acc

let zkp1_fast acc = plonk_acc_body_fast (fun acc ->
    Fiat_shamir.squeeze_alpha acc.fs ~proof:acc.proof ;
    Fiat_shamir.squeeze_zeta acc.fs ~proof:acc.proof ;
    let zeta_pow_n, zh_eval =
      Piop.eval_vanishing acc.fs.zeta
        ~domain_size_bits:plonk_vk.domain_size_bits
    in
    let inv_domain_size = FF.FpA.of_constant plonk_vk.inv_domain_size in
    let alpha_2_l0 =
      Piop.compute_alpha_square_lagrange_0 ~zh_eval ~zeta:acc.fs.zeta
        ~alpha:acc.fs.alpha ~inv_domain_size
    in
    acc.state.zeta_pow_n <- zeta_pow_n ;
    acc.state.zh_eval <- zh_eval ;
    acc.state.alpha_2_l0 <- alpha_2_l0) acc

let zkp2_fast acc = plonk_acc_body_fast (fun acc ->
    let hx, hy =
      Piop.fold_quotient_split_0 ~h0_x:acc.proof.h0_x ~h0_y:acc.proof.h0_y
        ~h1_x:acc.proof.h1_x ~h1_y:acc.proof.h1_y ~h2_x:acc.proof.h2_x
        ~h2_y:acc.proof.h2_y ~zeta:acc.fs.zeta
        ~zeta_pow_n:acc.state.zeta_pow_n
    in
    acc.state.hx <- hx ;
    acc.state.hy <- hy) acc

let zkp3_fast acc = plonk_acc_body_fast (fun acc ->
    let hx, hy =
      Piop.fold_quotient_split_1 ~hx:acc.state.hx ~hy:acc.state.hy
        ~zh_eval:acc.state.zh_eval
    in
    acc.state.hx <- hx ;
    acc.state.hy <- hy ;
    let inv_domain_size = FF.FpA.of_constant plonk_vk.inv_domain_size in
    let omega = FF.FpA.of_constant plonk_vk.omega in
    let pis =
      Piop.pi_contribution
        ~pub_inputs:[| acc.state.pi0; acc.state.pi1 |]
        ~zeta:acc.fs.zeta ~zh_eval:acc.state.zh_eval
        ~domain_inv:inv_domain_size ~omega
    in
    let omega_pow_i = FF.FpA.of_constant plonk_vk.omega_pow_i in
    let omega_pow_i_div_n = FF.FpA.of_constant plonk_vk.omega_pow_i_div_n in
    let l_pi_commit =
      Piop.custom_pi_lagrange ~zeta:acc.fs.zeta ~zh_eval:acc.state.zh_eval
        ~qcp_wire_x:acc.proof.qcp_0_wire_x ~qcp_wire_y:acc.proof.qcp_0_wire_y
        ~omega_pow_i ~omega_pow_i_div_n
    in
    let pi = Piop.add_fr pis l_pi_commit in
    let linearized_opening =
      Piop.opening_of_linearized_polynomial ~proof:acc.proof
        ~alpha:acc.fs.alpha ~beta:acc.fs.beta ~gamma:acc.fs.gamma ~pi
        ~alpha_2_l0:acc.state.alpha_2_l0
    in
    acc.state.pi <- pi ;
    acc.state.linearized_opening <- linearized_opening) acc

let zkp4_fast acc = plonk_acc_body_fast (fun acc ->
    let lcm_x, lcm_y =
      Piop.compute_commitment_linearized_polynomial_split_0 ~proof:acc.proof
        ~vk:plonk_vk
    in
    acc.state.lcm_x <- lcm_x ;
    acc.state.lcm_y <- lcm_y) acc

let zkp5_fast acc = plonk_acc_body_fast (fun acc ->
    let lcm_x, lcm_y =
      Piop.compute_commitment_linearized_polynomial_split_1
        ~lcm_x:acc.state.lcm_x ~lcm_y:acc.state.lcm_y ~proof:acc.proof
        ~vk:plonk_vk ~beta:acc.fs.beta ~gamma:acc.fs.gamma ~alpha:acc.fs.alpha
    in
    acc.state.lcm_x <- lcm_x ;
    acc.state.lcm_y <- lcm_y) acc

let zkp6_fast acc = plonk_acc_body_fast (fun acc ->
    let lcm_x, lcm_y =
      Piop.compute_commitment_linearized_polynomial_split_2
        ~lcm_x:acc.state.lcm_x ~lcm_y:acc.state.lcm_y ~proof:acc.proof
        ~vk:plonk_vk ~beta:acc.fs.beta ~gamma:acc.fs.gamma ~alpha:acc.fs.alpha
        ~zeta:acc.fs.zeta ~alpha_2_l0:acc.state.alpha_2_l0 ~hx:acc.state.hx
        ~hy:acc.state.hy
    in
    acc.state.lcm_x <- lcm_x ;
    acc.state.lcm_y <- lcm_y) acc

let zkp7_fast acc = plonk_acc_body_fast (fun acc ->
    let h =
      Fiat_shamir.gamma_kzg_digest_part0 acc.fs ~proof:acc.proof ~vk:plonk_vk
        ~linearized_cm_x:acc.state.lcm_x ~linearized_cm_y:acc.state.lcm_y
        ~linearized_opening:acc.state.linearized_opening
    in
    acc.state.h_state <- h) acc

let zkp8_fast acc = plonk_acc_body_fast (fun acc ->
    Fiat_shamir.gamma_kzg_digest_part1 acc.fs ~proof:acc.proof
      ~h_state:acc.state.h_state ;
    Fiat_shamir.squeeze_gamma_kzg_from_digest acc.fs ;
    let cm_x, cm_y, cm_opening =
      Piop.fold_state_0 ~proof:acc.proof ~lcm_x:acc.state.lcm_x
        ~lcm_y:acc.state.lcm_y ~lcm_opening:acc.state.linearized_opening
        ~gamma_kzg:acc.fs.gamma_kzg
    in
    acc.state.cm_x <- cm_x ;
    acc.state.cm_y <- cm_y ;
    acc.state.cm_opening <- cm_opening) acc

let zkp9_fast acc = plonk_acc_body_fast (fun acc ->
    let cm_x, cm_y =
      Piop.fold_state_1 ~proof:acc.proof ~vk:plonk_vk ~cm_x:acc.state.cm_x
        ~cm_y:acc.state.cm_y ~gamma_kzg:acc.fs.gamma_kzg
    in
    acc.state.cm_x <- cm_x ;
    acc.state.cm_y <- cm_y) acc

let zkp10_fast acc = plonk_acc_body_fast (fun acc ->
    let cm_x, cm_y =
      Piop.fold_state_2 ~vk:plonk_vk ~cm_x:acc.state.cm_x ~cm_y:acc.state.cm_y
        ~gamma_kzg:acc.fs.gamma_kzg
    in
    let kzg_random =
      Fiat_shamir.squeeze_random_for_kzg acc.fs ~proof:acc.proof ~cm_x ~cm_y
    in
    acc.state.cm_x <- cm_x ;
    acc.state.cm_y <- cm_y ;
    acc.state.kzg_random <- kzg_random) acc

let zkp11_fast acc = plonk_acc_body_fast (fun acc ->
    let kzg_cm_x, kzg_cm_y, neg_fq_x, neg_fq_y =
      Piop.prepare_pairing_0 ~vk:plonk_vk ~proof:acc.proof
        ~random:acc.state.kzg_random ~cm_x:acc.state.cm_x ~cm_y:acc.state.cm_y
        ~cm_opening:acc.state.cm_opening
    in
    acc.state.kzg_cm_x <- kzg_cm_x ;
    acc.state.kzg_cm_y <- kzg_cm_y ;
    acc.state.neg_fq_x <- neg_fq_x ;
    acc.state.neg_fq_y <- neg_fq_y) acc

(** Fast dispatch table for circuits 0-11. *)
let zkp_fast_fns =
  [| zkp0_fast; zkp1_fast; zkp2_fast; zkp3_fast; zkp4_fast; zkp5_fast
   ; zkp6_fast; zkp7_fast; zkp8_fast; zkp9_fast; zkp10_fast; zkp11_fast |]

(** Fast zkp12: inject acc as constant, skip hashing. *)
let zkp12_fast (acc_const : Plonk_accumulator.t_const)
    ~(shift_power : Step.Field.Constant.t) ~(c_fp12 : Fp12.Constant.t) :
    Kzg_accumulator.t =
  let acc = Plonk_accumulator.of_constant acc_const in
  let shift_power_var = Step.Field.constant shift_power in
  let c = Fp12.of_constant c_fp12 in
  let kzg_cm_x, kzg_cm_y =
    Piop.prepare_pairing_1 ~vk:plonk_vk ~proof:acc.proof
      ~random:acc.state.kzg_random ~folded_cm_x:acc.state.kzg_cm_x
      ~folded_cm_y:acc.state.kzg_cm_y ~zeta:acc.fs.zeta
  in
  let c_inv = Fp12.inverse c in
  { proof =
      { a_x = kzg_cm_x
      ; a_y = kzg_cm_y
      ; neg_b_x = acc.state.neg_fq_x
      ; neg_b_y = acc.state.neg_fq_y
      ; shift_power = shift_power_var
      ; c
      ; c_inv
      ; pi0 = acc.state.pi0
      ; pi1 = acc.state.pi1
      }
  ; state =
      { f = c_inv
      ; lines_hashes_digest = Kzg_accumulator.array_list_hasher_empty
      }
  }

(** Fast zkp_lines: inject KZG acc as constant, skip input/output hashing. *)
let zkp_lines_fast ~circuit_index (kzg_const : Kzg_accumulator.t_const)
    ~(lines_hashes : Step.Field.Constant.t array) :
    Kzg_accumulator.t * Step.Field.t array * Fp12.Circuit.t array =
  let ate = Kzg_accumulator.ate_loop_count in
  let ate_len = Array.length ate in
  let from_, to_ =
    match circuit_index with
    | 13 -> (1, ate_len - 46)
    | 14 -> (ate_len - 46, ate_len - 26)
    | 15 -> (ate_len - 26, ate_len - 6)
    | 16 -> (ate_len - 6, ate_len)
    | _ -> assert false
  in
  let data_dir = "src/lib/proof_conversion/plonk/data" in
  let all_g2 = Plonk_lines.load_lines_from_json (data_dir ^ "/g2_lines.json") in
  let all_tau = Plonk_lines.load_lines_from_json (data_dir ^ "/tau_lines.json") in
  let g2_lines = Plonk_lines.parse_g2 all_g2 ~from:from_ ~to_ in
  let tau_lines = Plonk_lines.parse_tau all_tau ~from:from_ ~to_ in
  let kzg = Kzg_accumulator.of_constant kzg_const in
  let lines_hashes_var =
    Array.map lines_hashes ~f:Step.Field.constant
  in
  let a_cache =
    Lines.AffineCache.make { G1.Circuit.x = kzg.proof.a_x; y = kzg.proof.a_y }
  in
  let b_cache =
    Lines.AffineCache.make
      { G1.Circuit.x = kzg.proof.neg_b_x; y = kzg.proof.neg_b_y }
  in
  let g_values = Queue.create () in
  let line_cnt = ref 0 in
  for i = from_ to to_ - 1 do
    let idx = i - 1 in
    let g_line = Lines.G2Line.of_constant g2_lines.(!line_cnt) in
    let tau_line = Lines.G2Line.of_constant tau_lines.(!line_cnt) in
    incr line_cnt ;
    let g = Lines.psi g_line a_cache in
    let g = Fp12.sparse_mul g (Lines.psi tau_line b_cache) in
    let g =
      if ate.(i) = 1 || ate.(i) = -1 then (
        let g_line2 = Lines.G2Line.of_constant g2_lines.(!line_cnt) in
        let tau_line2 = Lines.G2Line.of_constant tau_lines.(!line_cnt) in
        incr line_cnt ;
        let g = Fp12.sparse_mul g (Lines.psi g_line2 a_cache) in
        Fp12.sparse_mul g (Lines.psi tau_line2 b_cache) )
      else g
    in
    Queue.enqueue g_values g ;
    lines_hashes_var.(idx) <- Accumulator_hash.hash_fp12 g
  done ;
  if circuit_index = 16 then (
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
    Queue.enqueue g_values g ;
    lines_hashes_var.(ate_len - 1) <- Accumulator_hash.hash_fp12 g ) ;
  kzg.state.lines_hashes_digest <-
    Accumulator_hash.poseidon_hash lines_hashes_var ;
  (kzg, lines_hashes_var, Queue.to_array g_values)

(** Fully native zkp_f_accum: no snarky, pure Bignum_bigint arithmetic.
    Returns evolved KZG accumulator constant directly. *)
let zkp_f_accum_native ~circuit_index (kzg_const : Kzg_accumulator.t_const)
    ~(g_chunk_const : Fp12.Constant.t array) : Kzg_accumulator.t_const =
  let ate = Kzg_accumulator.ate_loop_count in
  let from_i, to_i =
    match circuit_index with
    | 17 -> (1, 10)
    | 18 -> (10, 21)
    | 19 -> (21, 32)
    | 20 -> (32, 43)
    | 21 -> (43, 54)
    | 22 -> (54, 65)
    | _ -> assert false
  in
  let f = ref kzg_const.state.f in
  for i = from_i to to_i - 1 do
    let idx = i - from_i in
    f := Fp_const.Fp12.mul (Fp_const.Fp12.square !f) g_chunk_const.(idx) ;
    if ate.(i) = 1 then f := Fp_const.Fp12.mul !f kzg_const.proof.c_inv
    else if ate.(i) = -1 then f := Fp_const.Fp12.mul !f kzg_const.proof.c
  done ;
  { kzg_const with state = { kzg_const.state with f = !f } }
