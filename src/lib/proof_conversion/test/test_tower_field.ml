(** Test out-of-circuit tower field arithmetic correctness. *)

open Core_kernel
module WT = Proof_conversion.Witness_tracker

let test_fp_arithmetic () =
  printf "Testing Fp arithmetic... %!" ;
  let a = Bignum_bigint.of_int 42 in
  let b = Bignum_bigint.of_int 17 in
  assert (Bignum_bigint.(WT.Fp.add a b = of_int 59)) ;
  assert (Bignum_bigint.(WT.Fp.sub a b = of_int 25)) ;
  assert (Bignum_bigint.(WT.Fp.mul a b = of_int 714)) ;
  let a_inv = WT.Fp.inv a in
  assert (Bignum_bigint.(WT.Fp.mul a a_inv = one)) ;
  printf "OK\n"

let test_fp2_mul () =
  printf "Testing Fp2 multiplication... %!" ;
  let a : WT.Fp2.t = (Bignum_bigint.of_int 7, Bignum_bigint.of_int 3) in
  let b : WT.Fp2.t = (Bignum_bigint.of_int 5, Bignum_bigint.of_int 11) in
  let c0, c1 = WT.Fp2.mul a b in
  (* (7+3i)(5+11i) = (35-33) + (77+15)i = 2 + 92i *)
  assert (Bignum_bigint.(c0 = of_int 2)) ;
  assert (Bignum_bigint.(c1 = of_int 92)) ;
  printf "OK\n"

let test_fp2_conjugate () =
  printf "Testing Fp2 conjugate... %!" ;
  let a : WT.Fp2.t = (Bignum_bigint.of_int 5, Bignum_bigint.of_int 3) in
  let c0, c1 = WT.Fp2.conjugate a in
  assert (Bignum_bigint.(c0 = of_int 5)) ;
  assert (Bignum_bigint.(c1 = WT.Fp.neg (of_int 3))) ;
  printf "OK\n"

let test_fp2_inverse () =
  printf "Testing Fp2 inverse... %!" ;
  let a : WT.Fp2.t = (Bignum_bigint.of_int 7, Bignum_bigint.of_int 11) in
  let a_inv = WT.Fp2.inverse a in
  let c0, c1 = WT.Fp2.mul a a_inv in
  assert (Bignum_bigint.(c0 = one)) ;
  assert (Bignum_bigint.(c1 = zero)) ;
  printf "OK\n"

let test_fp12_identity () =
  printf "Testing Fp12 squaring (1^2=1)... %!" ;
  let sq = WT.Fp12.square WT.Fp12.one in
  let (c00, _, _), (c10, _, _) = sq in
  assert (Bignum_bigint.(fst c00 = one)) ;
  assert (Bignum_bigint.(snd c00 = zero)) ;
  assert (Bignum_bigint.(fst c10 = zero)) ;
  printf "OK\n"

let test_fp2_square () =
  printf "Testing Fp2 squaring... %!" ;
  let a : WT.Fp2.t = (Bignum_bigint.of_int 3, Bignum_bigint.of_int 4) in
  let c0, c1 = WT.Fp2.square a in
  (* (3+4i)^2 = 9-16 + 24i = -7 + 24i *)
  let expected_c0 =
    WT.Fp.sub (Bignum_bigint.of_int 9) (Bignum_bigint.of_int 16)
  in
  assert (Bignum_bigint.(c0 = expected_c0)) ;
  assert (Bignum_bigint.(c1 = of_int 24)) ;
  printf "OK\n"

let test_fp6_mul_identity () =
  printf "Testing Fp6 multiplication (a*1=a)... %!" ;
  let a : WT.Fp6.t =
    ( (Bignum_bigint.of_int 5, Bignum_bigint.of_int 7)
    , (Bignum_bigint.of_int 11, Bignum_bigint.of_int 13)
    , (Bignum_bigint.of_int 17, Bignum_bigint.of_int 19) )
  in
  let result = WT.Fp6.mul a WT.Fp6.one in
  let (r00, r01), (r10, r11), (r20, r21) = result in
  assert (Bignum_bigint.(r00 = of_int 5)) ;
  assert (Bignum_bigint.(r01 = of_int 7)) ;
  assert (Bignum_bigint.(r10 = of_int 11)) ;
  assert (Bignum_bigint.(r11 = of_int 13)) ;
  assert (Bignum_bigint.(r20 = of_int 17)) ;
  assert (Bignum_bigint.(r21 = of_int 19)) ;
  printf "OK\n"

let test_fp12_mul_identity () =
  printf "Testing Fp12 multiplication (a*1=a)... %!" ;
  let a_c0 : WT.Fp6.t =
    ( (Bignum_bigint.of_int 2, Bignum_bigint.of_int 3)
    , (Bignum_bigint.of_int 5, Bignum_bigint.of_int 7)
    , (Bignum_bigint.of_int 11, Bignum_bigint.of_int 13) )
  in
  let a_c1 : WT.Fp6.t =
    ( (Bignum_bigint.of_int 17, Bignum_bigint.of_int 19)
    , (Bignum_bigint.of_int 23, Bignum_bigint.of_int 29)
    , (Bignum_bigint.of_int 31, Bignum_bigint.of_int 37) )
  in
  let a : WT.Fp12.t = (a_c0, a_c1) in
  let result = WT.Fp12.mul a WT.Fp12.one in
  let (r00, _, _), _ = result in
  assert (Bignum_bigint.(fst r00 = of_int 2)) ;
  assert (Bignum_bigint.(snd r00 = of_int 3)) ;
  printf "OK\n"

let test_fp12_conjugate_property () =
  printf "Testing Fp12 conjugate (a * conj(a) is real)... %!" ;
  let a_c0 : WT.Fp6.t =
    ((Bignum_bigint.of_int 2, Bignum_bigint.of_int 3), WT.Fp2.zero, WT.Fp2.zero)
  in
  let a_c1 : WT.Fp6.t =
    ((Bignum_bigint.of_int 5, Bignum_bigint.of_int 7), WT.Fp2.zero, WT.Fp2.zero)
  in
  let a : WT.Fp12.t = (a_c0, a_c1) in
  let conj = WT.Fp12.conjugate a in
  let product = WT.Fp12.mul a conj in
  (* a * conj(a) should have c1 = 0 (it's a "real" Fp6) *)
  let _, (c10, c11, c12) = product in
  assert (Bignum_bigint.(fst c10 = zero && snd c10 = zero)) ;
  assert (Bignum_bigint.(fst c11 = zero && snd c11 = zero)) ;
  assert (Bignum_bigint.(fst c12 = zero && snd c12 = zero)) ;
  printf "OK\n"

let test_miller_loop () =
  printf "Testing Miller loop computation... %!" ;
  let proof_path =
    match Stdlib.Sys.getenv_opt "PROOF_JSON" with Some p -> p | None -> ""
  in
  if String.is_empty proof_path then printf "SKIPPED (set PROOF_JSON=path)\n"
  else
    let vk_path = Filename.dirname proof_path ^ "/vk.json" in
    let proof = Proof_conversion.Proof_json.load_proof proof_path in
    let vk = Proof_conversion.Proof_json.load_vk vk_path in
    let aux_path = Filename.dirname proof_path ^ "/aux_witness.json" in
    let aux = Proof_conversion.Proof_json.load_aux_witness aux_path in
    let tracker = WT.create ~proof ~vk ~aux in
    (* Check that g_values were computed *)
    let g_vals = WT.get_g_values tracker in
    assert (Array.length g_vals > 0) ;
    (* Check f is not identity (it should have changed from 1) *)
    let f = WT.get_f tracker in
    let (f00, _, _), _ = f in
    let f00_is_one = Bignum_bigint.(fst f00 = one && snd f00 = zero) in
    assert (not f00_is_one) ;
    (* The first g value should not be identity either *)
    let g0 = WT.get_f_at_iteration tracker 0 in
    let (g00, _, _), _ = g0 in
    let g00_is_one = Bignum_bigint.(fst g00 = one && snd g00 = zero) in
    assert (not g00_is_one) ;
    printf "OK\n"

let test_witness_tracker_creation () =
  printf "Testing witness tracker with real proof data... %!" ;
  let proof_path =
    match Stdlib.Sys.getenv_opt "PROOF_JSON" with Some p -> p | None -> ""
  in
  if String.is_empty proof_path then printf "SKIPPED (set PROOF_JSON=path)\n"
  else
    let vk_path = Filename.dirname proof_path ^ "/vk.json" in
    let proof = Proof_conversion.Proof_json.load_proof proof_path in
    let vk = Proof_conversion.Proof_json.load_vk vk_path in
    let aux_path = Filename.dirname proof_path ^ "/aux_witness.json" in
    let aux = Proof_conversion.Proof_json.load_aux_witness aux_path in
    let tracker = WT.create ~proof ~vk ~aux in
    printf "IC=%d PI=%d... " (WT.num_ic tracker) (WT.num_public_inputs tracker) ;
    let neg_a = WT.get_neg_a tracker in
    assert (Bignum_bigint.(neg_a.x > zero)) ;
    printf "OK\n"

let () =
  printf "Tower field arithmetic tests\n" ;
  printf "============================\n" ;
  test_fp_arithmetic () ;
  test_fp2_mul () ;
  test_fp2_square () ;
  test_fp2_conjugate () ;
  test_fp2_inverse () ;
  test_fp6_mul_identity () ;
  test_fp12_identity () ;
  test_fp12_mul_identity () ;
  test_fp12_conjugate_property () ;
  test_miller_loop () ;
  test_witness_tracker_creation () ;
  printf "All tests passed.\n"
