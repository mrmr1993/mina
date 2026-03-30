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

let () =
  printf "Tower field arithmetic tests\n" ;
  printf "============================\n" ;
  test_fp_arithmetic () ;
  test_fp2_mul () ;
  test_fp2_conjugate () ;
  test_fp2_inverse () ;
  test_fp12_identity () ;
  printf "All tests passed.\n"
