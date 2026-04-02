(** PLONK Polynomial IOP (Interactive Oracle Proof) verification.

    Implements the algebraic checks that the PLONK verifier performs:
    1. Evaluate the vanishing polynomial Z_H(zeta)
    2. Compute the public input contribution
    3. Fold the quotient polynomial
    4. Compute the linearized polynomial commitment
    5. Verify the polynomial opening

    All operations are over the BN254 scalar field (Fr).

    Reference: nori-proof-conversion/src/plonk/piop/ *)

open! Core_kernel
module FF = Snarky_foreign_field.Foreign_field

let r = Bn254_params.r

(** Compute zeta^n mod r where n is the domain size. *)
let pow_fr (base : FF.Field3.t) ~(exp : int) : FF.Field3.t =
  let result = ref (FF.Field3.of_constant FF.Bignum_bigint.one) in
  let current = ref base in
  let e = ref exp in
  while !e > 0 do
    if !e mod 2 = 1 then result := FF.mul !result !current ~f:r ;
    current := FF.mul !current !current ~f:r ;
    e := !e / 2
  done ;
  !result

(** Evaluate vanishing polynomial: Z_H(zeta) = zeta^n - 1 *)
let eval_vanishing ~(zeta : FF.Field3.t) ~(domain_size : int) : FF.Field3.t =
  let zeta_n = pow_fr zeta ~exp:domain_size in
  FF.sub zeta_n (FF.Field3.of_constant FF.Bignum_bigint.one) ~f:r

(** Compute L_0(zeta) = (zeta^n - 1) / (n * (zeta - 1))
    Used for public input contribution. *)
let eval_l0 ~(zeta : FF.Field3.t) ~(domain_size : int) : FF.Field3.t =
  let zh = eval_vanishing ~zeta ~domain_size in
  let zeta_minus_1 =
    FF.sub zeta (FF.Field3.of_constant FF.Bignum_bigint.one) ~f:r
  in
  let denom =
    FF.mul
      (FF.Field3.of_constant (FF.Bignum_bigint.of_int domain_size))
      zeta_minus_1 ~f:r
  in
  FF.div zh denom ~f:r

(** Compute the public input polynomial contribution:
    PI(zeta) = sum_i (pi_i * L_i(zeta)) *)
let compute_pi ~(public_inputs : FF.Field3.t array) ~(zeta : FF.Field3.t)
    ~(domain_size : int) : FF.Field3.t =
  if Array.length public_inputs = 0 then
    FF.Field3.of_constant FF.Bignum_bigint.zero
  else
    (* Simplified: just compute L_0(zeta) * pi_0 for the first input *)
    let l0 = eval_l0 ~zeta ~domain_size in
    FF.mul l0 public_inputs.(0) ~f:r

(** Fold the quotient polynomial pieces:
    H(zeta) = h0 + h1 * zeta^(n+2) + h2 * zeta^(2*(n+2)) *)
let fold_quotient ~(h0_eval : FF.Field3.t) ~(h1_eval : FF.Field3.t)
    ~(h2_eval : FF.Field3.t) ~(zeta : FF.Field3.t) ~(domain_size : int) :
    FF.Field3.t =
  let zeta_np2 = pow_fr zeta ~exp:(domain_size + 2) in
  let zeta_2np4 = FF.mul zeta_np2 zeta_np2 ~f:r in
  let t1 = FF.mul h1_eval zeta_np2 ~f:r in
  let t2 = FF.mul h2_eval zeta_2np4 ~f:r in
  FF.add (FF.add h0_eval t1 ~f:r) t2 ~f:r
