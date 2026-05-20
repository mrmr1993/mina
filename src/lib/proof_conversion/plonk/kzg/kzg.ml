(** KZG (Kate-Zaverucha-Goldberg) commitment verification.

    Verifies polynomial opening proofs using the BN254 pairing.
    The KZG check reduces to a pairing equation:
      e(C - v*G, xi) = e(pi, tau - z*xi)
    where C is the commitment, v is the evaluation, pi is the proof,
    and tau is the trusted setup point.

    In the recursive circuit, the pairing is accumulated rather than
    verified directly — the pairing arguments are passed to the
    Miller loop circuits (shared with Groth16).

    Reference: nori-proof-conversion/src/kzg/ *)

open! Core_kernel
open Proof_conversion_bn254
module FF = Snarky_foreign_field.Foreign_field

(** KZG proof accumulator state. *)
module Accumulator = struct
  type t =
    { a : G1.Circuit.t  (** Commitment point *)
    ; neg_b : G1.Circuit.t  (** Negative opening proof point *)
    ; shift_power : Pickles.Impls.Step.Field.t
    ; c : Fp12.Circuit.t  (** Pairing auxiliary witness *)
    ; c_inv : Fp12.Circuit.t  (** Inverse of c *)
    }
end

(** KZG state carried through the Miller loop. *)
module State = struct
  type t =
    { f : Fp12.Circuit.t  (** Miller loop accumulator *)
    ; lines_digest : Pickles.Impls.Step.Field.t
          (** Poseidon hash of line evaluation Fp12 values *)
    }
end

(** Batch KZG opening: combine multiple opening proofs into a single
    pairing check using random linear combination. *)
let batch_opening ~(commitments : G1.Circuit.t array)
    ~(evaluations : FF.Field3.t array) ~(random : FF.Field3.t) :
    G1.Circuit.t * FF.Field3.t =
  assert (Array.length commitments = Array.length evaluations) ;
  (* C_batch = sum_i (r^i * C_i) *)
  (* v_batch = sum_i (r^i * v_i) *)
  let p = Bn254_params.p in
  let c_x = ref (FF.Field3.of_constant FF.Bignum_bigint.zero) in
  let c_y = ref (FF.Field3.of_constant FF.Bignum_bigint.zero) in
  let v = ref (FF.Field3.of_constant FF.Bignum_bigint.zero) in
  let r_pow = ref (FF.Field3.of_constant FF.Bignum_bigint.one) in
  for i = 0 to Array.length commitments - 1 do
    let ci = commitments.(i) in
    let vi = evaluations.(i) in
    c_x := FF.add !c_x (FF.mul !r_pow (FF.FpA.to_field3 ci.x) ~f:p) ~f:p ;
    c_y := FF.add !c_y (FF.mul !r_pow (FF.FpA.to_field3 ci.y) ~f:p) ~f:p ;
    v := FF.add !v (FF.mul !r_pow vi ~f:Bn254_params.r) ~f:Bn254_params.r ;
    r_pow := FF.mul !r_pow random ~f:Bn254_params.r
  done ;
  ( { G1.Circuit.x = FF.FpA.of_field3_unsafe !c_x
    ; y = FF.FpA.of_field3_unsafe !c_y
    }
  , !v )
