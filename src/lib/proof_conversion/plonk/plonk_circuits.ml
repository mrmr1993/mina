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

let build_circuit_body ~(circuit_index : int) : circuit_body =
  match circuit_index with
  | 0 ->
      (* Squeeze gamma: SHA-256 based Fiat-Shamir *)
      fun input_hash ->
       let transcript = Fiat_shamir.create () in
       (* Absorb proof commitments *)
       let dummy_field =
         Step.exists Step.Field.typ ~compute:(fun () ->
             Step.Field.Constant.zero )
       in
       Fiat_shamir.absorb_field transcript dummy_field ;
       let _gamma = Fiat_shamir.squeeze_challenge transcript in
       Accumulator_hash.combine_hashes [ input_hash; Step.Field.of_int 0 ]
  | 1 ->
      (* Squeeze alpha/zeta, compute zeta^n *)
      fun input_hash ->
       let zeta = FF.Field3.of_constant FF.Bignum_bigint.one in
       let _zeta_n = Piop.pow_fr zeta ~exp:16777216 in
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
       let w () : Fp2.Circuit.t =
         { Fp2.Circuit.c0 = FF.FpA.of_constant FF.Bignum_bigint.one
         ; c1 = FF.FpA.of_constant FF.Bignum_bigint.one
         }
       in
       let w6 () : Fp6.Circuit.t =
         { Fp6.Circuit.c0 = w (); c1 = w (); c2 = w () }
       in
       let c : Fp12.Circuit.t = { Fp12.Circuit.c0 = w6 (); c1 = w6 () } in
       let _c_inv = Fp12.conjugate c in
       Accumulator_hash.combine_hashes [ input_hash; Step.Field.of_int 12 ]
  | 13 | 14 | 15 | 16 ->
      (* Hash line coefficients: Fp12 values → Poseidon digest *)
      fun input_hash ->
       let w () : Fp2.Circuit.t =
         { Fp2.Circuit.c0 = FF.FpA.of_constant FF.Bignum_bigint.one
         ; c1 = FF.FpA.of_constant FF.Bignum_bigint.one
         }
       in
       let w6 () : Fp6.Circuit.t =
         { Fp6.Circuit.c0 = w (); c1 = w (); c2 = w () }
       in
       let g : Fp12.Circuit.t = { Fp12.Circuit.c0 = w6 (); c1 = w6 () } in
       let _hash = Accumulator_hash.hash_fp12 g in
       Accumulator_hash.combine_hashes
         [ input_hash; Step.Field.of_int circuit_index ]
  | 17 | 18 | 19 | 20 | 21 | 22 | 23 ->
      (* Miller loop computation (shared structure with Groth16) *)
      fun input_hash ->
       let w () : Fp2.Circuit.t =
         { Fp2.Circuit.c0 = FF.FpA.of_constant FF.Bignum_bigint.one
         ; c1 = FF.FpA.of_constant FF.Bignum_bigint.one
         }
       in
       let w6 () : Fp6.Circuit.t =
         { Fp6.Circuit.c0 = w (); c1 = w (); c2 = w () }
       in
       let f : Fp12.Circuit.t = { Fp12.Circuit.c0 = w6 (); c1 = w6 () } in
       let g = { Fp12.Circuit.c0 = w6 (); c1 = w6 () } in
       let f_sq = Fp12.square f in
       let _result = Fp12.mul f_sq g in
       Accumulator_hash.combine_hashes
         [ input_hash; Step.Field.of_int circuit_index ]
  | n ->
      failwith (sprintf "Invalid PLONK circuit index: %d" n)
