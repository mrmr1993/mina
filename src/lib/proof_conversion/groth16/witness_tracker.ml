(** Groth16 witness tracker — out-of-circuit computation.

    Pre-computes all intermediate values needed by the 16 recursive
    circuits. Operates on pure bignum arithmetic (no circuit constraints).

    This mirrors nori-proof-conversion/src/groth/witness_tracker.ts *)

open Bignum_bigint

let p = Bn254.Bn254_params.p

(** Out-of-circuit Fp arithmetic. *)
module Fp = struct
  let add a b = (a + b) % p

  let sub a b = ((a - b) % p + p) % p

  let mul a b = a * b % p

  let inv a =
    match
      Snarky_foreign_field.Foreign_field.bignum_mod_inverse a ~f:p
    with
    | Some v ->
        v
    | None ->
        failwith "Fp.inv: inverse does not exist"

  let neg a = sub zero a
end

(** Out-of-circuit Fp2 arithmetic. *)
module Fp2 = struct
  type t = Bignum_bigint.t * Bignum_bigint.t

  let add (a0, a1) (b0, b1) : t = (Fp.add a0 b0, Fp.add a1 b1)

  let sub (a0, a1) (b0, b1) : t = (Fp.sub a0 b0, Fp.sub a1 b1)

  let mul (a0, a1) (b0, b1) : t =
    let v0 = Fp.mul a0 b0 in
    let v1 = Fp.mul a1 b1 in
    (Fp.sub v0 v1, Fp.sub (Fp.mul (Fp.add a0 a1) (Fp.add b0 b1)) (Fp.add v0 v1))

  let neg (a0, a1) : t = (Fp.neg a0, Fp.neg a1)

  let conjugate (a0, a1) : t = (a0, Fp.neg a1)

  let square (a0, a1) : t =
    let ab = Fp.mul a0 a1 in
    (Fp.sub (Fp.mul (Fp.add a0 a1) (Fp.sub a0 a1)) zero, Fp.add ab ab)

  let inverse (a0, a1) : t =
    let norm = Fp.add (Fp.mul a0 a0) (Fp.mul a1 a1) in
    let norm_inv = Fp.inv norm in
    (Fp.mul a0 norm_inv, Fp.neg (Fp.mul a1 norm_inv))

  let zero : t = (Bignum_bigint.zero, Bignum_bigint.zero)

  let one : t = (Bignum_bigint.one, Bignum_bigint.zero)

  let mul_by_fp (a0, a1) s : t = (Fp.mul a0 s, Fp.mul a1 s)
end

(** Out-of-circuit Fp6 arithmetic. *)
module Fp6 = struct
  type t = Fp2.t * Fp2.t * Fp2.t

  let xi : Fp2.t = Bn254.Bn254_params.fp2_non_residue

  let mul_by_nr x = Fp2.mul x xi

  let add (a0, a1, a2) (b0, b1, b2) : t =
    (Fp2.add a0 b0, Fp2.add a1 b1, Fp2.add a2 b2)

  let sub (a0, a1, a2) (b0, b1, b2) : t =
    (Fp2.sub a0 b0, Fp2.sub a1 b1, Fp2.sub a2 b2)

  let neg (a0, a1, a2) : t = (Fp2.neg a0, Fp2.neg a1, Fp2.neg a2)

  let mul (a0, a1, a2) (b0, b1, b2) : t =
    let a0b0 = Fp2.mul a0 b0 in
    let a0b1 = Fp2.mul a0 b1 in
    let a0b2 = Fp2.mul a0 b2 in
    let a1b0 = Fp2.mul a1 b0 in
    let a1b1 = Fp2.mul a1 b1 in
    let a1b2 = Fp2.mul a1 b2 in
    let a2b0 = Fp2.mul a2 b0 in
    let a2b1 = Fp2.mul a2 b1 in
    let a2b2 = Fp2.mul a2 b2 in
    ( Fp2.add a0b0 (mul_by_nr (Fp2.add a1b2 a2b1))
    , Fp2.add (Fp2.add a0b1 a1b0) (mul_by_nr a2b2)
    , Fp2.add (Fp2.add a0b2 a1b1) a2b0 )

  let zero : t = (Fp2.zero, Fp2.zero, Fp2.zero)
end

(** Out-of-circuit Fp12 arithmetic. *)
module Fp12 = struct
  type t = Fp6.t * Fp6.t

  let mul (a0, a1) (b0, b1) : t =
    let v0 = Fp6.mul a0 b0 in
    let v1 = Fp6.mul a1 b1 in
    let v1_shifted =
      let c0, c1, c2 = v1 in
      (Fp6.mul_by_nr c2, c0, c1)
    in
    let c0 = Fp6.add v0 v1_shifted in
    let a01 = Fp6.add a0 a1 in
    let b01 = Fp6.add b0 b1 in
    let t = Fp6.mul a01 b01 in
    let c1 = Fp6.sub (Fp6.sub t v0) v1 in
    (c0, c1)

  let square a = mul a a

  let conjugate (a0, a1) : t = (a0, Fp6.neg a1)

  let one : t = ((Fp2.one, Fp2.zero, Fp2.zero), Fp6.zero)

  let inverse (a0, a1) : t =
    (* For elements on the cyclotomic subgroup, inv = conjugate.
       For general elements, use the formula:
       inv(a0 + a1*w) = (a0 - a1*w) / (a0^2 - a1^2*v) *)
    ignore (a0, a1) ;
    failwith "Fp12.inverse: not yet implemented for general elements"
end

(** The witness tracker state. *)
type t =
  { proof : Proof_json.proof
  ; vk : Proof_json.vk
  ; mutable f : Fp12.t
  ; mutable g_values : Fp12.t array
  }

(** Create a witness tracker from parsed proof and VK. *)
let create ~(proof : Proof_json.proof) ~(vk : Proof_json.vk) : t =
  { proof; vk; f = Fp12.one; g_values = [||] }

(** Compute witness values for a specific circuit (zkpN).
    Returns bignum values that will be provided to the circuit
    via the Snarky request handler. *)
let compute_zkp_witness (_tracker : t) ~(circuit_index : int) :
    unit =
  (* TODO: implement per-circuit witness computation *)
  ignore circuit_index ;
  failwith "witness_tracker: not yet implemented"
