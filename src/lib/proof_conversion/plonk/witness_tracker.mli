(** Out-of-circuit computation for PLONK proof-conversion witnesses.

    Computes values needed by the prover (e.g. Poseidon hashes of
    accumulator state) without circuit constraints. *)

open Proof_conversion_bn254
module Step = Pickles.Impls.Step

(** Convert a circuit-level chunked input to constants (all Cvars must
    be constant). *)
val chunked_input_to_const :
     Step.Field.t Random_oracle_input.Chunked.t
  -> Step.Field.Constant.t Random_oracle_input.Chunked.t

(** Poseidon hash of a PLONK accumulator constant. *)
val hash_accumulator_const : Accumulator.t_const -> Step.Field.Constant.t

(** Poseidon hash of a KZG accumulator constant. *)
val hash_kzg_accumulator_const :
  Kzg_accumulator.t_const -> Step.Field.Constant.t

(** Extract the KZG A/B points from the accumulator state after
    circuit 11; returns [(a_x, a_y, neg_b_x, neg_b_y)]. *)
val extract_kzg_points_from_state11 :
     Accumulator.t_const
  -> Bignum_bigint.t * Bignum_bigint.t * Bignum_bigint.t * Bignum_bigint.t

(** Compute the KZG Miller-loop output from pre-extracted A/B points. *)
val compute_mlo_from_points :
     a_x:Bignum_bigint.t
  -> a_y:Bignum_bigint.t
  -> neg_b_x:Bignum_bigint.t
  -> neg_b_y:Bignum_bigint.t
  -> Fp12.Constant.t

(** Run circuit [n] unchecked with a witness handler; returns the
    output hash. *)
val run_circuit_unchecked :
     n:int
  -> input_hash:Step.Field.Constant.t
  -> witness:Requests.witness
  -> Step.Field.Constant.t

(** Run circuits 0-11 unchecked, then compute the KZG Miller-loop
    output via the Rust FFI. *)
val compute_kzg_mlo : Accumulator.t_const -> Fp12.Constant.t
