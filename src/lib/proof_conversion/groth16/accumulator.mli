(** Groth16 proof-conversion accumulator types.

    The accumulator carries state between the 16 recursive circuits that
    together verify a Groth16 proof. Each circuit takes the accumulator
    (via Poseidon hash), processes a chunk of the verification, and
    outputs the updated accumulator. *)

open Proof_conversion_bn254
module Step = Pickles.Impls.Step

(** Constant types re-exported so callers in files where local modules
    shadow G1/G2 can resolve record field labels. *)
module G1_constant = G1.Constant

module G2_constant = G2.Constant

(** [RecursionProof]: the proof data carried through all circuits. *)
module RecursionProof : sig
  module Circuit : sig
    type t =
      { neg_a : G1.Circuit.t
      ; b : G2.Circuit.t
      ; c : G1.Circuit.t
      ; pi : G1.Circuit.t
      ; c_fp12 : Fp12.Circuit.t
      ; c_inv : Fp12.Circuit.t
      ; shift_power : Step.Field.t
      }
  end

  module Constant : sig
    type t =
      { neg_a : G1.Constant.t
      ; b : G2.Constant.t
      ; c : G1.Constant.t
      ; pi : G1.Constant.t
      ; c_fp12 : Fp12.Constant.t
      ; c_inv : Fp12.Constant.t
      ; shift_power : int
      }
  end

  val typ : (Circuit.t, Constant.t) Step.Typ.t
end

(** [State]: the mutable pairing-computation state. *)
module State : sig
  module Circuit : sig
    type t =
      { t_point : G2.Circuit.t; f : Fp12.Circuit.t; g_digest : Step.Field.t }
  end

  module Constant : sig
    type t =
      { t_point : G2.Constant.t
      ; f : Fp12.Constant.t
      ; g_digest : Step.Field.Constant.t
      }
  end

  val typ : (Circuit.t, Constant.t) Step.Typ.t
end

(** The full accumulator = [RecursionProof] + [State]. *)
module Circuit : sig
  type t = { proof : RecursionProof.Circuit.t; state : State.Circuit.t }
end

module Constant : sig
  type t = { proof : RecursionProof.Constant.t; state : State.Constant.t }
end

val typ : (Circuit.t, Constant.t) Step.Typ.t

(** Convert the accumulator to a chunked Random_oracle input. *)
val to_input : Circuit.t -> Step.Field.t Random_oracle_input.Chunked.t

(** Hash the accumulator using Poseidon with packing. *)
val hash : Circuit.t -> Step.Field.t
