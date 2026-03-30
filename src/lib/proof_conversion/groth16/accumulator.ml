(** Groth16 proof conversion accumulator types.

    The accumulator carries state between the 16 recursive circuits
    that together verify a Groth16 proof. Each circuit takes the
    accumulator as input (via Poseidon hash), processes a chunk of
    the verification, and outputs the updated accumulator.

    Reference: nori-proof-conversion/src/groth/recursion/prove_zkps.ts *)

(** The Groth16 proof structure (negated A, B, C, PI points). *)
module Proof = struct
  module Circuit = struct
    type t =
      { neg_a : G1.Circuit.t
      ; b : Fp2.Circuit.t * Fp2.Circuit.t  (* G2 point as Fp2 pair *)
      ; c : G1.Circuit.t
      ; pi : G1.Circuit.t
      }
  end
end

(** Auxiliary witness from the pairing computation.
    c and c_inv are Fp12 elements, shift_power is 0, 1, or 2. *)
module AuxWitness = struct
  module Circuit = struct
    type t =
      { c : Fp12.Circuit.t
      ; c_inv : Fp12.Circuit.t
      ; shift_power : Pickles.Impls.Step.Field.t
      }
  end
end

(** The full accumulator state passed between circuits. *)
module Circuit = struct
  type t =
    { proof : Proof.Circuit.t
    ; aux : AuxWitness.Circuit.t
    ; f : Fp12.Circuit.t          (** Miller loop intermediate result *)
    ; g_digest : Pickles.Impls.Step.Field.t
        (** Poseidon hash of line evaluation Fp12 values *)
    }
end

(** Hash an accumulator into a single field element using Poseidon.
    This is the public input/output for each circuit in the chain. *)
let _hash (_acc : Circuit.t) : Pickles.Impls.Step.Field.t =
  (* TODO: implement Poseidon hashing of accumulator fields *)
  failwith "Accumulator.hash: not yet implemented"
