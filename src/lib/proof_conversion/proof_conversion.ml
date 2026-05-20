(** Top-level proof conversion library.

    Converts non-native ZK proofs (Groth16, PLONK) into Mina-compatible
    proofs via recursive proof compression using Pickles.

    The library is split into focused sub-libraries, each re-exported here
    as a namespace. Multi-module sub-libraries are exposed as their own
    namespace ([Bn254], [Circuit_kit], [Groth16], [Plonk]); single-module
    sub-libraries are exposed directly ([Tree_compressor], [Workdir],
    [Pairing_utils_bridge]). *)

(** BN254 curve primitives: tower fields, curve points, pairing lines. *)
module Bn254 = Proof_conversion_bn254

(** Shared circuit-kit helpers ([Circuit_utils], [Cache_config]). *)
module Circuit_kit = Proof_conversion_circuit_kit

(** Groth16 (Risc0/SP1) proof-conversion circuits, witness tracker, and the
    end-to-end [Convert] pipeline. *)
module Groth16 = Proof_conversion_groth16

(** PLONK (SP1) proof-conversion circuits, transcript, and KZG. *)
module Plonk = Proof_conversion_plonk

(** Binary-tree proof-compression circuits. *)
module Tree_compressor = Proof_conversion_compressor.Tree_compressor

(** Staged working-directory orchestration. *)
module Workdir = Proof_conversion_workdir.Workdir

(** OCaml wrapper around the Rust pairing-utils FFI. *)
module Pairing_utils_bridge =
  Proof_conversion_pairing_utils_bridge.Pairing_utils_bridge
