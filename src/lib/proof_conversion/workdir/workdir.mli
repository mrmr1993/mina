(** Working-directory management for staged proof conversion.

    Each stage reads/writes intermediate state to a working directory,
    enabling independent process execution and future parallelism. *)

open Proof_conversion_plonk
open Proof_conversion_groth16
open Proof_conversion_bn254
module Step = Pickles.Impls.Step

(** Recursive [mkdir]. *)
val mkdir_p : string -> unit

(** Proof system of a working directory. *)
type system = Plonk of { base_count : int } | Groth16 of { base_count : int }

val state_dir : string -> string

val proofs_dir : string -> int -> string

val vks_dir : string -> int -> string

val meta_path : string -> string

val hash_path : string -> int -> string

val acc_path : string -> int -> string

val proof_path : string -> layer:int -> index:int -> string

val vk_path : string -> layer:int -> index:int -> string

val node_vk_path : string -> string

val bi_to_json : Bignum_bigint.t -> Yojson.Safe.t

val bi_of_json : Yojson.Safe.t -> Bignum_bigint.t

val fp2_to_json : Fp2.Constant.t -> Yojson.Safe.t

val fp2_of_json : Yojson.Safe.t -> Fp2.Constant.t

val fp6_to_json : Fp6.Constant.t -> Yojson.Safe.t

val fp6_of_json : Yojson.Safe.t -> Fp6.Constant.t

val fp12_to_json : Fp12.Constant.t -> Yojson.Safe.t

val fp12_of_json : Yojson.Safe.t -> Fp12.Constant.t

val g1_to_json : G1.Constant.t -> Yojson.Safe.t

val g1_of_json : Yojson.Safe.t -> G1.Constant.t

val g2_to_json : G2.Constant.t -> Yojson.Safe.t

val g2_of_json : Yojson.Safe.t -> G2.Constant.t

val field_to_json : Step.Field.Constant.t -> Yojson.Safe.t

val field_of_json : Yojson.Safe.t -> Step.Field.Constant.t

(** Groth16 accumulator JSON serialization. *)
module Groth16_ser : sig
  val proof_to_json : Accumulator.RecursionProof.Constant.t -> Yojson.Safe.t

  val proof_of_json : Yojson.Safe.t -> Accumulator.RecursionProof.Constant.t

  val state_to_json : Accumulator.State.Constant.t -> Yojson.Safe.t

  val state_of_json : Yojson.Safe.t -> Accumulator.State.Constant.t

  val acc_to_json : Accumulator.Constant.t -> Yojson.Safe.t

  val acc_of_json : Yojson.Safe.t -> Accumulator.Constant.t

  val full_state_to_json :
       acc:Accumulator.Constant.t
    -> line_hashes:Step.Field.Constant.t array
    -> g_values:Fp12.Constant.t array
    -> Yojson.Safe.t

  val full_state_of_json :
       Yojson.Safe.t
    -> Accumulator.Constant.t
       * Step.Field.Constant.t array
       * Fp12.Constant.t array
end

(** Write Groth16 accumulator state as JSON. *)
val write_groth16_state :
     workdir:string
  -> n:int
  -> acc:Accumulator.Constant.t
  -> line_hashes:Step.Field.Constant.t array
  -> g_values:Fp12.Constant.t array
  -> unit

(** Read Groth16 accumulator state from JSON. *)
val read_groth16_state :
     workdir:string
  -> n:int
  -> Accumulator.Constant.t
     * Step.Field.Constant.t array
     * Fp12.Constant.t array

(** Write PLONK accumulator state. *)
val write_plonk_state :
     workdir:string
  -> n:int
  -> acc:Proof_conversion_plonk.Accumulator.t_const
  -> unit

(** Read PLONK accumulator state. *)
val read_plonk_state :
  workdir:string -> n:int -> Proof_conversion_plonk.Accumulator.t_const

(** Write PLONK KZG accumulator state (circuits 12+). *)
val write_plonk_kzg_state :
     workdir:string
  -> n:int
  -> kzg:Kzg_accumulator.t_const
  -> lines_hashes:Step.Field.Constant.t array
  -> g_values:Fp12.Constant.t array
  -> unit

(** Read PLONK KZG accumulator state. *)
val read_plonk_kzg_state :
     workdir:string
  -> n:int
  -> Kzg_accumulator.t_const
     * Step.Field.Constant.t array
     * Fp12.Constant.t array

(** Highest tree layer for a system. *)
val max_layer : system -> int

(** Base-circuit count for a system. *)
val base_count : system -> int

(** Initialize a working directory for staged execution. *)
val init : workdir:string -> system:system -> unit

(** Detect the proof system from workdir metadata. *)
val detect_system : workdir:string -> system

val write_hash : workdir:string -> n:int -> hash:Step.Field.Constant.t -> unit

val read_hash : workdir:string -> n:int -> Step.Field.Constant.t

val write_proof_file :
  path:string -> proof_base64:string -> max_proofs_verified:int -> unit

val read_proof_file : path:string -> string * int

val write_vk_file : path:string -> vk_base64:string -> vk_hash:string -> unit

val read_vk_file : path:string -> string * string
