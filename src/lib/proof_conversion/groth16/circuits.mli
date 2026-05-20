(** Groth16 proof-conversion circuit bodies.

    Each circuit takes an input Poseidon hash of the accumulator state,
    witnesses the accumulator, verifies the hash, runs its computation
    chunk, and returns the output hash of the updated state. *)

open Proof_conversion_bn254
module Step = Pickles.Impls.Step
module FF = Snarky_foreign_field.Foreign_field
module WT = Witness_tracker

(** Convert a tracker G1 point to a bn254 G1 constant. *)
val g1_of_tracker : WT.G1.t -> G1.Constant.t

(** A circuit body: input hash → output hash. *)
type circuit_body = Step.Field.t -> Step.Field.t

(** Total number of circuits. *)
val num_circuits : int

(** Witness the accumulator and verify the input hash matches. *)
val witness_and_verify_acc : Step.Field.t -> Accumulator.Circuit.t

(** [Provable.switch] for Fp12: select by a one-hot boolean mask. *)
val switch_fp12 :
  Step.Boolean.var array -> Fp12.Circuit.t array -> Fp12.Circuit.t

(** Hash a G1 point matching nori's [Poseidon.hashPacked]. *)
val hash_g1 : G1.Circuit.t -> Step.Field.t

(** Hash a packed Field3 array matching nori's [packToFields]. *)
val hash_packed_field3_array : FF.Field3.t array -> Step.Field.t

(** Convert VK constant lines to embedded circuit constants. *)
val vk_lines_to_circuit : WT.Line.t array -> Lines.G2Line.t array

(** Witness the accumulator, line hashes and b_lines, and verify the
    input hash. Shared setup for the ate-loop circuits (0-6). *)
val witness_ate_common :
     Step.Field.t
  -> Accumulator.Circuit.t * Step.Field.t array * Lines.G2Line.t array

(** Build the circuit body for [circuit_index]. *)
val build_circuit_body : vk:Vk_constants.t -> circuit_index:int -> circuit_body

(** Auxiliary typ for ate-loop circuits: accumulator + line_hashes. *)
val ate_aux_typ :
  ( Accumulator.Circuit.t * Step.Field.t array
  , Accumulator.Constant.t * Step.Field.Constant.t array )
  Step.Typ.t

(** Number of g values produced by ate circuit [circuit_index] (0-6). *)
val ate_g_count : int -> int

(** Auxiliary typ for circuits 0-12: acc + line_hashes + g_values. *)
val ate_aux_typ_with_g :
     circuit_index:int
  -> ( (Accumulator.Circuit.t * Step.Field.t array) * Fp12.Circuit.t array
     , (Accumulator.Constant.t * Step.Field.Constant.t array)
       * Fp12.Constant.t array )
     Step.Typ.t

(** As {!build_circuit_body} but also returns the accumulator,
    line_hashes and g_values for aux-output chaining. *)
val build_circuit_body_with_acc :
     vk:Vk_constants.t
  -> circuit_index:int
  -> Step.Field.t
  -> Step.Field.t
     * (Accumulator.Circuit.t * Step.Field.t array * Fp12.Circuit.t array)
