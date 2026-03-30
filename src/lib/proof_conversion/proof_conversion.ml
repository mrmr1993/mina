(** Top-level proof conversion library.

    Converts non-native ZK proofs (Groth16, PLONK) into Mina-compatible
    proofs via recursive proof compression using Pickles. *)

open Core_kernel

module Step = Pickles.Impls.Step

(** Match o1js's [public_input_typ] which uses [Typ.array ~length:n Field.typ] *)
let public_input_typ n = Step.Typ.array ~length:n Step.Field.typ

(** Replicates the [dummy_constraints] function from o1js's pickles_bindings.ml.
    o1js injects these into every ZkProgram method to ensure the circuit always
    contains at least one instance of each EC gate type (EndoMulScalar,
    VarBaseMul, EndoMul, CompleteAdd), which is required by the Kimchi prover. *)
let dummy_constraints () =
  let open Step in
  let module Inner_curve = Pickles.Step_main_inputs.Inner_curve in
  let module Ops = Pickles.Step_main_inputs.Ops in
  let inner_curve_typ : (Field.t * Field.t, Kimchi_pasta.Pasta.Pallas.t) Typ.t =
    Typ.transport Inner_curve.typ
      ~there:Kimchi_pasta.Pasta.Pallas.to_affine_exn
      ~back:Kimchi_pasta.Pasta.Pallas.of_affine
  in
  let x = exists Field.typ ~compute:(fun () -> Field.Constant.of_int 3) in
  let g =
    exists inner_curve_typ ~compute:(fun _ -> Kimchi_pasta.Pasta.Pallas.one)
  in
  ignore
    ( Pickles.Scalar_challenge.to_field_checked'
        (module Step)
        ~num_bits:16
        (Kimchi_backend_common.Scalar_challenge.create x)
      : Field.t * Field.t * Field.t ) ;
  ignore
    ( Ops.scale_fast g ~num_bits:5
        (Pickles_types.Shifted_value.Type1.Shifted_value x)
      : Inner_curve.t ) ;
  ignore
    ( Pickles.Step_verifier.Scalar_challenge.endo g ~num_bits:4
        (Kimchi_backend_common.Scalar_challenge.create x)
      : Field.t * Field.t )

(** Module type for a proof conversion system. *)
module type PROOF_SYSTEM = sig
  (** Human-readable name of the proof system (e.g. "groth16", "plonk"). *)
  val name : string

  (** Parse a proof from a JSON file and convert it into a Mina-compatible
      proof. Returns the serialized proof data as a JSON string. *)
  val convert : input_path:string -> output_path:string -> unit
end

(** Groth16 proof conversion (RISC Zero). Not yet implemented. *)
module Groth16 : PROOF_SYSTEM = struct
  let name = "groth16"

  let convert ~input_path:_ ~output_path:_ =
    failwith "Groth16 proof conversion not yet implemented"
end

(** PLONK proof conversion (SP1). Not yet implemented. *)
module Plonk : PROOF_SYSTEM = struct
  let name = "plonk"

  let convert ~input_path:_ ~output_path:_ =
    failwith "PLONK proof conversion not yet implemented"
end
