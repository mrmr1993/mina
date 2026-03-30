(** Shared circuit utilities for proof conversion. *)

module Step = Pickles.Impls.Step

(** Match o1js's [public_input_typ] which uses [Typ.array ~length:n Field.typ] *)
let public_input_typ n = Step.Typ.array ~length:n Step.Field.typ

(** Replicates the [dummy_constraints] function from o1js's pickles_bindings.ml. *)
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
