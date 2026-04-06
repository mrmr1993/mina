(** Shared circuit utilities for proof conversion. *)

open! Core_kernel
module Step = Pickles.Impls.Step

(** Match o1js's [public_input_typ] which uses [Typ.array ~length:n Field.typ] *)
let public_input_typ n = Step.Typ.array ~length:n Step.Field.typ

let marker id =
  Step.assert_
    (Raw
       { kind = Zero
       ; values = [||]
       ; coeffs =
           Array.map ~f:Step.Field.Constant.of_int [| id; 1; 2; 3; 4; 5; 6 |]
       } )

let mark_typ before after (Typ typ : _ Step.Typ.t) : _ Step.Typ.t =
  Typ
    { typ with
      check =
        (fun x ->
          let open Step.Internal_Basic in
          let%bind () =
            assert_
              (Raw
                 { kind = Zero
                 ; values = [||]
                 ; coeffs =
                     Array.map ~f:Step.Field.Constant.of_int
                       [| before; 1; 2; 3; 4; 5; 6 |]
                 } )
          in
          let%bind () = typ.check x in
          assert_
            (Raw
               { kind = Zero
               ; values = [||]
               ; coeffs =
                   Array.map ~f:Step.Field.Constant.of_int
                     [| after; 1; 2; 3; 4; 5; 6 |]
               } ) )
    }

(** Replicates the [dummy_constraints] function from o1js's pickles_bindings.ml. *)
let dummy_constraints () =
  let open Step in
  let module Inner_curve = Pickles.Step_main_inputs.Inner_curve in
  let module Ops = Pickles.Step_main_inputs.Ops in
  let inner_curve_typ : (Field.t * Field.t, Kimchi_pasta.Pasta.Pallas.t) Typ.t =
    Typ.transport Inner_curve.typ ~there:Kimchi_pasta.Pasta.Pallas.to_affine_exn
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

(** Provable.switch for a generic Typ.t.
    Selects one of [values] based on which [bools] is true.
    Exactly one bool must be true (not enforced here — caller's responsibility).
    Matches nori Provable.switch(bools, type, values).

    Implementation: for each field component, compute sum of bool_i * value_i. *)
let provable_switch
    (type var value)
    (typ : (var, value) Step.Typ.t)
    (bools : Step.Field.t array)
    (values : var array) : var =
  let module FF = Snarky_foreign_field.Foreign_field in
  let (Step.Typ.Typ t) = typ in
  let n = Array.length bools in
  assert (Array.length values = n) ;
  let all_fields = Array.map values ~f:(fun v -> fst (t.var_to_fields v)) in
  let _, first_aux = t.var_to_fields values.(0) in
  let num_fields = Array.length all_fields.(0) in
  let result_fields = Array.init num_fields ~f:(fun j ->
      let terms = Array.to_list (Array.init n ~f:(fun i ->
          Step.Field.mul bools.(i) all_fields.(i).(j) )) in
      List.fold terms ~init:Step.Field.zero ~f:Step.Field.add ) in
  t.var_of_fields (result_fields, first_aux)
