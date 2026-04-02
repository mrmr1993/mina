(** G1 affine point operations on BN254. *)

open! Core_kernel
module FF = Snarky_foreign_field.Foreign_field
module FpA = FF.FpA

let p = Bn254_params.p

module Constant = struct
  type t = { x : FF.Bignum_bigint.t; y : FF.Bignum_bigint.t }
end

module Circuit = struct
  type t = { x : FpA.t; y : FpA.t }

  (** FpA check (MRC + weakBound) on each coordinate. *)
  let typ : (t, Constant.t) Pickles.Impls.Step.Typ.t =
    let fpa_typ = FpA.typ ~f:p in
    Pickles.Impls.Step.Typ.transport
      (Pickles.Impls.Step.Typ.tuple2 fpa_typ fpa_typ)
      ~there:(fun { Constant.x; y } -> (x, y))
      ~back:(fun (x, y) -> { Constant.x; y })
    |> Pickles.Impls.Step.Typ.transport_var
         ~there:(fun { x; y } -> (x, y))
         ~back:(fun (x, y) -> { x; y })
end

let of_constant (pt : Constant.t) : Circuit.t =
  { x = FpA.of_constant pt.x; y = FpA.of_constant pt.y }

let negate (pt : Circuit.t) : Circuit.t = { x = pt.x; y = FpA.neg pt.y ~f:p }

let add_nonzero (p1 : Circuit.t) (p2 : Circuit.t) : Circuit.t =
  let dx = FpA.sub p1.x p2.x ~f:p in
  let dy = FpA.sub p1.y p2.y ~f:p in
  let dx_a =
    match FpA.assert_almost_reduced [ dx ] ~f:p ~skip_mrc:true () with
    | [ a ] ->
        a
    | _ ->
        failwith "add_nonzero: dx"
  in
  let dy_a =
    match FpA.assert_almost_reduced [ dy ] ~f:p ~skip_mrc:true () with
    | [ a ] ->
        a
    | _ ->
        failwith "add_nonzero: dy"
  in
  let lambda = FpA.div dy_a dx_a ~f:p in
  let lambda_sq = FpA.mul lambda lambda ~f:p in
  let x3 =
    FF.FpU.sub
      (FF.FpU.sub lambda_sq (FpA.to_fpu p1.x) ~f:p)
      (FpA.to_fpu p2.x) ~f:p
  in
  let x3_a =
    match FpA.assert_almost_reduced [ x3 ] ~f:p ~skip_mrc:true () with
    | [ a ] ->
        a
    | _ ->
        failwith "add_nonzero: x3"
  in
  let dx1 = FpA.sub p1.x x3_a ~f:p in
  let dx1_a =
    match FpA.assert_almost_reduced [ dx1 ] ~f:p ~skip_mrc:true () with
    | [ a ] ->
        a
    | _ ->
        failwith "add_nonzero: dx1"
  in
  let y3 = FF.FpU.sub (FpA.mul lambda dx1_a ~f:p) (FpA.to_fpu p1.y) ~f:p in
  let y3_a =
    match FpA.assert_almost_reduced [ y3 ] ~f:p ~skip_mrc:true () with
    | [ a ] ->
        a
    | _ ->
        failwith "add_nonzero: y3"
  in
  { x = x3_a; y = y3_a }

let double (pt : Circuit.t) : Circuit.t =
  let x_sq = FpA.mul pt.x pt.x ~f:p in
  let three_x_sq = FF.FpU.add (FF.FpU.add x_sq x_sq ~f:p) x_sq ~f:p in
  let three_x_sq_a =
    match FpA.assert_almost_reduced [ three_x_sq ] ~f:p ~skip_mrc:true () with
    | [ a ] ->
        a
    | _ ->
        failwith "double: three_x_sq"
  in
  let two_y = FpA.add pt.y pt.y ~f:p in
  let two_y_a =
    match FpA.assert_almost_reduced [ two_y ] ~f:p ~skip_mrc:true () with
    | [ a ] ->
        a
    | _ ->
        failwith "double: two_y"
  in
  let lambda = FpA.div three_x_sq_a two_y_a ~f:p in
  let lambda_sq = FpA.mul lambda lambda ~f:p in
  let two_x = FpA.add pt.x pt.x ~f:p in
  let x3 = FF.FpU.sub lambda_sq two_x ~f:p in
  let x3_a =
    match FpA.assert_almost_reduced [ x3 ] ~f:p ~skip_mrc:true () with
    | [ a ] ->
        a
    | _ ->
        failwith "double: x3"
  in
  let dx = FpA.sub pt.x x3_a ~f:p in
  let dx_a =
    match FpA.assert_almost_reduced [ dx ] ~f:p ~skip_mrc:true () with
    | [ a ] ->
        a
    | _ ->
        failwith "double: dx"
  in
  let y3 = FF.FpU.sub (FpA.mul lambda dx_a ~f:p) (FpA.to_fpu pt.y) ~f:p in
  let y3_a =
    match FpA.assert_almost_reduced [ y3 ] ~f:p ~skip_mrc:true () with
    | [ a ] ->
        a
    | _ ->
        failwith "double: y3"
  in
  { x = x3_a; y = y3_a }

(** In-circuit scalar multiplication: point * scalar.
    Uses double-and-add with bit decomposition of the scalar.
    The scalar is a BN254 Fr element represented as Field3.

    Note: a production version should use windowed scalar mul with GLV
    decomposition. This simple double-and-add version is functionally
    correct but not gate-efficient. *)
let scale (pt : Circuit.t) (scalar : FF.Field3.t) : Circuit.t =
  let module Step = Pickles.Impls.Step in
  (* Decompose scalar limbs into bits.
     BN254 Fr has ~254 bits. Field3 stores 3×88-bit limbs. *)
  let l0, l1, l2 = scalar in
  let limb_bits = 88 in
  let top_bits = 78 in
  (* 254 - 2*88 = 78 *)
  let decompose_limb limb n_bits =
    Array.init n_bits ~f:(fun k ->
        Step.exists Step.Boolean.typ ~compute:(fun () ->
            let v = FF.field_const_to_bignum (Step.As_prover.read_var limb) in
            Bignum_bigint.(shift_right v k land one = one) ) )
  in
  let bits0 = decompose_limb l0 limb_bits in
  let bits1 = decompose_limb l1 limb_bits in
  let bits2 = decompose_limb l2 top_bits in
  (* Verify bit decomposition: sum of bits * 2^i == limb *)
  let verify_decomposition limb (bits : Step.Boolean.var array) n_bits =
    let sum = ref (Step.Field.of_int 0) in
    for i = 0 to n_bits - 1 do
      let coeff =
        Step.Field.constant
          (FF.bignum_to_field_const Bignum_bigint.(shift_left one i))
      in
      let bit_field = (bits.(i) :> Step.Field.t) in
      sum := Step.Field.add !sum (Step.Field.mul bit_field coeff)
    done ;
    Step.Field.Assert.equal limb !sum
  in
  verify_decomposition l0 bits0 limb_bits ;
  verify_decomposition l1 bits1 limb_bits ;
  verify_decomposition l2 bits2 top_bits ;
  (* All bits concatenated, LSB first *)
  let all_bits = Array.concat [ bits0; bits1; bits2 ] in
  let n_bits = Array.length all_bits in
  (* Double-and-add from MSB to LSB *)
  let acc = ref pt in
  let started = ref false in
  for i = n_bits - 1 downto 0 do
    if !started then acc := double !acc ;
    (* Conditionally add pt when bit is 1 *)
    if !started then
      let added = add_nonzero !acc pt in
      let bit = all_bits.(i) in
      (* Select: if bit then added else acc *)
      let sel (a : FpA.t) (b : FpA.t) : FpA.t =
        let a0, a1, a2 = FpA.to_field3 a in
        let b0, b1, b2 = FpA.to_field3 b in
        FpA.of_field3_unsafe
          ( Step.Field.if_ bit ~then_:a0 ~else_:b0
          , Step.Field.if_ bit ~then_:a1 ~else_:b1
          , Step.Field.if_ bit ~then_:a2 ~else_:b2 )
      in
      acc := { x = sel added.x !acc.x; y = sel added.y !acc.y }
    else (
      started := true ;
      ignore (all_bits.(i) : Step.Boolean.var) )
  done ;
  !acc
