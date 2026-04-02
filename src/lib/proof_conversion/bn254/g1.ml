(** G1 affine point operations on BN254.

    Matching o1js EllipticCurve.add / double / scale from
    o1js/src/lib/provable/gadgets/elliptic-curve.ts.

    add/double use the witness-and-assertMul pattern (not FpA.div).
    scale uses GLV decomposition + windowed MSM. *)

open! Core_kernel
module Step = Pickles.Impls.Step
module FF = Snarky_foreign_field.Foreign_field
module FpA = FF.FpA

let p = Bn254_params.p

(** Modular inverse via extended GCD. *)
let bignum_inv_mod a m =
  let open Bignum_bigint in
  let rec ext_gcd a b =
    if equal b zero then (a, one, zero)
    else
      let q = a / b in
      let r = a - (q * b) in
      let g, x, y = ext_gcd b r in
      (g, y, x - (q * y))
  in
  let a = ((a % m) + m) % m in
  let _, x, _ = ext_gcd a m in
  ((x % m) + m) % m

module Constant = struct
  type t = { x : FF.Bignum_bigint.t; y : FF.Bignum_bigint.t }
end

module Circuit = struct
  type t = { x : FpA.t; y : FpA.t }

  (** FpA check (MRC + weakBound) on each coordinate. *)
  let typ : (t, Constant.t) Step.Typ.t =
    let fpa_typ = FpA.typ ~f:p in
    Step.Typ.transport
      (Step.Typ.tuple2 fpa_typ fpa_typ)
      ~there:(fun { Constant.x; y } -> (x, y))
      ~back:(fun (x, y) -> { Constant.x; y })
    |> Step.Typ.transport_var
         ~there:(fun { x; y } -> (x, y))
         ~back:(fun (x, y) -> { x; y })
end

let of_constant (pt : Constant.t) : Circuit.t =
  { x = FpA.of_constant pt.x; y = FpA.of_constant pt.y }

let negate (pt : Circuit.t) : Circuit.t = { x = pt.x; y = FpA.neg pt.y ~f:p }

(* --- Helpers ------------------------------------------------------------ *)

let read_fpa (v : FpA.t) : Bignum_bigint.t =
  let l0, l1, l2 = FpA.to_field3 v in
  let r v = FF.field_const_to_bignum (Step.As_prover.read_var v) in
  Bignum_bigint.(r l0 + (r l1 * FF.two_to_limb) + (r l2 * FF.two_to_2limb))

(** Assert that a 2-element vector [x01, x2] does not equal a constant
    vector [c01, c2].  Matches nori's assertNotVectorEquals. *)
let assert_not_vector_equals (x01 : Step.Field.t) (x2 : Step.Field.t)
    ~(c01 : Step.Field.Constant.t) ~(c2 : Step.Field.Constant.t) : unit =
  let z0 =
    Step.exists Step.Field.typ ~compute:(fun () ->
        let x01v = Step.As_prover.read_var x01 in
        let x2v = Step.As_prover.read_var x2 in
        let d0 = Step.Field.Constant.(x01v - c01) in
        let d1 = Step.Field.Constant.(x2v - c2) in
        if not Step.Field.Constant.(equal d0 zero) then
          Step.Field.Constant.(one / d0)
        else if not Step.Field.Constant.(equal d1 zero) then
          Step.Field.Constant.(one / d1)
        else Step.Field.Constant.zero )
  in
  let z1 =
    Step.exists Step.Field.typ ~compute:(fun () ->
        let x01v = Step.As_prover.read_var x01 in
        let x2v = Step.As_prover.read_var x2 in
        let d0 = Step.Field.Constant.(x01v - c01) in
        let d1 = Step.Field.Constant.(x2v - c2) in
        if not Step.Field.Constant.(equal d0 zero) then Step.Field.Constant.zero
        else if not Step.Field.Constant.(equal d1 zero) then
          Step.Field.Constant.(one / d1)
        else Step.Field.Constant.zero )
  in
  (* (x01-c01)*z0 *)
  let prod0 = FF.bilinear x01 z0 ~a:Step.Field.Constant.one ~b:Step.Field.Constant.zero
      ~c:Step.Field.Constant.(zero - c01) ~d:Step.Field.Constant.zero in
  (* (x2-c2)*z1 *)
  let prod1 = FF.bilinear x2 z1 ~a:Step.Field.Constant.one ~b:Step.Field.Constant.zero
      ~c:Step.Field.Constant.(zero - c2) ~d:Step.Field.Constant.zero in
  (* prod0 + prod1 = 1 *)
  FF.assert_bilinear prod0 prod1
    ~a:Step.Field.Constant.zero ~b:Step.Field.Constant.one
    ~c:Step.Field.Constant.one ~d:Step.Field.Constant.(zero - one)

(* --- EC Addition (matching nori) ---------------------------------------- *)

(** EC point addition using witness-and-assertMul pattern.
    Witnesses slope m, result (x3, y3) and constrains:
      (x1-x2)*m = y1-y2
      m*m = x1+x2+x3
      (x1-x3)*m = y1+y3
    Also checks x1 != x2. *)
let add (p1 : Circuit.t) (p2 : Circuit.t) : Circuit.t =
  let x1 = FpA.to_field3 p1.x in
  let x2 = FpA.to_field3 p2.x in
  let y1 = FpA.to_field3 p1.y in
  let y2 = FpA.to_field3 p2.y in
  (* Constant case *)
  if FF.Field3.is_constant x1 && FF.Field3.is_constant x2
     && FF.Field3.is_constant y1 && FF.Field3.is_constant y2
  then (
    let x1v = FF.Field3.to_constant x1 in
    let x2v = FF.Field3.to_constant x2 in
    let y1v = FF.Field3.to_constant y1 in
    let y2v = FF.Field3.to_constant y2 in
    let open Bignum_bigint in
    let inv_mod a m =
      let rec ext_gcd a b =
        if equal b zero then (a, one, zero)
        else
          let q, r = (a / b, a % b) in
          let g, x, y = ext_gcd b r in
          (g, y, x - (q * y))
      in
      let _, x, _ = ext_gcd (((a % m) + m) % m) m in
      ((x % m) + m) % m
    in
    let dx = ((x1v - x2v) % p + p) % p in
    let dy = ((y1v - y2v) % p + p) % p in
    let m = dy * inv_mod dx p % p in
    let x3 = ((((m * m) % p) - x1v - x2v) % p + p) % p in
    let y3 = ((((m * (x1v - x3 + p)) % p) - y1v) % p + p) % p in
    { x = FpA.of_constant x3; y = FpA.of_constant y3 } )
  else
    (* Witness m, x3, y3 *)
    let cache = ref None in
    let get () =
      match !cache with
      | Some v -> v
      | None ->
        let x1v = read_fpa p1.x in
        let x2v = read_fpa p2.x in
        let y1v = read_fpa p1.y in
        let y2v = read_fpa p2.y in
        let open Bignum_bigint in
        let md a = ((a % p) + p) % p in
        let inv a = bignum_inv_mod a p in
        let dx = md (x1v - x2v) in
        let mv = md ((y1v - y2v) * inv dx) in
        let x3v = md ((mv * mv) - x1v - x2v) in
        let y3v = md ((mv * md (x1v - x3v)) - y1v) in
        let v = (mv, x3v, y3v) in
        cache := Some v ; v
    in
    let witness_field3 f =
      Step.exists FF.FpU.typ ~compute:(fun () -> f (get ()))
    in
    let m = witness_field3 (fun (mv, _, _) -> mv) in
    let x3 = witness_field3 (fun (_, x3v, _) -> x3v) in
    let y3 = witness_field3 (fun (_, _, y3v) -> y3v) in
    let m_a, x3_a, y3_a =
      match FpA.assert_almost_reduced [ m; x3; y3 ] ~f:p () with
      | [ a; b; c ] -> (a, b, c)
      | _ -> assert false
    in
    let m_f3 = FpA.to_field3 m_a in
    let x3_f3 = FpA.to_field3 x3_a in
    let y3_f3 = FpA.to_field3 y3_a in
    (* Check x1 != x2: deltaX = x1 - x2 + f, check != 0, != f, != 2f *)
    let deltaX = FF.sub x1 x2 ~f:p in
    let deltaX_0, deltaX_1, deltaX_2 = deltaX in
    let deltaX01 =
      FF.seal Step.Field.(
        deltaX_0 + (deltaX_1 * constant (FF.bignum_to_field_const FF.two_to_limb)))
    in
    let f0 = Bignum_bigint.(p land FF.limb_mask) in
    let f1 = Bignum_bigint.(shift_right p FF.limb_bits land FF.limb_mask) in
    let f2 = Bignum_bigint.(shift_right p (Int.( * ) 2 FF.limb_bits)) in
    let f01 = Bignum_bigint.(f0 + (f1 * FF.two_to_limb)) in
    let f2x2 =
      let _, _, f2x2 = FF.Field3.Constant.split Bignum_bigint.(p * of_int 2) in
      f2x2
    in
    assert_not_vector_equals deltaX01 deltaX_2
      ~c01:Step.Field.Constant.zero ~c2:Step.Field.Constant.zero ;
    assert_not_vector_equals deltaX01 deltaX_2
      ~c01:(FF.bignum_to_field_const f01) ~c2:(FF.bignum_to_field_const f2) ;
    Step.Field.Assert.not_equal deltaX_2
      (Step.Field.constant (FF.bignum_to_field_const f2x2)) ;
    (* (x1 - x2) * m = y1 - y2 *)
    let deltaY = FF.Sum.sub (FF.Sum.of_field3 y1) y2 in
    FF.assert_mul_sum (FF.Field3_input deltaX) (FF.Field3_input m_f3)
      (FF.Sum_input deltaY) ~f:p ;
    (* m * m = x1 + x2 + x3 *)
    let xSum =
      FF.Sum.add (FF.Sum.add (FF.Sum.of_field3 x1) x2) x3_f3
    in
    FF.assert_mul_sum (FF.Field3_input m_f3) (FF.Field3_input m_f3)
      (FF.Sum_input xSum) ~f:p ;
    (* (x1 - x3) * m = y1 + y3 *)
    let deltaX1X3 = FF.Sum.sub (FF.Sum.of_field3 x1) x3_f3 in
    let ySum = FF.Sum.add (FF.Sum.of_field3 y1) y3_f3 in
    FF.assert_mul_sum (FF.Sum_input deltaX1X3) (FF.Field3_input m_f3)
      (FF.Sum_input ySum) ~f:p ;
    { x = x3_a; y = y3_a }

(** EC point doubling using witness-and-assertMul pattern.
    Witnesses slope m, result (x3, y3) and constrains:
      x1*x1 = x1x1
      2*y1 * m = 3*x1x1 (+ a, but a=0 for BN254)
      m*m = 2*x1 + x3
      (x1-x3)*m = y1+y3 *)
let double (pt : Circuit.t) : Circuit.t =
  let x1 = FpA.to_field3 pt.x in
  let y1 = FpA.to_field3 pt.y in
  (* Constant case *)
  if FF.Field3.is_constant x1 && FF.Field3.is_constant y1 then (
    let x1v = FF.Field3.to_constant x1 in
    let y1v = FF.Field3.to_constant y1 in
    let open Bignum_bigint in
    let inv_mod a m =
      let rec ext_gcd a b =
        if equal b zero then (a, one, zero)
        else
          let q, r = (a / b, a % b) in
          let g, x, y = ext_gcd b r in
          (g, y, x - (q * y))
      in
      let _, x, _ = ext_gcd (((a % m) + m) % m) m in
      ((x % m) + m) % m
    in
    let x1_sq = x1v * x1v % p in
    let m = (of_int 3 * x1_sq) * inv_mod (of_int 2 * y1v % p) p % p in
    let x3 = ((m * m % p) - of_int 2 * x1v % p + p) % p in
    let y3 = (((m * ((x1v - x3 + p) % p)) % p) - y1v % p + p) % p in
    { x = FpA.of_constant x3; y = FpA.of_constant y3 } )
  else
    let cache = ref None in
    let get () =
      match !cache with
      | Some v -> v
      | None ->
        let x1v = read_fpa pt.x in
        let y1v = read_fpa pt.y in
        let open Bignum_bigint in
        let md a = ((a % p) + p) % p in
        let inv a = bignum_inv_mod a p in
        let x1_sq = md (x1v * x1v) in
        let mv = md (of_int 3 * x1_sq * inv (md (of_int 2 * y1v))) in
        let x3v = md ((mv * mv) - (of_int 2 * x1v)) in
        let y3v = md ((mv * md (x1v - x3v)) - y1v) in
        let v = (mv, x3v, y3v) in
        cache := Some v ; v
    in
    let witness_field3 f =
      Step.exists FF.FpU.typ ~compute:(fun () -> f (get ()))
    in
    let m = witness_field3 (fun (mv, _, _) -> mv) in
    let x3 = witness_field3 (fun (_, x3v, _) -> x3v) in
    let y3 = witness_field3 (fun (_, _, y3v) -> y3v) in
    let m_a, x3_a, y3_a =
      match FpA.assert_almost_reduced [ m; x3; y3 ] ~f:p () with
      | [ a; b; c ] -> (a, b, c)
      | _ -> assert false
    in
    let m_f3 = FpA.to_field3 m_a in
    let x3_f3 = FpA.to_field3 x3_a in
    let y3_f3 = FpA.to_field3 y3_a in
    (* x1^2 = x1x1 *)
    let x1x1 = FF.mul x1 x1 ~f:p in
    (* 2*y1 * m = 3*x1x1 (a=0 for BN254, so no +a term) *)
    let y1_times_2 = FF.Sum.add (FF.Sum.of_field3 y1) y1 in
    let x1x1_times_3 =
      FF.Sum.add (FF.Sum.add (FF.Sum.of_field3 x1x1) x1x1) x1x1
    in
    FF.assert_mul_sum (FF.Sum_input y1_times_2) (FF.Field3_input m_f3)
      (FF.Sum_input x1x1_times_3) ~f:p ;
    (* m*m = 2*x1 + x3 *)
    let xSum = FF.Sum.add (FF.Sum.add (FF.Sum.of_field3 x1) x1) x3_f3 in
    FF.assert_mul_sum (FF.Field3_input m_f3) (FF.Field3_input m_f3)
      (FF.Sum_input xSum) ~f:p ;
    (* (x1 - x3) * m = y1 + y3 *)
    let deltaX1X3 = FF.Sum.sub (FF.Sum.of_field3 x1) x3_f3 in
    let ySum = FF.Sum.add (FF.Sum.of_field3 y1) y3_f3 in
    FF.assert_mul_sum (FF.Sum_input deltaX1X3) (FF.Field3_input m_f3)
      (FF.Sum_input ySum) ~f:p ;
    { x = x3_a; y = y3_a }

(* Keep add_nonzero as alias for backward compatibility in non-MSM code *)
let add_nonzero = add

(** Placeholder for scale — will be replaced with GLV+MSM in next commit.
    For now, use the old double-and-add to keep everything compiling. *)
let scale (pt : Circuit.t) (scalar : FF.Field3.t) : Circuit.t =
  let module Step = Pickles.Impls.Step in
  let l0, l1, l2 = scalar in
  let limb_bits = 88 in
  let top_bits = 78 in
  let decompose_limb limb n_bits =
    Array.init n_bits ~f:(fun k ->
        Step.exists Step.Boolean.typ ~compute:(fun () ->
            let v = FF.field_const_to_bignum (Step.As_prover.read_var limb) in
            Bignum_bigint.(shift_right v k land one = one) ) )
  in
  let bits0 = decompose_limb l0 limb_bits in
  let bits1 = decompose_limb l1 limb_bits in
  let bits2 = decompose_limb l2 top_bits in
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
  let all_bits = Array.concat [ bits0; bits1; bits2 ] in
  let n_bits = Array.length all_bits in
  let acc = ref pt in
  let started = ref false in
  for i = n_bits - 1 downto 0 do
    if !started then acc := double !acc ;
    if !started then
      let added = add !acc pt in
      let bit = all_bits.(i) in
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
