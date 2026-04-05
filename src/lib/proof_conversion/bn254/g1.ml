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
    (* Witness 9 raw fields (no MRC check — assertAlmostReduced handles it) *)
    let w i =
      Step.exists Step.Field.typ ~compute:(fun () ->
          let mv, x3v, y3v = get () in
          let vals = [| mv; x3v; y3v |] in
          let v = vals.(i / 3) in
          let limb = i mod 3 in
          let mask = FF.limb_mask in
          FF.bignum_to_field_const Bignum_bigint.(
            if Int.equal limb 0 then v land mask
            else if Int.equal limb 1 then shift_right v FF.limb_bits land mask
            else shift_right v (Int.( * ) 2 FF.limb_bits) land mask) )
    in
    let m : FF.FpU.t = FF.FpU.of_field3_unsafe (w 0, w 1, w 2) in
    let x3 : FF.FpU.t = FF.FpU.of_field3_unsafe (w 3, w 4, w 5) in
    let y3 : FF.FpU.t = FF.FpU.of_field3_unsafe (w 6, w 7, w 8) in
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
    (* Witness 9 raw fields (no MRC check — assertAlmostReduced handles it) *)
    let w i =
      Step.exists Step.Field.typ ~compute:(fun () ->
          let mv, x3v, y3v = get () in
          let vals = [| mv; x3v; y3v |] in
          let v = vals.(i / 3) in
          let limb = i mod 3 in
          let mask = FF.limb_mask in
          FF.bignum_to_field_const Bignum_bigint.(
            if Int.equal limb 0 then v land mask
            else if Int.equal limb 1 then shift_right v FF.limb_bits land mask
            else shift_right v (Int.( * ) 2 FF.limb_bits) land mask) )
    in
    let m : FF.FpU.t = FF.FpU.of_field3_unsafe (w 0, w 1, w 2) in
    let x3 : FF.FpU.t = FF.FpU.of_field3_unsafe (w 3, w 4, w 5) in
    let y3 : FF.FpU.t = FF.FpU.of_field3_unsafe (w 6, w 7, w 8) in
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

(* --- GLV decomposition -------------------------------------------------- *)

(** Computed from GLV lattice vectors as ceil(log2(max(maxS0, maxS1)))
    where maxS_i = (|v_i0| + |v_i1|) / 2 + 1.
    Matches nori's Curve.Endo.decomposeMaxBits. *)
let glv_max_bits =
  let open Bignum_bigint in
  let max_s0 = (abs Bn254_params.glv_n11 + abs Bn254_params.glv_n12) / of_int 2 + one in
  let max_s1 = (abs Bn254_params.glv_n12 + abs Bn254_params.glv_n22) / of_int 2 + one in
  let m = max max_s0 max_s1 in
  (* bit_length = ceil(log2(m+1)), matching nori's log2 *)
  Z.log2up (Bigint.to_zarith_bigint m)

(** GLV decompose: s = s0 + s1*lambda (mod r).
    Out-of-circuit: uses lattice basis to find small s0, s1.
    In-circuit: witnesses s0, s1, signs; constrains s1*lambda = s ∓ s0. *)
let glv_decompose (s : FF.Field3.t) :
    (Step.Field.t * FF.Field3.t) * (Step.Field.t * FF.Field3.t) =
  let r = Bn254_params.r in
  let lambda = Bn254_params.glv_lambda in
  (* Witness s0_neg, s00, s01, s1_neg, s10, s11 *)
  let cache = ref None in
  let get () =
    match !cache with
    | Some v -> v
    | None ->
      let sv =
        let l0, l1, l2 = s in
        let r v = FF.field_const_to_bignum (Step.As_prover.read_var v) in
        Bignum_bigint.(r l0 + (r l1 * FF.two_to_limb) + (r l2 * FF.two_to_2limb))
      in
      let open Bignum_bigint in
      let v00 = Bn254_params.glv_n11 in
      let v01 = Bn254_params.glv_n12 in
      let v10 = neg Bn254_params.glv_n12 in
      let v11 = Bn254_params.glv_n22 in
      let det = r in
      let div_round a b =
        let q = a / b in
        let rem = a - (q * b) in
        if abs rem * of_int 2 > abs b then
          if Bool.equal (rem > zero) (b > zero) then q + one else q - one
        else q
      in
      let x0n = div_round (neg v11 * sv) det in
      let x1n = div_round (v10 * sv) det in
      let s0 = (v00 * x0n) + (v01 * x1n) + sv in
      let s1 = (v10 * x0n) + (v11 * x1n) in
      let v = (s0 < zero, abs s0, s1 < zero, abs s1) in
      cache := Some v ; v
  in
  let s0_neg =
    Step.exists Step.Field.typ ~compute:(fun () ->
        let neg, _, _, _ = get () in
        if neg then Step.Field.Constant.one else Step.Field.Constant.zero)
  in
  let s00 =
    Step.exists Step.Field.typ ~compute:(fun () ->
        let _, a, _, _ = get () in
        FF.bignum_to_field_const Bignum_bigint.(a land FF.limb_mask))
  in
  let s01 =
    Step.exists Step.Field.typ ~compute:(fun () ->
        let _, a, _, _ = get () in
        FF.bignum_to_field_const Bignum_bigint.(shift_right a FF.limb_bits land FF.limb_mask))
  in
  let s1_neg =
    Step.exists Step.Field.typ ~compute:(fun () ->
        let _, _, neg, _ = get () in
        if neg then Step.Field.Constant.one else Step.Field.Constant.zero)
  in
  let s10 =
    Step.exists Step.Field.typ ~compute:(fun () ->
        let _, _, _, a = get () in
        FF.bignum_to_field_const Bignum_bigint.(a land FF.limb_mask))
  in
  let s11 =
    Step.exists Step.Field.typ ~compute:(fun () ->
        let _, _, _, a = get () in
        FF.bignum_to_field_const Bignum_bigint.(shift_right a FF.limb_bits land FF.limb_mask))
  in
  let s0 : FF.Field3.t = (s00, s01, Step.Field.zero) in
  let s1 : FF.Field3.t = (s10, s11, Step.Field.zero) in
  Step.assert_ (Boolean s0_neg) ;
  Step.assert_ (Boolean s1_neg) ;
  (* Prove s1*lambda = s - s0  (or s + s0 if s0 negative) *)
  let neg_lambda = FF.Field3.of_constant
      Bignum_bigint.((r - lambda) % r) in
  let lambda_f3 = FF.Field3.of_constant lambda in
  let lambda_sel =
    let l0 = FF.if_field s1_neg
        ~then_:(let l0, _, _ = neg_lambda in l0)
        ~else_:(let l0, _, _ = lambda_f3 in l0)
    in
    let l1 = FF.if_field s1_neg
        ~then_:(let _, l1, _ = neg_lambda in l1)
        ~else_:(let _, l1, _ = lambda_f3 in l1)
    in
    let l2 = FF.if_field s1_neg
        ~then_:(let _, _, l2 = neg_lambda in l2)
        ~else_:(let _, _, l2 = lambda_f3 in l2)
    in
    (l0, l1, l2)
  in
  let rhs =
    (* rhs = s - s0 or s + s0 depending on s0_neg.
       Nori uses Provable.if on Sum results. *)
    ( if Option.is_some (Step.Field.to_constant s0_neg) then
        let is_neg =
          let c = Option.value_exn (Step.Field.to_constant s0_neg) in
          Bignum_bigint.(FF.field_const_to_bignum c = one)
        in
        if is_neg then FF.Sum.add (FF.Sum.of_field3 s) s0
        else FF.Sum.sub (FF.Sum.of_field3 s) s0
      else
        let s_plus_s0 =
          FF.Sum.finish_simple (FF.Sum.add (FF.Sum.of_field3 s) s0) ~f:r
        in
        let s_minus_s0 =
          FF.Sum.finish_simple (FF.Sum.sub (FF.Sum.of_field3 s) s0) ~f:r
        in
        let rhs0 =
          FF.if_field s0_neg
            ~then_:(let l0, _, _ = s_plus_s0 in l0)
            ~else_:(let l0, _, _ = s_minus_s0 in l0)
        in
        let rhs1 =
          FF.if_field s0_neg
            ~then_:(let _, l1, _ = s_plus_s0 in l1)
            ~else_:(let _, l1, _ = s_minus_s0 in l1)
        in
        let rhs2 =
          FF.if_field s0_neg
            ~then_:(let _, _, l2 = s_plus_s0 in l2)
            ~else_:(let _, _, l2 = s_minus_s0 in l2)
        in
        FF.Sum.of_field3 (rhs0, rhs1, rhs2) )
  in
  FF.assert_mul_sum (FF.Field3_input s1) (FF.Field3_input lambda_sel)
    (FF.Sum_input rhs) ~f:r ;
  ((s0_neg, s0), (s1_neg, s1))

(* --- Bit slicing -------------------------------------------------------- *)

(** Provable method for slicing a field element into bit chunks of
    [chunk_size]. Serves as a range check that the input is in
    [0, 2^max_bits).  Matches o1js sliceField exactly.

    Returns { chunks; leftover_size } where leftover_size is the
    number of unfilled bit positions in the last chunk. *)
type slice_result =
  { chunks : Step.Field.t list
  ; leftover_size : int
  }

let slice_field (x : Step.Field.t) ~(max_bits : int) ~(chunk_size : int)
    ?(leftover : slice_result option) () : slice_result =
  (* let bits = exists(maxBits, () => bigIntToBits(x)) *)
  let bits =
    Array.init max_bits ~f:(fun k ->
        Step.exists Step.Field.typ ~compute:(fun () ->
            let v = Step.As_prover.read_var x in
            let bi = FF.field_const_to_bignum v in
            if Bignum_bigint.(shift_right bi k land one = one)
            then Step.Field.Constant.one
            else Step.Field.Constant.zero ) )
  in
  let chunks = ref [] in
  let the_sum = ref Step.Field.zero in
  (* if there's a leftover chunk from a previous sliceField() call,
     we complete it *)
  ( match leftover with
  | Some { chunks = previous; leftover_size = size } when size > 0 ->
      let remaining_chunk = ref Step.Field.zero in
      for i = 0 to size - 1 do
        let bit = bits.(i) in
        Step.assert_ (Boolean bit) ;
        let coeff =
          Step.Field.constant
            (FF.bignum_to_field_const Bignum_bigint.(shift_left one i))
        in
        remaining_chunk := Step.Field.(!remaining_chunk + (bit * coeff))
      done ;
      let sealed = FF.seal !remaining_chunk in
      the_sum := sealed ;
      (* previous[previous.length - 1] += remaining * 2^(chunkSize - size) *)
      let prev = List.last_exn previous in
      let shift_amt = chunk_size - size in
      let shift_c =
        Step.Field.constant
          (FF.bignum_to_field_const Bignum_bigint.(shift_left one shift_amt))
      in
      let patched = Step.Field.(prev + (sealed * shift_c)) in
      (* Replace last element of previous chunks list *)
      chunks :=
        List.mapi previous ~f:(fun j c ->
            if j = List.length previous - 1 then patched else c )
  | Some { chunks = previous; _ } ->
      (* leftover_size = 0: no bits to process, but copy previous chunks *)
      chunks := previous
  | None ->
      () ) ;
  (* let i = leftover?.leftoverSize ?? 0 *)
  let start_i = match leftover with Some l -> l.leftover_size | None -> 0 in
  let i = ref start_i in
  while !i < max_bits do
    (* prove that chunk has chunkSize bits *)
    let chunk = ref Step.Field.zero in
    let size = min (max_bits - !i) chunk_size in
    for j = 0 to size - 1 do
      let bit = bits.(!i + j) in
      Step.assert_ (Boolean bit) ;
      let coeff =
        Step.Field.constant
          (FF.bignum_to_field_const Bignum_bigint.(shift_left one j))
      in
      chunk := Step.Field.(!chunk + (bit * coeff))
    done ;
    let sealed = FF.seal !chunk in
    (* prove that chunks add up to x *)
    let shift =
      Step.Field.constant
        (FF.bignum_to_field_const Bignum_bigint.(shift_left one !i))
    in
    the_sum := Step.Field.(!the_sum + (sealed * shift)) ;
    chunks := !chunks @ [ sealed ] ;
    i := !i + chunk_size
  done ;
  (* sum.assertEquals(x) *)
  Step.Field.Assert.equal !the_sum x ;
  let leftover_size = !i - max_bits in
  { chunks = !chunks; leftover_size }

(** Slice a Field3 into chunks of [chunk_size] bits, with [max_bits] total.
    Matches o1js sliceField3 exactly. *)
let slice_field3 ((x0, x1, x2) : FF.Field3.t) ~(max_bits : int)
    ~(chunk_size : int) : Step.Field.t array =
  let l = FF.limb_bits in
  (* first limb *)
  let result0 = slice_field x0 ~max_bits:(min l max_bits) ~chunk_size () in
  let max_bits = max_bits - l in
  if max_bits <= 0 then Array.of_list result0.chunks
  else
    (* second limb *)
    let result1 =
      slice_field x1 ~max_bits:(min l max_bits) ~chunk_size ~leftover:result0 ()
    in
    let max_bits = max_bits - l in
    if max_bits <= 0 then Array.of_list (result0.chunks @ result1.chunks)
    else
      (* third limb *)
      let result2 =
        slice_field x2 ~max_bits ~chunk_size ~leftover:result1 ()
      in
      Array.of_list (result0.chunks @ result1.chunks @ result2.chunks)

(* --- Array lookup ------------------------------------------------------- *)

(** Provable array lookup: given [array] and [index], returns array[index].
    For each element j, proves z[j]*(i-j) = a - array[j].
    Matches o1js arrayGet. *)
let array_get (array : Step.Field.t array) (index : Step.Field.t) :
    Step.Field.t =
  match Step.Field.to_constant index with
  | Some c ->
    let idx = Bignum_bigint.to_int_exn (FF.field_const_to_bignum c) in
    array.(idx)
  | None ->
    let i = index in
    let a =
      Step.exists Step.Field.typ ~compute:(fun () ->
          let iv = Step.As_prover.read_var i in
          let idx = Bignum_bigint.to_int_exn (FF.field_const_to_bignum iv) in
          Step.As_prover.read_var array.(idx) )
    in
    let n = Array.length array in
    for j = 0 to n - 1 do
      let zj =
        Step.exists Step.Field.typ ~compute:(fun () ->
            let av = Step.As_prover.read_var a in
            let aj = Step.As_prover.read_var array.(j) in
            let iv = Step.As_prover.read_var i in
            let d_denom =
              Step.Field.Constant.(iv - of_int j)
            in
            if Step.Field.Constant.(equal d_denom zero) then
              Step.Field.Constant.zero
            else Step.Field.Constant.((av - aj) / d_denom) )
      in
      let cj = Step.Field.Constant.of_int j in
      ( match Step.Field.to_constant array.(j) with
      | Some aj_const ->
        (* zj*i + (-j)*zj + 0*i + array[j] = a *)
        FF.generic
          ~ql:Step.Field.Constant.(zero - cj)
          ~qr:Step.Field.Constant.zero
          ~qo:Step.Field.Constant.(zero - one)
          ~qm:Step.Field.Constant.one
          ~qc:aj_const
          ~left:zj ~right:i ~out:a
      | None ->
        let a_minus_aj = FF.to_var Step.Field.(a - array.(j)) in
        (* zj*i + (-j)*zj + 0*i + 0 = a_minus_aj *)
        FF.generic
          ~ql:Step.Field.Constant.(zero - cj)
          ~qr:Step.Field.Constant.zero
          ~qo:Step.Field.Constant.(zero - one)
          ~qm:Step.Field.Constant.one
          ~qc:Step.Field.Constant.zero
          ~left:zj ~right:i ~out:a_minus_aj )
    done ;
    a

(** Lookup a G1 point from a table by index.
    Each coordinate has 3 limbs, so 6 array_get calls total.
    Pre-materializes the index to avoid repeated to_var inside arrayGet. *)
let array_get_point (table : Circuit.t array) (index : Step.Field.t) :
    Circuit.t =
  (* Pre-materialize index so arrayGet's to_var is a no-op *)
  let index = FF.to_var index in
  let get_limb coord_fn limb_fn =
    let arr = Array.map table ~f:(fun pt ->
        let f3 = FpA.to_field3 (coord_fn pt) in
        limb_fn f3 )
    in
    array_get arr index
  in
  let x0 = get_limb (fun pt -> pt.x) (fun (l, _, _) -> l) in
  let x1 = get_limb (fun pt -> pt.x) (fun (_, l, _) -> l) in
  let x2 = get_limb (fun pt -> pt.x) (fun (_, _, l) -> l) in
  let y0 = get_limb (fun pt -> pt.y) (fun (l, _, _) -> l) in
  let y1 = get_limb (fun pt -> pt.y) (fun (_, l, _) -> l) in
  let y2 = get_limb (fun pt -> pt.y) (fun (_, _, l) -> l) in
  { x = FpA.of_field3_unsafe (x0, x1, x2)
  ; y = FpA.of_field3_unsafe (y0, y1, y2)
  }

(* --- Point table -------------------------------------------------------- *)

(** Build table [zero, P, 2P, 3P, ..., (2^w - 1)*P] *)
let get_point_table (pt : Circuit.t) ~(window_size : int) : Circuit.t array =
  let n = 1 lsl window_size in
  let zero_pt : Circuit.t =
    { x = FpA.of_constant Bignum_bigint.zero
    ; y = FpA.of_constant Bignum_bigint.zero
    }
  in
  if n = 2 then [| zero_pt; pt |]
  else
    let table = Array.create ~len:n zero_pt in
    table.(1) <- pt ;
    table.(2) <- double pt ;
    for i = 3 to n - 1 do
      table.(i) <- add table.(i - 1) pt
    done ;
    table

(* --- Conditional negation ----------------------------------------------- *)

let negate_if (cond : Step.Field.t) (pt : Circuit.t) : Circuit.t =
  let neg_y = FpA.neg pt.y ~f:p in
  let y0_n, y1_n, y2_n = FpA.to_field3 neg_y in
  let y0_p, y1_p, y2_p = FpA.to_field3 pt.y in
  let yl0 = FF.if_field cond ~then_:y0_n ~else_:y0_p in
  let yl1 = FF.if_field cond ~then_:y1_n ~else_:y1_p in
  let yl2 = FF.if_field cond ~then_:y2_n ~else_:y2_p in
  let y : FpA.t = FpA.of_field3_unsafe (yl0, yl1, yl2) in
  { x = pt.x; y }

(* --- Initial aggregator ------------------------------------------------ *)

(** Precomputed initial aggregator for BN254.
    Computed via SHA256("initial-aggregator" || p || r || a || b)
    then simpleMapToCurve. Must match o1js initialAggregator(). *)
let initial_aggregator : Constant.t =
  { x = Bignum_bigint.of_string
        "657865848190250950586043384551149334256032752579024067073124622351051783979"
  ; y = Bignum_bigint.of_string
        "8359021910448911796605974533522365839990844082424982413428358974708560872337"
  }

(** 2^(maxBits-1) * IA, precomputed out-of-circuit.
    Matches: let iaFinal = Curve.scale(Curve.fromNonzero(ia), 1n << BigInt(maxBits - 1)) *)
let ia_final : Constant.t =
  let open Bignum_bigint in
  let ia = initial_aggregator in
  let md a = ((a % p) + p) % p in
  let dbl (x, y) =
    let x_sq = md (x * x) in
    let m = md (of_int 3 * x_sq * bignum_inv_mod (md (of_int 2 * y)) p) in
    let x3 = md ((m * m) - (of_int 2 * x)) in
    let y3 = md ((m * md (x - x3)) - y) in
    (x3, y3)
  in
  let pt = ref (ia.x, ia.y) in
  for _ = 1 to glv_max_bits - 1 do
    pt := dbl !pt
  done ;
  let x, y = !pt in
  { x; y }

(* --- Point equality (matching nori equals) ------------------------------ *)

(** Check whether a point equals a constant point.
    Matches nori's equals(p1, p2, Curve) which uses
    ForeignField.equals per coordinate: pack x01 = x0 + x1*2^88,
    then check (x01, x2) == (c01, c2) or (c01+f01, c2+f2).
    cf. elliptic-curve.ts:211 *)
let point_equals (pt : Circuit.t) (c : Constant.t) : Step.Boolean.var =
  let ff_equals (x : FpA.t) (cv : Bignum_bigint.t) : Step.Boolean.var =
    let x0, x1, x2 = FpA.to_field3 x in
    let x01 = FF.seal Step.Field.(x0 + (x1 * constant (FF.bignum_to_field_const FF.two_to_limb))) in
    let l2_mask = Bignum_bigint.(FF.two_to_2limb - one) in
    let two_l = Int.( * ) 2 FF.limb_bits in
    let c01 = Bignum_bigint.(cv land l2_mask) in
    let c2 = Bignum_bigint.(shift_right cv two_l) in
    let c_plus_f = Bignum_bigint.(cv + p) in
    let cpf01 = Bignum_bigint.(c_plus_f land l2_mask) in
    let cpf2 = Bignum_bigint.(shift_right c_plus_f two_l) in
    let is_c =
      let e01 = FF.field_var_equal x01
          (Step.Field.constant (FF.bignum_to_field_const c01)) in
      let e2 = FF.field_var_equal x2
          (Step.Field.constant (FF.bignum_to_field_const c2)) in
      Step.Boolean.( &&& ) e01 e2
    in
    let is_cpf =
      let e01 = FF.field_var_equal x01
          (Step.Field.constant (FF.bignum_to_field_const cpf01)) in
      let e2 = FF.field_var_equal x2
          (Step.Field.constant (FF.bignum_to_field_const cpf2)) in
      Step.Boolean.( &&& ) e01 e2
    in
    Step.Boolean.( ||| ) is_c is_cpf
  in
  let x_eq = ff_equals pt.x c.x in
  let y_eq = ff_equals pt.y c.y in
  Step.Boolean.( &&& ) x_eq y_eq

(* --- Provable.if for points (matching nori) ----------------------------- *)

(** Conditional select for G1 points.
    Matches nori's Provable.if(condition, Point, if_true, if_false).
    cf. elliptic-curve.ts:498:
      sum = Provable.if(sj.equals(0), Point, sum, added)
    When condition is true, returns if_true; when false, returns if_false. *)
let provable_if_point (condition : Step.Field.t)
    ~(if_true : Circuit.t) ~(if_false : Circuit.t) : Circuit.t =
  let sel_fpa fa fb =
    let a0, a1, a2 = FpA.to_field3 fa in
    let b0, b1, b2 = FpA.to_field3 fb in
    let r0 = FF.if_field condition ~then_:a0 ~else_:b0 in
    let r1 = FF.if_field condition ~then_:a1 ~else_:b1 in
    let r2 = FF.if_field condition ~then_:a2 ~else_:b2 in
    FpA.of_field3_unsafe (r0, r1, r2)
  in
  let x = sel_fpa if_true.x if_false.x in
  let y = sel_fpa if_true.y if_false.y in
  { Circuit.x; y }

(* --- Multi-scalar multiplication (matching nori multiScalarMul) --------- *)

(** Multi-scalar multiplication: s_0 * P_0 + ... + s_(n-1) * P_(n-1)
    with GLV decomposition and windowed tables.

    Matches o1js multiScalarMul (elliptic-curve.ts:409-526).

    The function takes pre-decomposed arrays:
    - [n] is the total number of effective scalars (2 * original n after GLV)
    - [scalars]: the absolute-value GLV sub-scalars
    - [tables]: point tables with sign-negation already applied
    - [window_sizes]: per-scalar window sizes
    - [max_bits]: number of bits per sub-scalar (glv_max_bits)
    - [scalar_chunks]: pre-sliced scalar bit-chunks *)
let multi_scalar_mul
    ~(n : int)
    ~(tables : Circuit.t array array)
    ~(points : Circuit.t array)
    ~(window_sizes : int array)
    ~(max_bits : int)
    ~(scalar_chunks : Step.Field.t array array)
    : Circuit.t =

  (* initialize sum to the initial aggregator
     cf. elliptic-curve.ts:483-484:
       ia ??= initialAggregator(Curve);
       let sum = Point.from(ia); *)
  let sum = ref (of_constant initial_aggregator) in

  (* Main loop: for (let i = maxBits - 1; i >= 0; i--)
     cf. elliptic-curve.ts:486-509 *)
  for i = max_bits - 1 downto 0 do

    (* add in multiple of each point
       cf. elliptic-curve.ts:488: for (let j = 0; j < n; j++) *)
    for j = 0 to n - 1 do
      let window_size = window_sizes.(j) in
      if i mod window_size = 0 then begin
        let chunk_idx = i / window_size in

        (* pick point to add based on the scalar chunk
           cf. elliptic-curve.ts:492-493:
             let sj = scalarChunks[j][i / windowSize];
             let sjP = windowSize === 1 ? points[j] : arrayGetGeneric(...) *)
        let sj = scalar_chunks.(j).(chunk_idx) in
        let sj_p =
          if window_size = 1 then points.(j)
          else array_get_point tables.(j) sj
        in

        (* ec addition
           cf. elliptic-curve.ts:495: let added = add(sum, sjP, Curve) *)
        let added = add !sum sj_p in

        (* handle degenerate case (if sj = 0, Gj is all zeros and the add result is garbage)
           cf. elliptic-curve.ts:498:
             sum = Provable.if(sj.equals(0), Point, sum, added) *)
        let is_zero = FF.field_var_equal sj Step.Field.zero in
        sum := provable_if_point (is_zero :> Step.Field.t)
            ~if_true:!sum ~if_false:added
      end
    done ;

    (* cf. elliptic-curve.ts:504: if (i === 0) break *)
    if i > 0 then
      (* jointly double all points
         cf. elliptic-curve.ts:508: sum = double(sum, Curve) *)
      sum := double !sum
  done ;

  (* the sum is now 2^(b-1)*IA + sum_i s_i*P_i
     cf. elliptic-curve.ts:513:
       let iaFinal = Curve.scale(Curve.fromNonzero(ia), 1n << BigInt(maxBits - 1)) *)
  let is_zero = point_equals !sum ia_final in

  (* cf. elliptic-curve.ts:516-518:
       isZero.assertFalse();
       sum = add(sum, Point.from(Curve.negate(iaFinal)), Curve) *)
  Step.Boolean.Assert.is_true (Step.Boolean.not is_zero) ;
  let ia_neg = of_constant
      { ia_final with y = Bignum_bigint.((p - ia_final.y) % p) }
  in
  add !sum ia_neg

(* --- Scale (GLV + MSM entry point) -------------------------------------- *)

(** Scalar multiplication: scalar * point.
    Matches o1js EllipticCurve.scale (elliptic-curve.ts:189-201)
    which delegates to multiScalarMul after GLV decomposition.

    For constant points (IC points in Groth16), window_size = 4. *)
let scale (pt : Circuit.t) (scalar : FF.Field3.t) : Circuit.t =
  let window_size = 4 in
  let n_original = 1 in

  (* GLV decompose: s = s0 + s1 * lambda (mod r)
     cf. elliptic-curve.ts:435-471 *)
  let (s0_neg, s0), (s1_neg, s1) = glv_decompose scalar in

  (* Build point table: [0, P, 2P, ..., (2^w - 1)*P]
     cf. elliptic-curve.ts:429-431 *)
  let table = get_point_table pt ~window_size in

  (* Endomorphism table: phi(P) = (beta * P.x, P.y), with MRC stack
     cf. elliptic-curve.ts:452-457:
       let endoTable = table.map((P, i) => {
         if (i === 0) return P;
         let [phiP, betaXBound] = endomorphism(Curve, P);
         mrcStack.push(betaXBound);
         return phiP;
       }) *)
  let endo_table =
    Array.mapi table ~f:(fun i pt_i ->
        if i = 0 then pt_i
        else
          let beta_x = FF.mul (FpA.to_field3 pt_i.x)
              (FF.Field3.of_constant Bn254_params.glv_beta) ~f:p in
          let beta_x_a =
            match FpA.assert_almost_reduced
                    [ FF.FpU.of_field3_unsafe beta_x ] ~f:p () with
            | [ a ] -> a
            | _ -> assert false
          in
          { Circuit.x = beta_x_a; y = pt_i.y } )
  in

  (* Apply sign negation to tables
     cf. elliptic-curve.ts:458-459:
       tables2[2*i]   = table.map(P => negateIf(s0.isNegative, P, f));
       tables2[2*i+1] = endoTable.map(P => negateIf(s1.isNegative, P, f)); *)
  let table0 = Array.map table ~f:(negate_if s0_neg) in
  let table1 = Array.map endo_table ~f:(negate_if s1_neg) in

  (* After GLV, n doubles: n = 2 * n_original
     cf. elliptic-curve.ts:460-471 *)
  let n = 2 * n_original in
  let tables = [| table0; table1 |] in
  let points = [| table0.(1); table1.(1) |] in
  let window_sizes = [| window_size; window_size |] in

  (* Slice scalars into chunks
     cf. elliptic-curve.ts:476-478:
       scalarChunks.push(sliceField3(scalars[si], { maxBits, chunkSize: windowSizes[si] })) *)
  let scalar_chunks =
    [| slice_field3 s0 ~max_bits:glv_max_bits ~chunk_size:window_size
     ; slice_field3 s1 ~max_bits:glv_max_bits ~chunk_size:window_size
     |]
  in

  multi_scalar_mul ~n ~tables ~points ~window_sizes
    ~max_bits:glv_max_bits ~scalar_chunks
