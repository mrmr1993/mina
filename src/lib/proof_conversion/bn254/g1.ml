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

let glv_max_bits = 128

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
    ( Step.Field.if_ (Step.Boolean.Unsafe.of_cvar s1_neg)
        ~then_:(let l0, _, _ = neg_lambda in l0)
        ~else_:(let l0, _, _ = lambda_f3 in l0)
    , Step.Field.if_ (Step.Boolean.Unsafe.of_cvar s1_neg)
        ~then_:(let _, l1, _ = neg_lambda in l1)
        ~else_:(let _, l1, _ = lambda_f3 in l1)
    , Step.Field.if_ (Step.Boolean.Unsafe.of_cvar s1_neg)
        ~then_:(let _, _, l2 = neg_lambda in l2)
        ~else_:(let _, _, l2 = lambda_f3 in l2) )
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
        let s_plus_s0 = FF.sum [ s; s0 ] [ FF.Add ] ~f:r in
        let s_minus_s0 = FF.sum [ s; s0 ] [ FF.Sub ] ~f:r in
        let b = Step.Boolean.Unsafe.of_cvar s0_neg in
        let rhs0 =
          Step.Field.if_ b
            ~then_:(let l0, _, _ = s_plus_s0 in l0)
            ~else_:(let l0, _, _ = s_minus_s0 in l0)
        in
        let rhs1 =
          Step.Field.if_ b
            ~then_:(let _, l1, _ = s_plus_s0 in l1)
            ~else_:(let _, l1, _ = s_minus_s0 in l1)
        in
        let rhs2 =
          Step.Field.if_ b
            ~then_:(let _, _, l2 = s_plus_s0 in l2)
            ~else_:(let _, _, l2 = s_minus_s0 in l2)
        in
        FF.Sum.of_field3 (rhs0, rhs1, rhs2) )
  in
  FF.assert_mul_sum (FF.Field3_input s1) (FF.Field3_input lambda_sel)
    (FF.Sum_input rhs) ~f:r ;
  ((s0_neg, s0), (s1_neg, s1))

(* --- Bit slicing -------------------------------------------------------- *)

(** Decompose a native field element into individual bits and group into
    chunks of [chunk_size]. Returns chunks as native field elements.
    Matches o1js sliceField / sliceField3. *)
let slice_field (x : Step.Field.t) ~(max_bits : int) ~(chunk_size : int)
    ?(leftover_bits : Step.Field.t list option) () :
    Step.Field.t list * Step.Field.t list =
  let bits =
    Array.init max_bits ~f:(fun k ->
        Step.exists Step.Boolean.typ ~compute:(fun () ->
            let v = Step.As_prover.read_var x in
            let bi = FF.field_const_to_bignum v in
            Bignum_bigint.(shift_right bi k land one = one) ) )
  in
  let bit_fields = Array.map bits ~f:(fun b -> (b :> Step.Field.t)) in
  (* Verify: sum of bits*2^i = x *)
  let acc = ref Step.Field.zero in
  for i = 0 to max_bits - 1 do
    let coeff =
      Step.Field.constant
        (FF.bignum_to_field_const Bignum_bigint.(shift_left one i))
    in
    acc := Step.Field.(!acc + ((bits.(i) :> Step.Field.t) * coeff))
  done ;
  Step.Field.Assert.equal x !acc ;
  (* Group bits into chunks, handling leftover from previous limb *)
  let all_bits =
    match leftover_bits with
    | None -> Array.to_list bit_fields
    | Some prev -> prev @ Array.to_list bit_fields
  in
  let rec group acc remaining =
    match remaining with
    | [] -> (List.rev acc, [])
    | _ ->
      if List.length remaining < chunk_size then
        (List.rev acc, remaining)
      else
        let chunk_bits, rest = List.split_n remaining chunk_size in
        let chunk_val = ref Step.Field.zero in
        List.iteri chunk_bits ~f:(fun i bit ->
            let coeff =
              Step.Field.constant
                (FF.bignum_to_field_const Bignum_bigint.(shift_left one i))
            in
            chunk_val := Step.Field.(!chunk_val + (bit * coeff)) ) ;
        group (!chunk_val :: acc) rest
  in
  group [] all_bits

(** Slice a Field3 into chunks of [chunk_size] bits, with [max_bits] total. *)
let slice_field3 ((l0, l1, l2) : FF.Field3.t) ~(max_bits : int)
    ~(chunk_size : int) : Step.Field.t array =
  let limb_bits = FF.limb_bits in
  let bits0 = min limb_bits max_bits in
  let chunks0, leftover0 = slice_field l0 ~max_bits:bits0 ~chunk_size () in
  let remaining = max_bits - bits0 in
  if remaining <= 0 then Array.of_list chunks0
  else
    let bits1 = min limb_bits remaining in
    let chunks1, leftover1 =
      slice_field l1 ~max_bits:bits1 ~chunk_size ~leftover_bits:leftover0 ()
    in
    let remaining2 = remaining - bits1 in
    if remaining2 <= 0 then Array.of_list (chunks0 @ chunks1)
    else
      let chunks2, _leftover2 =
        slice_field l2 ~max_bits:remaining2 ~chunk_size
          ~leftover_bits:leftover1 ()
      in
      Array.of_list (chunks0 @ chunks1 @ chunks2)

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
    let i = FF.to_var index in
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
  let b = Step.Boolean.Unsafe.of_cvar cond in
  let y : FpA.t =
    FpA.of_field3_unsafe
      ( Step.Field.if_ b ~then_:y0_n ~else_:y0_p
      , Step.Field.if_ b ~then_:y1_n ~else_:y1_p
      , Step.Field.if_ b ~then_:y2_n ~else_:y2_p )
  in
  { x = pt.x; y }

(* --- Initial aggregator ------------------------------------------------ *)

(** Precomputed initial aggregator for BN254.
    Computed via SHA256("initial-aggregator" || p || r || a || b)
    then simpleMapToCurve. Must match o1js initialAggregator(). *)
let initial_aggregator : Constant.t =
  (* These values are precomputed from the o1js algorithm.
     TODO: verify these match by running nori and comparing gate dumps. *)
  { x = Bignum_bigint.of_string
        "657865848190250950586043384551149334256032752579024067073124622351051783979"
  ; y = Bignum_bigint.of_string
        "8359021910448911796605974533522365839990844082424982413428358974708560872337"
  }

(** 2^(maxBits-1) * IA, precomputed out-of-circuit. *)
let ia_final : Constant.t =
  let open Bignum_bigint in
  let ia = initial_aggregator in
  (* Compute 2^127 * IA using repeated doubling *)
  let md a = ((a % p) + p) % p in
  let dbl (x, y) =
    let x_sq = md (x * x) in
    let m = md (of_int 3 * x_sq * bignum_inv_mod (md (of_int 2 * y)) p) in
    let x3 = md ((m * m) - (of_int 2 * x)) in
    let y3 = md ((m * md (x - x3)) - y) in
    (x3, y3)
  in
  let pt = ref (ia.x, ia.y) in
  for _ = 1 to 127 do
    pt := dbl !pt
  done ;
  let x, y = !pt in
  { x; y }

(* --- Main scale (GLV + windowed MSM) ----------------------------------- *)

(** Scalar multiplication using GLV decomposition + windowed MSM.
    Matches o1js EllipticCurve.scale → multiScalarMul.
    For constant points (IC points), window_size = 4. *)
let scale (pt : Circuit.t) (scalar : FF.Field3.t) : Circuit.t =
  let window_size = 4 in

  (* 1. GLV decompose *)
  let (s0_neg, s0), (s1_neg, s1) = glv_decompose scalar in

  (* 2. Build point tables *)
  let table = get_point_table pt ~window_size in
  (* Endomorphism: phi(P) = (beta * P.x, P.y) *)
  let endo_table =
    Array.mapi table ~f:(fun i pt_i ->
        if i = 0 then pt_i
        else
          let beta_x = FF.mul (FpA.to_field3 pt_i.x)
              (FF.Field3.of_constant Bn254_params.glv_beta) ~f:p in
          let beta_x_a =
            match FpA.assert_almost_reduced [ FF.FpU.of_field3_unsafe beta_x ] ~f:p () with
            | [ a ] -> a
            | _ -> assert false
          in
          { Circuit.x = beta_x_a; y = pt_i.y } )
  in
  (* Apply sign negation to tables *)
  let table0 = Array.map table ~f:(fun pt_i -> negate_if s0_neg pt_i) in
  let table1 = Array.map endo_table ~f:(fun pt_i -> negate_if s1_neg pt_i) in

  (* 3. Slice scalars into chunks *)
  let chunks0 = slice_field3 s0 ~max_bits:glv_max_bits ~chunk_size:window_size in
  let chunks1 = slice_field3 s1 ~max_bits:glv_max_bits ~chunk_size:window_size in

  (* 4. Main loop *)
  let ia = of_constant initial_aggregator in
  let sum = ref ia in
  for i = glv_max_bits - 1 downto 0 do
    (* Add from table0 every window_size bits *)
    if i mod window_size = 0 then (
      let chunk_idx = i / window_size in
      let sj0 = chunks0.(chunk_idx) in
      let sj0_pt = array_get_point table0 sj0 in
      let added0 = add !sum sj0_pt in
      let is_zero0 = Step.Field.equal sj0 Step.Field.zero in
      let sel_if0 cond (a : Circuit.t) (b : Circuit.t) : Circuit.t =
        let sel_fpa fa fb =
          let a0, a1, a2 = FpA.to_field3 fa in
          let b0, b1, b2 = FpA.to_field3 fb in
          FpA.of_field3_unsafe
            ( Step.Field.if_ cond ~then_:b0 ~else_:a0
            , Step.Field.if_ cond ~then_:b1 ~else_:a1
            , Step.Field.if_ cond ~then_:b2 ~else_:a2 )
        in
        { x = sel_fpa a.x b.x; y = sel_fpa a.y b.y }
      in
      sum := sel_if0 is_zero0 added0 !sum ;
      (* Add from table1 *)
      let sj1 = chunks1.(chunk_idx) in
      let sj1_pt = array_get_point table1 sj1 in
      let added1 = add !sum sj1_pt in
      let is_zero1 = Step.Field.equal sj1 Step.Field.zero in
      let sel_if cond (a : Circuit.t) (b : Circuit.t) : Circuit.t =
        let sel_fpa fa fb =
          let a0, a1, a2 = FpA.to_field3 fa in
          let b0, b1, b2 = FpA.to_field3 fb in
          FpA.of_field3_unsafe
            ( Step.Field.if_ cond ~then_:b0 ~else_:a0
            , Step.Field.if_ cond ~then_:b1 ~else_:a1
            , Step.Field.if_ cond ~then_:b2 ~else_:a2 )
        in
        { x = sel_fpa a.x b.x; y = sel_fpa a.y b.y }
      in
      sum := sel_if is_zero1 added1 !sum ) ;
    if i > 0 then sum := double !sum
  done ;

  (* 5. Final correction: subtract 2^127 * IA *)
  let ia_neg = of_constant { ia_final with y = Bignum_bigint.((p - ia_final.y) % p) } in
  (* Assert sum != iaFinal (the result is non-zero) *)
  let ia_f = of_constant ia_final in
  let x_eq =
    let x0, x1, x2 = FpA.to_field3 !sum.x in
    let a0, a1, a2 = FpA.to_field3 ia_f.x in
    let e0 = Step.Field.equal x0 a0 in
    let e1 = Step.Field.equal x1 a1 in
    let e2 = Step.Field.equal x2 a2 in
    Step.Boolean.( &&& ) e0 (Step.Boolean.( &&& ) e1 e2)
  in
  let y_eq =
    let y0, y1, y2 = FpA.to_field3 !sum.y in
    let a0, a1, a2 = FpA.to_field3 ia_f.y in
    let e0 = Step.Field.equal y0 a0 in
    let e1 = Step.Field.equal y1 a1 in
    let e2 = Step.Field.equal y2 a2 in
    Step.Boolean.( &&& ) e0 (Step.Boolean.( &&& ) e1 e2)
  in
  let is_zero = Step.Boolean.( &&& ) x_eq y_eq in
  Step.Boolean.Assert.is_true (Step.Boolean.not is_zero) ;
  add !sum ia_neg
