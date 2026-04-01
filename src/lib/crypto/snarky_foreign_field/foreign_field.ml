(** Foreign field arithmetic over 3-limb (88-bit) representations.

    Implements Field3 — a representation of field elements as three 88-bit
    limbs suitable for 254-bit foreign field moduli (e.g. BN254 Fp/Fr).

    Adapted from feature/groth16-and-kzg-foreign-field branch with
    debugging artifacts removed. *)

open Core_kernel
module Bignum_bigint = Bigint
module Circuit = Kimchi_pasta_snarky_backend.Step_impl

(* ------------------------------------------------------------------ *)
(* Constants                                                           *)
(* ------------------------------------------------------------------ *)

let limb_bits = 88

let two_to_limb = Bignum_bigint.(pow (of_int 2) (of_int limb_bits))

let limb_mask = Bignum_bigint.(two_to_limb - one)

let two_to_2limb = Bignum_bigint.(two_to_limb * two_to_limb)

let _two_to_3limb = Bignum_bigint.(two_to_2limb * two_to_limb)

(* ------------------------------------------------------------------ *)
(* Conversion helpers                                                  *)
(* ------------------------------------------------------------------ *)

let field_const_to_bignum (x : Circuit.Field.Constant.t) : Bignum_bigint.t =
  Circuit.Bigint.(to_bignum_bigint (of_field x))

let bignum_to_field_const (x : Bignum_bigint.t) : Circuit.Field.Constant.t =
  if Bignum_bigint.(x < zero) then
    let p =
      Circuit.Bigint.(
        to_bignum_bigint (of_field Circuit.Field.Constant.(zero - one)))
    in
    let p = Bignum_bigint.(p + one) in
    Circuit.Bigint.(
      to_field (of_bignum_bigint Bignum_bigint.(((x % p) + p) % p)))
  else Circuit.Bigint.(to_field (of_bignum_bigint x))

let bit_slice (x : Bignum_bigint.t) ~(start : int) ~(length : int) :
    Bignum_bigint.t =
  Bignum_bigint.(
    shift_right x start land (pow (of_int 2) (of_int length) - one))

let witness_bit_slice (v : Circuit.Field.t) ~(start : int) ~(length : int) :
    Circuit.Field.t =
  Circuit.exists Circuit.Field.typ ~compute:(fun () ->
      let v_const = Circuit.As_prover.read_var v in
      let v_bignum = field_const_to_bignum v_const in
      bignum_to_field_const (bit_slice v_bignum ~start ~length) )

(* ------------------------------------------------------------------ *)
(* Field3: 3-limb foreign field element                                *)
(* ------------------------------------------------------------------ *)

module Field3 = struct
  module Constant = struct
    type t = Bignum_bigint.t

    let split (x : Bignum_bigint.t) :
        Bignum_bigint.t * Bignum_bigint.t * Bignum_bigint.t =
      let open Bignum_bigint in
      let l0 = x land limb_mask in
      let l1 = shift_right x limb_bits land limb_mask in
      let l2 = shift_right x (Int.( * ) 2 limb_bits) land limb_mask in
      (l0, l1, l2)

    let combine
        ((l0, l1, l2) : Bignum_bigint.t * Bignum_bigint.t * Bignum_bigint.t) :
        Bignum_bigint.t =
      let open Bignum_bigint in
      l0 + (l1 * two_to_limb) + (l2 * two_to_2limb)

    let of_bigint (x : Bignum_bigint.t) : t = x

    let zero : t = Bignum_bigint.zero

    let one : t = Bignum_bigint.one

    let mod_ (x : t) ~(f : Bignum_bigint.t) : t = Bignum_bigint.(x % f)
  end

  type t = Circuit.Field.t * Circuit.Field.t * Circuit.Field.t

  let of_constant (x : Constant.t) : t =
    let l0, l1, l2 = Constant.split x in
    ( Circuit.Field.constant (bignum_to_field_const l0)
    , Circuit.Field.constant (bignum_to_field_const l1)
    , Circuit.Field.constant (bignum_to_field_const l2) )

  let of_limbs
      ((l0, l1, l2) : Circuit.Field.t * Circuit.Field.t * Circuit.Field.t) : t =
    (l0, l1, l2)

  let limbs ((l0, l1, l2) : t) :
      Circuit.Field.t * Circuit.Field.t * Circuit.Field.t =
    (l0, l1, l2)

  let is_constant ((l0, l1, l2) : t) : bool =
    Option.is_some (Circuit.Field.to_constant l0)
    && Option.is_some (Circuit.Field.to_constant l1)
    && Option.is_some (Circuit.Field.to_constant l2)

  let to_constant_opt ((l0, l1, l2) : t) : Constant.t option =
    match
      ( Circuit.Field.to_constant l0
      , Circuit.Field.to_constant l1
      , Circuit.Field.to_constant l2 )
    with
    | Some c0, Some c1, Some c2 ->
        let v0 = field_const_to_bignum c0 in
        let v1 = field_const_to_bignum c1 in
        let v2 = field_const_to_bignum c2 in
        Some (Constant.combine (v0, v1, v2))
    | _ ->
        None

  let to_constant (x : t) : Constant.t =
    match to_constant_opt x with
    | Some c ->
        c
    | None ->
        failwith "Field3.to_constant: not a constant"

  (** Forward reference to multi_range_check, set after it's defined. *)
  let check_ref : (t -> unit) ref = ref (fun _ -> ())

  (** Snarky Typ for Field3 values. Witnessing via [exists typ ~compute]
      automatically applies multi_range_check to ensure each limb is
      in [0, 2^88). *)
  let typ : (t, Constant.t) Circuit.Typ.t =
    Circuit.Typ.Typ
      { size_in_field_elements = 3
      ; constraint_system_auxiliary = (fun () -> ())
      ; value_to_fields =
          (fun x ->
            let l0, l1, l2 = Constant.split x in
            ( [| bignum_to_field_const l0
               ; bignum_to_field_const l1
               ; bignum_to_field_const l2
              |]
            , () ) )
      ; value_of_fields =
          (fun (fields, ()) ->
            let l0 = field_const_to_bignum fields.(0) in
            let l1 = field_const_to_bignum fields.(1) in
            let l2 = field_const_to_bignum fields.(2) in
            Constant.combine (l0, l1, l2) )
      ; var_to_fields = (fun (l0, l1, l2) -> ([| l0; l1; l2 |], ()))
      ; var_of_fields =
          (fun (fields, ()) -> (fields.(0), fields.(1), fields.(2)))
      ; check =
          (fun (l0, l1, l2) ->
            Circuit.make_checked (fun () -> !check_ref (l0, l1, l2)) )
      }
end

(* ------------------------------------------------------------------ *)
(* Range check gadgets                                                 *)
(* ------------------------------------------------------------------ *)

(** Range check a single 88-bit limb using RangeCheck0 gate.
    Returns the top two 12-bit plookup chunks (bits 64-87). *)
let range_check0 (v0 : Circuit.Field.t) ~(compact : bool) :
    Circuit.Field.t * Circuit.Field.t =
  let ws = witness_bit_slice v0 in
  let v0c0 = ws ~start:0 ~length:2 in
  let v0c1 = ws ~start:2 ~length:2 in
  let v0c2 = ws ~start:4 ~length:2 in
  let v0c3 = ws ~start:6 ~length:2 in
  let v0c4 = ws ~start:8 ~length:2 in
  let v0c5 = ws ~start:10 ~length:2 in
  let v0c6 = ws ~start:12 ~length:2 in
  let v0c7 = ws ~start:14 ~length:2 in
  let v0p5 = ws ~start:16 ~length:12 in
  let v0p4 = ws ~start:28 ~length:12 in
  let v0p3 = ws ~start:40 ~length:12 in
  let v0p2 = ws ~start:52 ~length:12 in
  let v0p1 = ws ~start:64 ~length:12 in
  let v0p0 = ws ~start:76 ~length:12 in
  Circuit.assert_
    (RangeCheck0
       { v0
       ; v0p0
       ; v0p1
       ; v0p2
       ; v0p3
       ; v0p4
       ; v0p5
       ; v0c0
       ; v0c1
       ; v0c2
       ; v0c3
       ; v0c4
       ; v0c5
       ; v0c6
       ; v0c7
       ; compact =
           ( if compact then Circuit.Field.Constant.one
           else Circuit.Field.Constant.zero )
       } ) ;
  (v0p1, v0p0)

(** Range check using RangeCheck1 gate. Combines three limbs'
    plookup chunks into one gate. *)
let range_check1 ~(x64 : Circuit.Field.t) ~(x76 : Circuit.Field.t)
    ~(y64 : Circuit.Field.t) ~(y76 : Circuit.Field.t) ~(z : Circuit.Field.t)
    ~(yz : Circuit.Field.t) : unit =
  let ws = witness_bit_slice z in
  let v2c0 = ws ~start:22 ~length:2 in
  let v2c1 = ws ~start:24 ~length:2 in
  let v2c2 = ws ~start:26 ~length:2 in
  let v2c3 = ws ~start:28 ~length:2 in
  let v2c4 = ws ~start:30 ~length:2 in
  let v2c5 = ws ~start:32 ~length:2 in
  let v2c6 = ws ~start:34 ~length:2 in
  let v2c7 = ws ~start:36 ~length:2 in
  let v2p0 = ws ~start:38 ~length:12 in
  let v2p1 = ws ~start:50 ~length:12 in
  let v2p2 = ws ~start:62 ~length:12 in
  let v2p3 = ws ~start:74 ~length:12 in
  let v2c8 = ws ~start:86 ~length:2 in
  let v2c19 = ws ~start:0 ~length:2 in
  let v2c18 = ws ~start:2 ~length:2 in
  let v2c17 = ws ~start:4 ~length:2 in
  let v2c16 = ws ~start:6 ~length:2 in
  let v2c15 = ws ~start:8 ~length:2 in
  let v2c14 = ws ~start:10 ~length:2 in
  let v2c13 = ws ~start:12 ~length:2 in
  let v2c12 = ws ~start:14 ~length:2 in
  let v2c11 = ws ~start:16 ~length:2 in
  let v2c10 = ws ~start:18 ~length:2 in
  let v2c9 = ws ~start:20 ~length:2 in
  Circuit.assert_
    (RangeCheck1
       { v2 = z
       ; v12 = yz
       ; v2c0
       ; v2p0
       ; v2p1
       ; v2p2
       ; v2p3
       ; v2c1
       ; v2c2
       ; v2c3
       ; v2c4
       ; v2c5
       ; v2c6
       ; v2c7
       ; v2c8
       ; v2c9
       ; v2c10
       ; v2c11
       ; v0p0 = x76
       ; v0p1 = x64
       ; v1p0 = y76
       ; v1p1 = y64
       ; v2c12
       ; v2c13
       ; v2c14
       ; v2c15
       ; v2c16
       ; v2c17
       ; v2c18
       ; v2c19
       } )

(* ------------------------------------------------------------------ *)
(* Seal and to_var                                                     *)
(* ------------------------------------------------------------------ *)

(** Seal a circuit variable — materializes compound Cvars into fresh
    variables. Matches o1js Field.seal(). *)
let seal (x : Circuit.Field.t) : Circuit.Field.t =
  match Circuit.Field.to_constant_and_terms x with
  | Some _, [] | None, [] ->
      x
  | None, [ (c, _) ] when Circuit.Field.Constant.(equal c one) ->
      x
  | Some c, [ (s, _) ]
    when Circuit.Field.Constant.(equal c zero)
         && Circuit.Field.Constant.(equal s one) ->
      x
  | _ ->
      let v =
        Circuit.exists Circuit.Field.typ ~compute:(fun () ->
            Circuit.As_prover.read_var x )
      in
      Circuit.assert_ (Equal (x, v)) ;
      v

(** Convert to a simple variable, sealing if compound. *)
let to_var (x : Circuit.Field.t) : Circuit.Field.t =
  match Circuit.Field.to_constant_and_terms x with
  | None, [ (c, _) ] when Circuit.Field.Constant.(equal c one) ->
      x
  | Some c, [ (s, _) ]
    when Circuit.Field.Constant.(equal c zero)
         && Circuit.Field.Constant.(equal s one) ->
      x
  | _ ->
      let v =
        Circuit.exists Circuit.Field.typ ~compute:(fun () ->
            Circuit.As_prover.read_var x )
      in
      Circuit.assert_ (Equal (v, x)) ;
      v

(* ------------------------------------------------------------------ *)
(* Multi-range checks                                                  *)
(* ------------------------------------------------------------------ *)

(** Range check all three limbs of a Field3 to [0, 2^88). *)
let multi_range_check ((x, y, z) : Field3.t) : unit =
  if Field3.is_constant (x, y, z) then (
    let check v name =
      let v_bignum =
        field_const_to_bignum (Option.value_exn (Circuit.Field.to_constant v))
      in
      if Bignum_bigint.(v_bignum >= two_to_limb) then
        failwith (sprintf "multi_range_check: %s >= 2^%d" name limb_bits)
    in
    check x "x" ; check y "y" ; check z "z" )
  else
    let x = to_var x in
    let y = to_var y in
    let z = to_var z in
    let zero = to_var (Circuit.Field.constant Circuit.Field.Constant.zero) in
    let x64, x76 = range_check0 x ~compact:false in
    let y64, y76 = range_check0 y ~compact:false in
    range_check1 ~x64 ~x76 ~y64 ~y76 ~z ~yz:zero

(* Initialize the Field3.typ check function now that multi_range_check exists *)
let () = Field3.check_ref := multi_range_check

(** Range check a compact 2-limb value [xy] (176 bits) and a single
    limb [z] (88 bits). Returns the three individual limbs. *)
let compact_multi_range_check (xy : Circuit.Field.t) (z : Circuit.Field.t) :
    Field3.t =
  if
    Option.is_some (Circuit.Field.to_constant xy)
    && Option.is_some (Circuit.Field.to_constant z)
  then (
    let xy_bignum =
      field_const_to_bignum (Option.value_exn (Circuit.Field.to_constant xy))
    in
    let z_bignum =
      field_const_to_bignum (Option.value_exn (Circuit.Field.to_constant z))
    in
    if Bignum_bigint.(xy_bignum >= two_to_2limb) then
      failwith "compact_multi_range_check: xy >= 2^176" ;
    if Bignum_bigint.(z_bignum >= two_to_limb) then
      failwith "compact_multi_range_check: z >= 2^88" ;
    let x = Bignum_bigint.(xy_bignum land limb_mask) in
    let y = Bignum_bigint.(shift_right xy_bignum limb_bits) in
    ( Circuit.Field.constant (bignum_to_field_const x)
    , Circuit.Field.constant (bignum_to_field_const y)
    , z ) )
  else
    let xy = to_var xy in
    let z = to_var z in
    let x =
      Circuit.exists Circuit.Field.typ ~compute:(fun () ->
          let xy_v = Circuit.As_prover.read_var xy in
          let xy_bignum = field_const_to_bignum xy_v in
          bignum_to_field_const Bignum_bigint.(xy_bignum land limb_mask) )
    in
    let y =
      Circuit.exists Circuit.Field.typ ~compute:(fun () ->
          let xy_v = Circuit.As_prover.read_var xy in
          let xy_bignum = field_const_to_bignum xy_v in
          bignum_to_field_const Bignum_bigint.(shift_right xy_bignum limb_bits) )
    in
    let z64, z76 = range_check0 z ~compact:false in
    let x64, x76 = range_check0 x ~compact:true in
    range_check1 ~x64:z64 ~x76:z76 ~y64:x64 ~y76:x76 ~z:y ~yz:xy ;
    (x, y, z)

(* ------------------------------------------------------------------ *)
(* Almost-reduced assertion                                            *)
(* ------------------------------------------------------------------ *)

(** Compute a bound value for the high limb that proves x < f
    (or x <= f depending on the modulus structure). *)
let weak_bound (x2 : Circuit.Field.t) ~(f : Bignum_bigint.t) : Circuit.Field.t =
  let l2_mask = Bignum_bigint.(two_to_2limb - one) in
  if Bignum_bigint.(f land l2_mask = zero) then
    let bound =
      Bignum_bigint.(two_to_limb - shift_right f (Int.( * ) 2 limb_bits))
    in
    Circuit.Field.(x2 + constant (bignum_to_field_const bound))
  else
    let bound =
      Bignum_bigint.(limb_mask - shift_right f (Int.( * ) 2 limb_bits))
    in
    Circuit.Field.(x2 + constant (bignum_to_field_const bound))

(** Assert that each Field3 in the list is almost-reduced modulo [f],
    meaning its high limb is bounded. *)
let assert_almost_reduced (xs : Field3.t list) ~(f : Bignum_bigint.t)
    ~(skip_mrc : bool) : unit =
  let bounds = ref [] in
  let flush_bounds () =
    match !bounds with
    | [ b1; b2; b3 ] ->
        multi_range_check (b1, b2, b3) ;
        bounds := []
    | _ ->
        ()
  in
  List.iter xs ~f:(fun ((_, _, x2) as x) ->
      if not skip_mrc then multi_range_check x ;
      bounds := !bounds @ [ weak_bound x2 ~f ] ;
      if List.length !bounds = 3 then flush_bounds () ) ;
  match !bounds with
  | [ b1 ] ->
      multi_range_check
        ( b1
        , Circuit.exists Circuit.Field.typ ~compute:(fun () ->
              Circuit.Field.Constant.zero )
        , Circuit.exists Circuit.Field.typ ~compute:(fun () ->
              Circuit.Field.Constant.zero ) )
  | [ b1; b2 ] ->
      multi_range_check
        ( b1
        , b2
        , Circuit.exists Circuit.Field.typ ~compute:(fun () ->
              Circuit.Field.Constant.zero ) )
  | _ ->
      ()

(* ------------------------------------------------------------------ *)
(* Foreign field addition / subtraction                                *)
(* ------------------------------------------------------------------ *)

type sign = Add | Sub

let sign_to_bigint = function
  | Add ->
      Bignum_bigint.one
  | Sub ->
      Bignum_bigint.(neg one)

(** Single foreign field addition/subtraction using ForeignFieldAdd gate. *)
let single_add (x : Field3.t) (y : Field3.t) ~(sign : sign)
    ~(f : Bignum_bigint.t) : Field3.t * Circuit.Field.t =
  let f0, f1, f2 = Field3.Constant.split f in
  let compute_add () =
    let x0, x1, x2 = x in
    let y0, y1, y2 = y in
    let xv0 = field_const_to_bignum (Circuit.As_prover.read_var x0) in
    let xv1 = field_const_to_bignum (Circuit.As_prover.read_var x1) in
    let xv2 = field_const_to_bignum (Circuit.As_prover.read_var x2) in
    let yv0 = field_const_to_bignum (Circuit.As_prover.read_var y0) in
    let yv1 = field_const_to_bignum (Circuit.As_prover.read_var y1) in
    let yv2 = field_const_to_bignum (Circuit.As_prover.read_var y2) in
    let x_big = Field3.Constant.combine (xv0, xv1, xv2) in
    let y_big = Field3.Constant.combine (yv0, yv1, yv2) in
    let s = sign_to_bigint sign in
    let r = Bignum_bigint.(x_big + (s * y_big)) in
    let overflow =
      if Bignum_bigint.(f = zero) then Bignum_bigint.zero
      else if Bignum_bigint.(s = one) && Bignum_bigint.(r >= f) then
        Bignum_bigint.one
      else if Bignum_bigint.(s = neg one) && Bignum_bigint.(r < zero) then
        Bignum_bigint.(neg one)
      else Bignum_bigint.zero
    in
    let l2_mask = Bignum_bigint.(two_to_2limb - one) in
    let x01 = Bignum_bigint.(xv0 + (xv1 * two_to_limb)) in
    let y01 = Bignum_bigint.(yv0 + (yv1 * two_to_limb)) in
    let f01 = Bignum_bigint.(f0 + (f1 * two_to_limb)) in
    let r01 = Bignum_bigint.(x01 + (s * y01) - (overflow * f01)) in
    let carry = Bignum_bigint.(shift_right r01 (Int.( * ) 2 limb_bits)) in
    let r01_masked = Bignum_bigint.(r01 land l2_mask) in
    let r0_val = Bignum_bigint.(r01_masked land limb_mask) in
    let r1_val = Bignum_bigint.(shift_right r01_masked limb_bits) in
    let r2_val = Bignum_bigint.(xv2 + (s * yv2) - (overflow * f2) + carry) in
    (r0_val, r1_val, r2_val, overflow, carry)
  in
  let cache = ref None in
  let get_cached () =
    match !cache with
    | Some v ->
        v
    | None ->
        let v = compute_add () in
        cache := Some v ;
        v
  in
  let r0 =
    Circuit.exists Circuit.Field.typ ~compute:(fun () ->
        let r0, _, _, _, _ = get_cached () in
        bignum_to_field_const r0 )
  in
  let r1 =
    Circuit.exists Circuit.Field.typ ~compute:(fun () ->
        let _, r1, _, _, _ = get_cached () in
        bignum_to_field_const r1 )
  in
  let r2 =
    Circuit.exists Circuit.Field.typ ~compute:(fun () ->
        let _, _, r2, _, _ = get_cached () in
        bignum_to_field_const r2 )
  in
  let overflow =
    Circuit.exists Circuit.Field.typ ~compute:(fun () ->
        let _, _, _, overflow, _ = get_cached () in
        bignum_to_field_const overflow )
  in
  let carry =
    Circuit.exists Circuit.Field.typ ~compute:(fun () ->
        let _, _, _, _, carry = get_cached () in
        bignum_to_field_const carry )
  in
  let x0, x1, x2 = x in
  let y0, y1, y2 = y in
  let sign_const =
    match sign with
    | Add ->
        Circuit.Field.Constant.one
    | Sub ->
        Circuit.Field.Constant.(zero - one)
  in
  Circuit.assert_
    (ForeignFieldAdd
       { left_input_lo = x0
       ; left_input_mi = x1
       ; left_input_hi = x2
       ; right_input_lo = y0
       ; right_input_mi = y1
       ; right_input_hi = y2
       ; field_overflow = overflow
       ; carry
       ; foreign_field_modulus0 = bignum_to_field_const f0
       ; foreign_field_modulus1 = bignum_to_field_const f1
       ; foreign_field_modulus2 = bignum_to_field_const f2
       ; sign = sign_const
       } ) ;
  ((r0, r1, r2), overflow)

(** Sum a list of Field3 values with given signs.
    [xs] has one more element than [signs]:
    result = xs[0] +/- xs[1] +/- xs[2] ... *)
let sum (xs : Field3.t list) (signs : sign list) ~(f : Bignum_bigint.t) :
    Field3.t =
  assert (List.length xs = List.length signs + 1) ;
  if List.for_all xs ~f:Field3.is_constant then
    let x_bigs = List.map xs ~f:Field3.to_constant in
    let s = sign_to_bigint in
    let result =
      List.fold2_exn (List.tl_exn x_bigs) signs ~init:(List.hd_exn x_bigs)
        ~f:(fun acc xi sign_i -> Bignum_bigint.(acc + (s sign_i * xi)))
    in
    let result_mod = Bignum_bigint.(((result % f) + f) % f) in
    Field3.of_constant result_mod
  else
    let xs =
      List.map xs ~f:(fun (l0, l1, l2) ->
          let v0 = to_var l0 in
          let v1 = to_var l1 in
          let v2 = to_var l2 in
          (v0, v1, v2) )
    in
    let result = ref (List.hd_exn xs) in
    List.iter2_exn (List.tl_exn xs) signs ~f:(fun xi sign_i ->
        let r, _overflow = single_add !result xi ~sign:sign_i ~f in
        result := r ) ;
    let r0, r1, r2 = !result in
    Circuit.assert_
      (Raw { kind = Zero; values = [| r0; r1; r2 |]; coeffs = [||] }) ;
    (* Indirect range check matching o1js *)
    let r0, r1, r2 = !result in
    let r0_trunc =
      Circuit.exists Circuit.Field.typ ~compute:(fun () ->
          let v = Circuit.As_prover.read_var r0 in
          bignum_to_field_const
            Bignum_bigint.(field_const_to_bignum v land limb_mask) )
    in
    let r1_trunc =
      Circuit.exists Circuit.Field.typ ~compute:(fun () ->
          let v = Circuit.As_prover.read_var r1 in
          bignum_to_field_const
            Bignum_bigint.(field_const_to_bignum v land limb_mask) )
    in
    let r2_trunc =
      Circuit.exists Circuit.Field.typ ~compute:(fun () ->
          let v = Circuit.As_prover.read_var r2 in
          bignum_to_field_const
            Bignum_bigint.(field_const_to_bignum v land limb_mask) )
    in
    multi_range_check (r0_trunc, r1_trunc, r2_trunc) ;
    Circuit.assert_ (Equal (r0, r0_trunc)) ;
    Circuit.assert_ (Equal (r1, r1_trunc)) ;
    Circuit.assert_ (Equal (r2, r2_trunc)) ;
    !result

let add (x : Field3.t) (y : Field3.t) ~(f : Bignum_bigint.t) : Field3.t =
  sum [ x; y ] [ Add ] ~f

let sub (x : Field3.t) (y : Field3.t) ~(f : Bignum_bigint.t) : Field3.t =
  sum [ x; y ] [ Sub ] ~f

let negate (x : Field3.t) ~(f : Bignum_bigint.t) : Field3.t =
  sub (Field3.of_constant Bignum_bigint.zero) x ~f

(* ------------------------------------------------------------------ *)
(* Foreign field multiplication                                        *)
(* ------------------------------------------------------------------ *)

(** Multiply two Field3 values using ForeignFieldMul gate, without
    range-checking the result. Returns (quotient, remainder01, remainder2). *)
let multiply_no_range_check (a : Field3.t) (b : Field3.t) ~(f : Bignum_bigint.t)
    : Field3.t * Circuit.Field.t * Circuit.Field.t =
  let f_ =
    Bignum_bigint.(pow (of_int 2) (of_int (Int.( * ) 3 limb_bits)) - f)
  in
  let f_0, f_1, f_2 = Field3.Constant.split f_ in
  let f2 = Bignum_bigint.(shift_right f (Int.( * ) 2 limb_bits)) in
  let f2_bound = Bignum_bigint.(two_to_limb - f2 - one) in
  let cache = ref None in
  let get_cached () =
    match !cache with
    | Some v ->
        v
    | None ->
        let a0, a1, a2 = a in
        let b0, b1, b2 = b in
        let av0 = field_const_to_bignum (Circuit.As_prover.read_var a0) in
        let av1 = field_const_to_bignum (Circuit.As_prover.read_var a1) in
        let av2 = field_const_to_bignum (Circuit.As_prover.read_var a2) in
        let bv0 = field_const_to_bignum (Circuit.As_prover.read_var b0) in
        let bv1 = field_const_to_bignum (Circuit.As_prover.read_var b1) in
        let bv2 = field_const_to_bignum (Circuit.As_prover.read_var b2) in
        let a_big = Field3.Constant.combine (av0, av1, av2) in
        let b_big = Field3.Constant.combine (bv0, bv1, bv2) in
        let ab = Bignum_bigint.(a_big * b_big) in
        let q = Bignum_bigint.(ab / f) in
        let r = Bignum_bigint.(ab - (q * f)) in
        let q0, q1, q2 = Field3.Constant.split q in
        let _r0, _r1, r2 = Field3.Constant.split r in
        let r01 =
          Bignum_bigint.(
            (r land limb_mask)
            + (shift_right r limb_bits land limb_mask * two_to_limb))
        in
        let p0 = Bignum_bigint.((av0 * bv0) + (q0 * f_0)) in
        let p1 =
          Bignum_bigint.((av0 * bv1) + (av1 * bv0) + (q0 * f_1) + (q1 * f_0))
        in
        let p2 =
          Bignum_bigint.(
            (av0 * bv2) + (av1 * bv1) + (av2 * bv0) + (q0 * f_2) + (q1 * f_1)
            + (q2 * f_0))
        in
        let p10 = Bignum_bigint.(p1 land limb_mask) in
        let p1_shifted = Bignum_bigint.(shift_right p1 limb_bits) in
        let p110 = Bignum_bigint.(p1_shifted land limb_mask) in
        let p111 = Bignum_bigint.(shift_right p1_shifted limb_bits) in
        let _p11 = Bignum_bigint.(p110 + (p111 * two_to_limb)) in
        let c0 =
          Bignum_bigint.(
            shift_right (p0 + (p10 * two_to_limb) - r01) (Int.( * ) 2 limb_bits))
        in
        let c1 = Bignum_bigint.(shift_right (p2 - r2 + _p11 + c0) limb_bits) in
        let c1_00 = bit_slice c1 ~start:0 ~length:12 in
        let c1_12 = bit_slice c1 ~start:12 ~length:12 in
        let c1_24 = bit_slice c1 ~start:24 ~length:12 in
        let c1_36 = bit_slice c1 ~start:36 ~length:12 in
        let c1_48 = bit_slice c1 ~start:48 ~length:12 in
        let c1_60 = bit_slice c1 ~start:60 ~length:12 in
        let c1_72 = bit_slice c1 ~start:72 ~length:12 in
        let c1_84 = bit_slice c1 ~start:84 ~length:2 in
        let c1_86 = bit_slice c1 ~start:86 ~length:2 in
        let c1_88 = bit_slice c1 ~start:88 ~length:2 in
        let c1_90 = bit_slice c1 ~start:90 ~length:1 in
        let q2_bound = Bignum_bigint.(q2 + f2_bound) in
        let v =
          ( r01
          , r2
          , q0
          , q1
          , q2
          , q2_bound
          , p10
          , p110
          , p111
          , c0
          , c1_00
          , c1_12
          , c1_24
          , c1_36
          , c1_48
          , c1_60
          , c1_72
          , c1_84
          , c1_86
          , c1_88
          , c1_90 )
        in
        cache := Some v ;
        v
  in
  let w i =
    Circuit.exists Circuit.Field.typ ~compute:(fun () ->
        let ( r01
            , r2
            , q0
            , q1
            , q2
            , q2_bound
            , p10
            , p110
            , p111
            , c0
            , c1_00
            , c1_12
            , c1_24
            , c1_36
            , c1_48
            , c1_60
            , c1_72
            , c1_84
            , c1_86
            , c1_88
            , c1_90 ) =
          get_cached ()
        in
        let vals =
          [| r01
           ; r2
           ; q0
           ; q1
           ; q2
           ; q2_bound
           ; p10
           ; p110
           ; p111
           ; c0
           ; c1_00
           ; c1_12
           ; c1_24
           ; c1_36
           ; c1_48
           ; c1_60
           ; c1_72
           ; c1_84
           ; c1_86
           ; c1_88
           ; c1_90
          |]
        in
        bignum_to_field_const vals.(i) )
  in
  let r01 = w 0 in
  let r2 = w 1 in
  let q0 = w 2 in
  let q1 = w 3 in
  let q2 = w 4 in
  let q2_bound = w 5 in
  let p10 = w 6 in
  let p110 = w 7 in
  let p111 = w 8 in
  let c0 = w 9 in
  let c1_00 = w 10 in
  let c1_12 = w 11 in
  let c1_24 = w 12 in
  let c1_36 = w 13 in
  let c1_48 = w 14 in
  let c1_60 = w 15 in
  let c1_72 = w 16 in
  let c1_84 = w 17 in
  let c1_86 = w 18 in
  let c1_88 = w 19 in
  let c1_90 = w 20 in
  let a0, a1, a2 = a in
  let b0, b1, b2 = b in
  Circuit.assert_
    (ForeignFieldMul
       { left_input0 = a0
       ; left_input1 = a1
       ; left_input2 = a2
       ; right_input0 = b0
       ; right_input1 = b1
       ; right_input2 = b2
       ; remainder01 = r01
       ; remainder2 = r2
       ; quotient0 = q0
       ; quotient1 = q1
       ; quotient2 = q2
       ; quotient_hi_bound = q2_bound
       ; product1_lo = p10
       ; product1_hi_0 = p110
       ; product1_hi_1 = p111
       ; carry0 = c0
       ; carry1_0 = c1_00
       ; carry1_12 = c1_12
       ; carry1_24 = c1_24
       ; carry1_36 = c1_36
       ; carry1_48 = c1_48
       ; carry1_60 = c1_60
       ; carry1_72 = c1_72
       ; carry1_84 = c1_84
       ; carry1_86 = c1_86
       ; carry1_88 = c1_88
       ; carry1_90 = c1_90
       ; foreign_field_modulus2 = bignum_to_field_const f2
       ; neg_foreign_field_modulus0 = bignum_to_field_const f_0
       ; neg_foreign_field_modulus1 = bignum_to_field_const f_1
       ; neg_foreign_field_modulus2 = bignum_to_field_const f_2
       } ) ;
  multi_range_check (p10, p110, q2_bound) ;
  ((q0, q1, q2), r01, r2)

(** Multiply two Field3 values mod f, returning the result as Field3. *)
let mul (a : Field3.t) (b : Field3.t) ~(f : Bignum_bigint.t) : Field3.t =
  assert (Bignum_bigint.(f < shift_left one 259)) ;
  if Field3.is_constant a && Field3.is_constant b then
    let a_big = Field3.to_constant a in
    let b_big = Field3.to_constant b in
    let ab = Bignum_bigint.(a_big * b_big) in
    Field3.of_constant Bignum_bigint.(ab % f)
  else
    let q, r01, r2 = multiply_no_range_check a b ~f in
    multi_range_check q ;
    compact_multi_range_check r01 r2

(** Assert that x * y = xy mod f (compact field2 form). *)
type field2 = Circuit.Field.t * Circuit.Field.t

let assert_mul_field2 (x : Field3.t) (y : Field3.t) (xy : field2)
    ~(f : Bignum_bigint.t) : unit =
  let q, r01, r2 = multiply_no_range_check x y ~f in
  multi_range_check q ;
  let xy01, xy2 = xy in
  Circuit.assert_ (Equal (r01, xy01)) ;
  Circuit.assert_ (Equal (r2, xy2))

(** Assert that x * y = xy mod f. *)
let assert_mul (x : Field3.t) (y : Field3.t) (xy : Field3.t)
    ~(f : Bignum_bigint.t) : unit =
  if Field3.is_constant x && Field3.is_constant y && Field3.is_constant xy then (
    let x_big = Field3.to_constant x in
    let y_big = Field3.to_constant y in
    let xy_big = Field3.to_constant xy in
    let expected = Bignum_bigint.(x_big * y_big % f) in
    if not Bignum_bigint.(expected = xy_big) then
      failwith "assert_mul: incorrect multiplication result" )
  else
    let xy0, xy1, xy2 = xy in
    let q, r01, r2 = multiply_no_range_check x y ~f in
    multi_range_check q ;
    let xy01 =
      Circuit.Field.(xy0 + (xy1 * constant (bignum_to_field_const two_to_limb)))
    in
    Circuit.assert_ (Equal (r01, xy01)) ;
    Circuit.assert_ (Equal (r2, xy2))

(* ------------------------------------------------------------------ *)
(* Modular inverse                                                     *)
(* ------------------------------------------------------------------ *)

(** Extended Euclidean algorithm for modular inverse. *)
let bignum_mod_inverse (x : Bignum_bigint.t) ~(f : Bignum_bigint.t) :
    Bignum_bigint.t option =
  let rec gcd_ext a b =
    if Bignum_bigint.(b = zero) then (a, Bignum_bigint.one, Bignum_bigint.zero)
    else
      let q, r = Bignum_bigint.(a / b, a % b) in
      let g, s, t = gcd_ext b r in
      (g, t, Bignum_bigint.(s - (q * t)))
  in
  let x_mod = Bignum_bigint.(((x % f) + f) % f) in
  if Bignum_bigint.(x_mod = zero) then None
  else
    let g, s, _t = gcd_ext x_mod f in
    if Bignum_bigint.(g <> one) then None
    else Some Bignum_bigint.(((s % f) + f) % f)

(** Compute modular inverse x^{-1} mod f. *)
let inv (x : Field3.t) ~(f : Bignum_bigint.t) : Field3.t =
  if Field3.is_constant x then
    let x_big = Field3.to_constant x in
    match bignum_mod_inverse x_big ~f with
    | Some x_inv ->
        Field3.of_constant x_inv
    | None ->
        failwith "inv: inverse does not exist"
  else
    let x0, x1, x2 = x in
    let w i =
      Circuit.exists Circuit.Field.typ ~compute:(fun () ->
          let xv0 = field_const_to_bignum (Circuit.As_prover.read_var x0) in
          let xv1 = field_const_to_bignum (Circuit.As_prover.read_var x1) in
          let xv2 = field_const_to_bignum (Circuit.As_prover.read_var x2) in
          let x_big = Field3.Constant.combine (xv0, xv1, xv2) in
          let x_inv =
            match bignum_mod_inverse x_big ~f with
            | Some v ->
                v
            | None ->
                Bignum_bigint.zero
          in
          let l0, l1, l2 = Field3.Constant.split x_inv in
          bignum_to_field_const [| l0; l1; l2 |].(i) )
    in
    let v0 = w 0 in
    let v1 = w 1 in
    let v2 = w 2 in
    let x_inv = (v0, v1, v2) in
    multi_range_check x_inv ;
    let _, _, x_inv2 = x_inv in
    let x_inv2_bound = weak_bound x_inv2 ~f in
    let one_field2 : field2 =
      ( Circuit.Field.(constant Constant.one)
      , Circuit.Field.(constant Constant.zero) )
    in
    assert_mul_field2 x x_inv one_field2 ~f ;
    multi_range_check
      ( x_inv2_bound
      , Circuit.Field.constant Circuit.Field.Constant.zero
      , Circuit.Field.constant Circuit.Field.Constant.zero ) ;
    x_inv

(** Compute x / y mod f. *)
let div (x : Field3.t) (y : Field3.t) ~(f : Bignum_bigint.t) : Field3.t =
  let y_inv = inv y ~f in
  mul x y_inv ~f

(* ------------------------------------------------------------------ *)
(* Utility functions                                                   *)
(* ------------------------------------------------------------------ *)

(** Assert x < bound by computing (bound-1) - x and range-checking. *)
let assert_less_than (x : Field3.t) ~(bound : Bignum_bigint.t) : unit =
  if Field3.is_constant x then (
    let x_big = Field3.to_constant x in
    if Bignum_bigint.(x_big >= bound) then
      failwith "assert_less_than: x >= bound" )
  else if Bignum_bigint.(bound > zero) then
    ignore (negate x ~f:Bignum_bigint.(bound - one) : Field3.t)
  else failwith "assert_less_than: bound must be positive"

(** Assert two Field3 values are equal limb-wise. *)
let assert_equal ((x0, x1, x2) : Field3.t) ((y0, y1, y2) : Field3.t) : unit =
  if Field3.is_constant (x0, x1, x2) && Field3.is_constant (y0, y1, y2) then (
    let x_big = Field3.to_constant (x0, x1, x2) in
    let y_big = Field3.to_constant (y0, y1, y2) in
    if not Bignum_bigint.(x_big = y_big) then failwith "assert_equal: x != y" )
  else (
    Circuit.assert_ (Equal (x0, y0)) ;
    Circuit.assert_ (Equal (x1, y1)) ;
    Circuit.assert_ (Equal (x2, y2)) )

(** Boolean AND via field multiplication. *)
let bool_and (a : Circuit.Boolean.var) (b : Circuit.Boolean.var) :
    Circuit.Boolean.var =
  let r =
    Circuit.exists Circuit.Field.typ ~compute:(fun () ->
        let av = Circuit.As_prover.read Circuit.Boolean.typ a in
        let bv = Circuit.As_prover.read Circuit.Boolean.typ b in
        if av && bv then Circuit.Field.Constant.one
        else Circuit.Field.Constant.zero )
  in
  Circuit.assert_ (R1CS ((a :> Circuit.Field.t), (b :> Circuit.Field.t), r)) ;
  Circuit.Boolean.Unsafe.of_cvar r

(** Check if a circuit field variable equals a bignum constant.
    Matches o1js Field.equals(). *)
let field_var_equal (x : Circuit.Field.t) (y : Circuit.Field.t) :
    Circuit.Boolean.var =
  match (Circuit.Field.to_constant x, Circuit.Field.to_constant y) with
  | Some cx, Some cy ->
      if Circuit.Field.Constant.(equal cx cy) then Circuit.Boolean.true_
      else Circuit.Boolean.false_
  | _ ->
      let diff = seal Circuit.Field.(x - y) in
      let r =
        Circuit.exists Circuit.Boolean.typ ~compute:(fun () ->
            let dv = Circuit.As_prover.read_var diff in
            Circuit.Field.Constant.(equal dv zero) )
      in
      let z =
        Circuit.exists Circuit.Field.typ ~compute:(fun () ->
            let dv = Circuit.As_prover.read_var diff in
            if Circuit.Field.Constant.(equal dv zero) then
              Circuit.Field.Constant.zero
            else Circuit.Field.Constant.(inv dv) )
      in
      (* b * diff = 0 (if b=true then diff must be 0) *)
      Circuit.assert_ (R1CS ((r :> Circuit.Field.t), diff, Circuit.Field.zero)) ;
      (* z * diff = 1 - b (if diff != 0 then b must be false) *)
      Circuit.assert_
        (R1CS (z, diff, Circuit.Field.(constant Constant.one - (r :> t)))) ;
      r

let field_equal (x : Circuit.Field.t) (c : Bignum_bigint.t) :
    Circuit.Boolean.var =
  field_var_equal x (Circuit.Field.constant (bignum_to_field_const c))

(* ------------------------------------------------------------------ *)
(* Sum accumulator                                                     *)
(* ------------------------------------------------------------------ *)

(** Lazy accumulator for chaining additions/subtractions.
    Operations are collected and materialized at once when [finish]
    is called, matching o1js Sum API. *)
module Sum = struct
  type t =
    { summands : Field3.t list
    ; ops : sign list
    ; mutable result : Field3.t option
    ; chained : bool
          (** When true, finish_for_mul_input skips the final Zero gate,
            allowing the FFAdd to chain directly into the next FFMul. *)
    }

  let of_field3 (x : Field3.t) : t =
    { summands = [ x ]; ops = []; result = None; chained = false }

  let add (t : t) (y : Field3.t) : t =
    assert (Option.is_none t.result) ;
    { t with summands = t.summands @ [ y ]; ops = t.ops @ [ Add ] }

  let sub (t : t) (y : Field3.t) : t =
    assert (Option.is_none t.result) ;
    { t with summands = t.summands @ [ y ]; ops = t.ops @ [ Sub ] }

  let length (t : t) : int = List.length t.summands

  let is_constant (t : t) : bool = List.for_all t.summands ~f:Field3.is_constant

  (** Materialize the accumulated sum, producing all ForeignFieldAdd
      gates at once. *)
  let finish (t : t) ~(f : Bignum_bigint.t) : Field3.t =
    assert (Option.is_none t.result) ;
    if List.length t.ops = 0 then (
      let r = List.hd_exn t.summands in
      t.result <- Some r ;
      r )
    else
      let r = sum t.summands t.ops ~f in
      t.result <- Some r ;
      r

  (** Simple finish: FFAdd chain + Zero gate only.
      No range check, no generic-gate low-limb constraints.
      Matches nori's Sum.finish() used for the xy (result) operand
      in assertMul. *)
  let finish_simple (t : t) ~(f : Bignum_bigint.t) : Field3.t =
    assert (Option.is_none t.result) ;
    if List.length t.ops = 0 then (
      let r = List.hd_exn t.summands in
      t.result <- Some r ;
      r )
    else if List.for_all t.summands ~f:Field3.is_constant then (
      let x_bigs = List.map t.summands ~f:Field3.to_constant in
      let result =
        List.fold2_exn (List.tl_exn x_bigs) t.ops ~init:(List.hd_exn x_bigs)
          ~f:(fun acc xi sign_i ->
            Bignum_bigint.(acc + (sign_to_bigint sign_i * xi)) )
      in
      let result_mod = Bignum_bigint.(((result % f) + f) % f) in
      let r = Field3.of_constant result_mod in
      t.result <- Some r ;
      r )
    else
      let xs =
        List.map t.summands ~f:(fun (l0, l1, l2) ->
            (to_var l0, to_var l1, to_var l2) )
      in
      let result = ref (List.hd_exn xs) in
      List.iter2_exn (List.tl_exn xs) t.ops ~f:(fun xi sign_i ->
          let r, _overflow = single_add !result xi ~sign:sign_i ~f in
          result := r ) ;
      let r0, r1, r2 = !result in
      Circuit.assert_
        (Raw { kind = Zero; values = [| r0; r1; r2 |]; coeffs = [||] }) ;
      t.result <- Some !result ;
      !result

  (** Materialize the sum for use as a multiplication input.
      Produces ForeignFieldAdd gates + Zero gate + Generic gates for
      low-limb tracking, but skips the multi_range_check.
      Matches o1js finishForMulInput — uses Generic gates to constrain
      the lowest limb individually, since FFAdd only constrains the
      low+middle limbs together. *)
  let finish_for_mul_input (t : t) ~(f : Bignum_bigint.t) : Field3.t =
    assert (Option.is_none t.result) ;
    if List.length t.ops = 0 then (
      let r = List.hd_exn t.summands in
      t.result <- Some r ;
      r )
    else
      let xs = t.summands in
      let signs = t.ops in
      if List.for_all xs ~f:Field3.is_constant then (
        let x_bigs = List.map xs ~f:Field3.to_constant in
        let result =
          List.fold2_exn (List.tl_exn x_bigs) signs ~init:(List.hd_exn x_bigs)
            ~f:(fun acc xi sign_i ->
              Bignum_bigint.(acc + (sign_to_bigint sign_i * xi)) )
        in
        let result_mod = Bignum_bigint.(((result % f) + f) % f) in
        let r = Field3.of_constant result_mod in
        t.result <- Some r ;
        r )
      else
        let xs =
          List.map xs ~f:(fun (l0, l1, l2) ->
              (to_var l0, to_var l1, to_var l2) )
        in
        let f0 = Bignum_bigint.(f land limb_mask) in
        let n = List.length signs in
        (* Generic gates for low limbs — mirrors o1js finishForMulInput *)
        let x0 =
          ref
            (let l0, _, _ = List.hd_exn xs in
             l0 )
        in
        let x0s = Array.create ~len:n Circuit.Field.zero in
        let overflows = Array.create ~len:n Circuit.Field.zero in
        List.iteri (List.tl_exn xs) ~f:(fun i xi ->
            let xi0, _, _ = xi in
            let sign_i = List.nth_exn signs i in
            let sign_bi = sign_to_bigint sign_i in
            let carry, overflow =
              let c =
                Circuit.exists
                  (Circuit.Typ.tuple2 Circuit.Field.typ Circuit.Field.typ)
                  ~compute:(fun () ->
                    let x0v =
                      field_const_to_bignum (Circuit.As_prover.read_var !x0)
                    in
                    let xi_full =
                      let l0, l1, l2 = xi in
                      let rl v =
                        field_const_to_bignum (Circuit.As_prover.read_var v)
                      in
                      Bignum_bigint.(
                        rl l0 + (rl l1 * two_to_limb) + (rl l2 * two_to_2limb))
                    in
                    let full =
                      Bignum_bigint.(
                        x0v
                        + sign_bi
                          * field_const_to_bignum
                              (Circuit.As_prover.read_var xi0))
                    in
                    let overflow =
                      if
                        Bignum_bigint.(sign_bi > zero)
                        && Bignum_bigint.(x0v + (sign_bi * xi_full) >= f)
                      then Bignum_bigint.one
                      else if
                        Bignum_bigint.(sign_bi < zero)
                        && Bignum_bigint.(x0v + (sign_bi * xi_full) < zero)
                      then Bignum_bigint.(neg one)
                      else Bignum_bigint.zero
                    in
                    let x0_new = Bignum_bigint.(full - (overflow * f0)) in
                    let carry = Bignum_bigint.(shift_right x0_new limb_bits) in
                    (bignum_to_field_const carry, bignum_to_field_const overflow) )
              in
              (fst c, snd c)
            in
            overflows.(i) <- overflow ;
            (* Constrain carry to {0, 1, -1}: carry*(carry²-1) = 0.
               Two R1CS half-generics that enter the PCS pairing queue:
               1. carry*(carry-1) = z
               2. z*(carry+1) = 0
               These pair with OTHER half-generics (e.g. weakBound),
               matching nori's pairing behavior. *)
            let z =
              Circuit.exists Circuit.Field.typ ~compute:(fun () ->
                  let c = Circuit.As_prover.read_var carry in
                  Circuit.Field.Constant.(c * (c - one)) )
            in
            Circuit.assert_
              (R1CS
                 ( carry
                 , Circuit.Field.(carry - constant Circuit.Field.Constant.one)
                 , z ) ) ;
            Circuit.assert_
              (R1CS
                 ( z
                 , Circuit.Field.(carry + constant Circuit.Field.Constant.one)
                 , Circuit.Field.zero ) ) ;
            (* x0 <- x0 + sign*xi0 - overflow*f0 - carry*2^l *)
            let sign_field = bignum_to_field_const sign_bi in
            let f0_field = bignum_to_field_const f0 in
            let two_l_field = bignum_to_field_const two_to_limb in
            let x0_expr =
              Circuit.Field.(
                !x0
                + (xi0 * constant sign_field)
                - (overflow * constant f0_field)
                - (carry * constant two_l_field))
            in
            x0 := to_var x0_expr ;
            x0s.(i) <- !x0 ) ;
        (* ForeignFieldAdd chain — assert equality via wiring.
           The assertEqual calls produce half-generics that pair with
           each other and with the toVar half-generic above. *)
        let result = ref (List.hd_exn xs) in
        List.iteri (List.tl_exn xs) ~f:(fun i xi ->
            let sign_i = List.nth_exn signs i in
            let r, overflow = single_add !result xi ~sign:sign_i ~f in
            let r0, _, _ = r in
            Circuit.assert_ (Equal (r0, x0s.(i))) ;
            Circuit.assert_ (Equal (overflow, overflows.(i))) ;
            result := r ) ;
        ( if not t.chained then
          let r0, r1, r2 = !result in
          Circuit.assert_
            (Raw { kind = Zero; values = [| r0; r1; r2 |]; coeffs = [||] }) ) ;
        t.result <- Some !result ;
        !result
end

(** Input type for assert_mul_sum: either a Sum accumulator or a
    plain Field3 value. *)
type mul_input = Sum_input of Sum.t | Field3_input of Field3.t

(** Assert x * y = xy (mod f), accepting Sum accumulators as inputs.
    Finishes pending sums before performing the multiplication check.

    Note: nori uses finishForMulInput which replaces the range check
    with generic-gate low-limb constraints. Our Sum.finish uses the
    standard range check approach. Matching nori's exact gate sequence
    requires implementing the generic-gate low-limb tracking from o1js. *)

(** Convert a Field3 to variables if not already pure variables.
    Matches nori's toVariable step in assertMul which ensures
    finished sum values don't break the gate chain. *)
let to_var_field3 ((l0, l1, l2) : Field3.t) : Field3.t =
  (to_var l0, to_var l1, to_var l2)

let assert_mul_sum (x : mul_input) (y : mul_input) (xy : mul_input)
    ~(f : Bignum_bigint.t) : unit =
  let finish_for_mul = function
    | Sum_input s ->
        Sum.finish_for_mul_input s ~f
    | Field3_input f3 ->
        f3
  in
  let finish_simple = function
    | Sum_input s ->
        Sum.finish_simple s ~f
    | Field3_input f3 ->
        f3
  in
  let finish_chained = function
    | Sum_input s ->
        Sum.finish_for_mul_input { s with chained = true } ~f
    | Field3_input f3 ->
        f3
  in
  (* Match nori's assertMul order:
     1. finish b (y), finish c (xy)
     2. toVariable on b and c (if not all constant)
     3. finish a (x, chained) → assertMul *)
  let y_val = finish_for_mul y in
  let xy_val = finish_simple xy in
  let all_constant =
    (match x with
    | Sum_input s ->
        Sum.is_constant s
    | Field3_input f3 ->
        Field3.is_constant f3)
    && Field3.is_constant y_val && Field3.is_constant xy_val
  in
  let y_val, xy_val =
    if all_constant then (y_val, xy_val)
    else (to_var_field3 y_val, to_var_field3 xy_val)
  in
  let x_val = finish_chained x in
  assert_mul x_val y_val xy_val ~f

(* ------------------------------------------------------------------ *)
(* FpU / FpA: Typed foreign field hierarchy                            *)
(*                                                                     *)
(* Mirrors o1js foreign-field.ts:                                      *)
(*   ForeignField (base)     — add, sub, neg, sum                      *)
(*     └ UnreducedForeignField  — check = MRC                          *)
(*     └ ForeignFieldWithMul    — mul, inv, div                        *)
(*         └ AlmostForeignField — check = MRC + weakBound              *)
(*         └ CanonicalForeignField — check = MRC + canonical           *)
(*                                                                     *)
(* Return types match o1js exactly:                                    *)
(*   add/sub → Unreduced,  neg → AlmostReduced                        *)
(*   mul → Unreduced,  inv/div → AlmostReduced                        *)
(* ------------------------------------------------------------------ *)

(** Unreduced foreign field element. Limbs are range-checked (< 2^88)
    but the high limb is NOT weakly bounded.

    Mirrors o1js UnreducedForeignField.
    Has add/sub (returns FpU), but NOT mul/inv/div.
    check = multiRangeCheck only. *)
module FpU : sig
  type t = private Field3.t

  val to_field3 : t -> Field3.t

  val of_field3_unsafe : Field3.t -> t

  (** FpU + FpU → FpU. Emits ForeignFieldAdd + indirectMRC. *)
  val add : t -> t -> f:Bignum_bigint.t -> t

  (** FpU - FpU → FpU. Emits ForeignFieldAdd + indirectMRC. *)
  val sub : t -> t -> f:Bignum_bigint.t -> t

  (** -FpU → FpU. Emits ForeignFieldAdd + indirectMRC.
      Note: in o1js, neg returns AlmostReduced. We return FpU here
      because FpA is not yet defined. Callers that need FpA should
      use FpA.neg instead. *)
  val neg : t -> f:Bignum_bigint.t -> t

  val typ : (t, Field3.Constant.t) Circuit.Typ.t
end = struct
  type t = Field3.t

  let to_field3 (x : t) = x

  let of_field3_unsafe (x : Field3.t) : t = x

  let add (x : t) (y : t) ~(f : Bignum_bigint.t) : t = add x y ~f

  let sub (x : t) (y : t) ~(f : Bignum_bigint.t) : t = sub x y ~f

  let neg (x : t) ~(f : Bignum_bigint.t) : t = negate x ~f

  let typ : (t, Field3.Constant.t) Circuit.Typ.t = Field3.typ
end

(** Almost-reduced foreign field element. Limbs are range-checked (< 2^88)
    AND the high limb is weakly bounded.

    Mirrors o1js AlmostForeignField.
    Has add/sub (returns FpU), neg (returns FpA),
    mul (returns FpU), inv/div (returns FpA).
    check = multiRangeCheck + weakBound. *)
module FpA : sig
  type t = private Field3.t

  val to_field3 : t -> Field3.t

  val to_fpu : t -> FpU.t

  val of_field3_unsafe : Field3.t -> t

  val of_constant : Bignum_bigint.t -> t

  (** FpA + FpA → FpU. Emits ForeignFieldAdd + indirectMRC. *)
  val add : t -> t -> f:Bignum_bigint.t -> FpU.t

  (** FpA - FpA → FpU. Emits ForeignFieldAdd + indirectMRC. *)
  val sub : t -> t -> f:Bignum_bigint.t -> FpU.t

  (** -FpA → FpA. Negation proves result < f, so it's AlmostReduced. *)
  val neg : t -> f:Bignum_bigint.t -> t

  (** FpA * FpA → FpU. Emits ForeignFieldMul + range checks. *)
  val mul : t -> t -> f:Bignum_bigint.t -> FpU.t

  (** 1/FpA → FpA. Witnesses inverse, constrains via assertMul. *)
  val inv : t -> f:Bignum_bigint.t -> t

  (** FpA / FpA → FpA. *)
  val div : t -> t -> f:Bignum_bigint.t -> t

  (** Convert FpU values to FpA by adding weakBound check. *)
  val assert_almost_reduced :
    FpU.t list -> f:Bignum_bigint.t -> ?skip_mrc:bool -> unit -> t list

  val typ : f:Bignum_bigint.t -> (t, Field3.Constant.t) Circuit.Typ.t
end = struct
  type t = Field3.t

  let to_field3 (x : t) : Field3.t = x

  let to_fpu (x : t) : FpU.t = FpU.of_field3_unsafe x

  let of_field3_unsafe (x : Field3.t) : t = x

  let of_constant (x : Bignum_bigint.t) : t = Field3.of_constant x

  (* add/sub return FpU — matching o1js ForeignField.add/sub → Unreduced *)
  let add (x : t) (y : t) ~(f : Bignum_bigint.t) : FpU.t =
    FpU.of_field3_unsafe (add x y ~f)

  let sub (x : t) (y : t) ~(f : Bignum_bigint.t) : FpU.t =
    FpU.of_field3_unsafe (sub x y ~f)

  (* neg returns FpA — matching o1js ForeignField.neg → AlmostReduced
     because negation proves r = f - x >= 0, so r < f *)
  let neg (x : t) ~(f : Bignum_bigint.t) : t = negate x ~f

  (* mul returns FpU — matching o1js ForeignFieldWithMul.mul → Unreduced *)
  let mul (x : t) (y : t) ~(f : Bignum_bigint.t) : FpU.t =
    FpU.of_field3_unsafe (mul x y ~f)

  (* inv/div return FpA — matching o1js → AlmostReduced *)
  let inv (x : t) ~(f : Bignum_bigint.t) : t = inv x ~f

  let div (x : t) (y : t) ~(f : Bignum_bigint.t) : t = div x y ~f

  let assert_almost_reduced (xs : FpU.t list) ~(f : Bignum_bigint.t)
      ?(skip_mrc = false) () : t list =
    let xs_raw = List.map xs ~f:FpU.to_field3 in
    assert_almost_reduced xs_raw ~f ~skip_mrc ;
    List.map xs_raw ~f:of_field3_unsafe

  let typ ~(f : Bignum_bigint.t) : (t, Field3.Constant.t) Circuit.Typ.t =
    let (Circuit.Typ.Typ base) = Field3.typ in
    Circuit.Typ.Typ
      { base with
        check =
          (fun (l0, l1, l2) ->
            Circuit.make_checked (fun () ->
                multi_range_check (l0, l1, l2) ;
                let bound = weak_bound l2 ~f in
                multi_range_check
                  ( bound
                  , Circuit.Field.constant Circuit.Field.Constant.zero
                  , Circuit.Field.constant Circuit.Field.Constant.zero ) ) )
      }
end

(** Canonical foreign field element.  Limbs are range-checked (< 2^88)
    AND the full value is proven < f.

    Mirrors o1js CanonicalForeignField.
    check = multiRangeCheck + assertCanonical (assertLessThan(f)). *)
module FpC = struct
  type t = private FpA.t

  let of_fpa_unsafe (x : FpA.t) : t = (Obj.magic x : t)

  let to_field3 (x : t) : Field3.t = (x :> Field3.t)

  let to_fpa (x : t) : FpA.t = (x :> FpA.t)

  let of_constant (x : Bignum_bigint.t) : t = of_fpa_unsafe (FpA.of_constant x)

  let mul ~f (x : t) (y : t) : FpU.t = FpA.mul ~f (x :> FpA.t) (y :> FpA.t)

  (** Assert a value is canonical (< f) and return as FpC. *)
  let assert_canonical_ (x : FpU.t) ~(f : Bignum_bigint.t) : t =
    assert_less_than (FpU.to_field3 x) ~bound:f ;
    of_fpa_unsafe (FpA.of_field3_unsafe (FpU.to_field3 x))

  let assert_canonical (x : FpA.t) ~(f : Bignum_bigint.t) : t =
    assert_less_than (FpA.to_field3 x) ~bound:f ;
    of_fpa_unsafe x

  let typ ~(f : Bignum_bigint.t) : (t, Field3.Constant.t) Circuit.Typ.t =
    let (Circuit.Typ.Typ base) = (FpA.typ ~f : (FpA.t, _) Circuit.Typ.t) in
    Circuit.Typ.Typ
      { base with
        check =
          (fun x ->
            Circuit.make_checked (fun () ->
                multi_range_check (FpA.to_field3 x) ;
                assert_less_than (FpA.to_field3 x) ~bound:f ) )
      }
    |> Circuit.Typ.transport_var
         ~there:(fun x -> to_fpa x)
         ~back:(fun x -> of_fpa_unsafe x)
end
