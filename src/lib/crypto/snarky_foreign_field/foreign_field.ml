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
    Circuit.Bigint.(to_field (of_bignum_bigint Bignum_bigint.((x % p + p) % p)))
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
        ((l0, l1, l2) :
          Bignum_bigint.t * Bignum_bigint.t * Bignum_bigint.t ) :
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
      ((l0, l1, l2) :
        Circuit.Field.t * Circuit.Field.t * Circuit.Field.t ) : t =
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
       { v0; v0p0; v0p1; v0p2; v0p3; v0p4; v0p5
       ; v0c0; v0c1; v0c2; v0c3; v0c4; v0c5; v0c6; v0c7
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
       { v2 = z; v12 = yz; v2c0; v2p0; v2p1; v2p2; v2p3
       ; v2c1; v2c2; v2c3; v2c4; v2c5; v2c6; v2c7; v2c8
       ; v2c9; v2c10; v2c11
       ; v0p0 = x76; v0p1 = x64; v1p0 = y76; v1p1 = y64
       ; v2c12; v2c13; v2c14; v2c15; v2c16; v2c17; v2c18; v2c19
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
        field_const_to_bignum
          (Option.value_exn (Circuit.Field.to_constant v))
      in
      if Bignum_bigint.(v_bignum >= two_to_limb) then
        failwith (sprintf "multi_range_check: %s >= 2^%d" name limb_bits)
    in
    check x "x" ; check y "y" ; check z "z" )
  else
    let x = to_var x in
    let y = to_var y in
    let z = to_var z in
    let zero =
      to_var (Circuit.Field.constant Circuit.Field.Constant.zero)
    in
    let x64, x76 = range_check0 x ~compact:false in
    let y64, y76 = range_check0 y ~compact:false in
    range_check1 ~x64 ~x76 ~y64 ~y76 ~z ~yz:zero

(** Range check a compact 2-limb value [xy] (176 bits) and a single
    limb [z] (88 bits). Returns the three individual limbs. *)
let compact_multi_range_check (xy : Circuit.Field.t) (z : Circuit.Field.t) :
    Field3.t =
  if
    Option.is_some (Circuit.Field.to_constant xy)
    && Option.is_some (Circuit.Field.to_constant z)
  then
    let xy_bignum =
      field_const_to_bignum
        (Option.value_exn (Circuit.Field.to_constant xy))
    in
    let z_bignum =
      field_const_to_bignum
        (Option.value_exn (Circuit.Field.to_constant z))
    in
    if Bignum_bigint.(xy_bignum >= two_to_2limb) then
      failwith "compact_multi_range_check: xy >= 2^176" ;
    if Bignum_bigint.(z_bignum >= two_to_limb) then
      failwith "compact_multi_range_check: z >= 2^88" ;
    let x = Bignum_bigint.(xy_bignum land limb_mask) in
    let y = Bignum_bigint.(shift_right xy_bignum limb_bits) in
    ( Circuit.Field.constant (bignum_to_field_const x)
    , Circuit.Field.constant (bignum_to_field_const y)
    , z )
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
          bignum_to_field_const
            Bignum_bigint.(shift_right xy_bignum limb_bits) )
    in
    let z64, z76 = range_check0 z ~compact:false in
    let x64, x76 = range_check0 x ~compact:true in
    range_check1 ~x64:z64 ~x76:z76 ~y64:x64 ~y76:x76 ~z:y ~yz:xy ;
    (x, y, z)
