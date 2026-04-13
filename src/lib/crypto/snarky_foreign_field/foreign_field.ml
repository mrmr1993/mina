(** Foreign field arithmetic over 3-limb (88-bit) representations.

    Implements Field3 — a representation of field elements as three 88-bit
    limbs suitable for 254-bit foreign field moduli (e.g. BN254 Fp/Fr).

    Adapted from feature/groth16-and-kzg-foreign-field branch. *)

open Core_kernel
module Bignum_bigint = Bigint
module Circuit = Kimchi_pasta_snarky_backend.Step_impl

(* ------------------------------------------------------------------ *)
(* Circuit abort infrastructure for gate comparison debugging          *)
(* ------------------------------------------------------------------ *)

exception Circuit_abort

let abort_enabled = ref false

let enable_abort () = abort_enabled := true

let check_abort tag =
  if !abort_enabled then
    match Stdlib.Sys.getenv_opt "ABORT_SCALE" with
    | Some s when String.equal s tag ->
        raise Circuit_abort
    | _ ->
        ()

(* ------------------------------------------------------------------ *)
(* Constants                                                           *)
(* ------------------------------------------------------------------ *)

let limb_bits = 88

let two_to_limb = Bignum_bigint.(pow (of_int 2) (of_int limb_bits))

let limb_mask = Bignum_bigint.(two_to_limb - one)

let two_to_2limb = Bignum_bigint.(two_to_limb * two_to_limb)

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

(* ------------------------------------------------------------------ *)
(* Seal and to_var                                                     *)
(* ------------------------------------------------------------------ *)

(** Seal a circuit variable — materializes compound Cvars into fresh
    variables. *)
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

let seal_field = seal

let to_var_field = to_var

(* ------------------------------------------------------------------ *)
(* Limb: a single 88-bit limb with cached bigint                       *)
(* ------------------------------------------------------------------ *)

module Limb : sig
  (** An 88-bit limb of a foreign field element.  Carries the circuit
      variable AND the corresponding [Bignum_bigint.t] value as auxiliary
      data.  In prover mode the bigint is always available; during
      constraint-system-only passes it is [None] and falls back to
      [field_const_to_bignum].

      Use [Circuit.exists Limb.typ ~compute] to witness,
      [Circuit.As_prover.read Limb.typ] to read in prover context. *)
  type t

  (** Snarky Typ whose value is [Bignum_bigint.t].  The auxiliary channel
      carries the bigint through to the var, so [exists typ ~compute]
      produces a [t] with the bigint already cached. *)
  val typ : (t, Bignum_bigint.t) Circuit.Typ.t

  (** Build a constant limb.  Uses [Circuit.constant typ]. *)
  val of_constant : Bignum_bigint.t -> t

  (** Extract the [Circuit.Field.t] variable for use in gates. *)
  val to_field : t -> Circuit.Field.t

  (** Add a constant bigint to a limb, producing a new limb whose
      Cvar is [x + constant(c)] and whose cached bigint is [b + c]. *)
  val add_const : t -> Bignum_bigint.t -> t

  (** Seal a compound Cvar into a simple variable, preserving the
      cached bigint.  Uses [seal] (Equal argument order: old, new). *)
  val seal : t -> t

  (** Seal via [to_var] (Equal argument order: new, old). *)
  val to_var : t -> t

  (** Wrap a raw [Circuit.Field.t] as a limb with no cached bigint.
      Use when the variable was witnessed outside [Limb.typ]. *)
  val of_var : Circuit.Field.t -> t

  (** If the limb is a constant, return its bigint value. *)
  val to_constant : t -> Bignum_bigint.t option
end = struct
  type t = { var : Circuit.Field.t ; bigint : Bignum_bigint.t option }

  let typ : (t, Bignum_bigint.t) Circuit.Typ.t =
    Circuit.Typ.Typ
      { size_in_field_elements = 1
      ; constraint_system_auxiliary = (fun () -> None)
      ; value_to_fields =
          (fun b -> ([| bignum_to_field_const b |], Some b))
      ; value_of_fields =
          (fun (fields, aux) ->
            match aux with
            | Some b -> b
            | None -> field_const_to_bignum fields.(0) )
      ; var_to_fields = (fun t -> ([| t.var |], t.bigint))
      ; var_of_fields =
          (fun (fields, bigint) -> { var = fields.(0) ; bigint })
      ; check = (fun _ -> Circuit.make_checked (fun () -> ()))
      }

  let of_constant b = Circuit.constant typ b

  let to_field t = t.var

  let add_const t c =
    { var = Circuit.Field.(t.var + constant (bignum_to_field_const c))
    ; bigint = Option.map t.bigint ~f:(fun b -> Bignum_bigint.(b + c))
    }

  let seal t = { t with var = seal_field t.var }

  let to_var t = { t with var = to_var_field t.var }

  let of_var v = { var = v ; bigint = None }

  let to_constant t =
    Option.bind (Circuit.Field.to_constant t.var) ~f:(fun _ -> t.bigint)
end

let witness_bit_slice (v : Limb.t) ~(start : int) ~(length : int) :
    Circuit.Field.t =
  Circuit.exists Circuit.Field.typ ~compute:(fun () ->
      let v_bignum = Circuit.As_prover.read Limb.typ v in
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
      l0 + shift_left l1 limb_bits + shift_left l2 (Int.( * ) 2 limb_bits)

    let of_bigint (x : Bignum_bigint.t) : t = x

    let zero : t = Bignum_bigint.zero

    let one : t = Bignum_bigint.one

    let mod_ (x : t) ~(f : Bignum_bigint.t) : t = Bignum_bigint.(x % f)
  end

  type t = Limb.t * Limb.t * Limb.t

  (** Extract the three [Circuit.Field.t] variables. *)
  let vars ((l0, l1, l2) : t) :
      Circuit.Field.t * Circuit.Field.t * Circuit.Field.t =
    (Limb.to_field l0, Limb.to_field l1, Limb.to_field l2)

  let of_constant (x : Constant.t) : t =
    let l0, l1, l2 = Constant.split x in
    (Limb.of_constant l0, Limb.of_constant l1, Limb.of_constant l2)

  let of_limbs ((l0, l1, l2) : Limb.t * Limb.t * Limb.t) : t = (l0, l1, l2)

  let limbs ((l0, l1, l2) : t) :
      Circuit.Field.t * Circuit.Field.t * Circuit.Field.t =
    (Limb.to_field l0, Limb.to_field l1, Limb.to_field l2)

  let is_constant ((l0, l1, l2) : t) : bool =
    Option.is_some (Limb.to_constant l0)
    && Option.is_some (Limb.to_constant l1)
    && Option.is_some (Limb.to_constant l2)

  let to_constant_opt ((l0, l1, l2) : t) : Constant.t option =
    match (Limb.to_constant l0, Limb.to_constant l1, Limb.to_constant l2) with
    | Some v0, Some v1, Some v2 ->
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

  (** Snarky Typ for Field3 values. Built from [Limb.typ] composition.
      Witnessing via [exists typ ~compute] automatically applies
      multi_range_check to ensure each limb is in [0, 2^88). *)
  let typ : (t, Constant.t) Circuit.Typ.t =
    Circuit.Typ.(
      transport
        (tuple3 Limb.typ Limb.typ Limb.typ)
        ~there:Constant.split ~back:Constant.combine)
    |> Circuit.Typ.transport_var ~there:Fun.id ~back:Fun.id
    (* Wrap check to apply multi_range_check *)
    |> fun (Circuit.Typ.Typ base) ->
    Circuit.Typ.Typ
      { base with
        check =
          (fun (l0, l1, l2) ->
            Circuit.make_checked (fun () -> !check_ref (l0, l1, l2)) )
      }
end

(* ------------------------------------------------------------------ *)
(* Range check gadgets                                                 *)
(* ------------------------------------------------------------------ *)

(** Range check a single 88-bit limb using RangeCheck0 gate.
    Returns the top two 12-bit plookup chunks (bits 64-87). *)
let range_check0 (v0 : Limb.t) ~(compact : bool) :
    Circuit.Field.t * Circuit.Field.t =
  let ws = witness_bit_slice v0 in
  let v0 = Limb.to_field v0 in
  let v0c0 = ws ~start:14 ~length:2 in
  let v0c1 = ws ~start:12 ~length:2 in
  let v0c2 = ws ~start:10 ~length:2 in
  let v0c3 = ws ~start:8 ~length:2 in
  let v0c4 = ws ~start:6 ~length:2 in
  let v0c5 = ws ~start:4 ~length:2 in
  let v0c6 = ws ~start:2 ~length:2 in
  let v0c7 = ws ~start:0 ~length:2 in
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
    ~(y64 : Circuit.Field.t) ~(y76 : Circuit.Field.t) ~(z : Limb.t)
    ~(yz : Circuit.Field.t) : unit =
  let ws = witness_bit_slice z in
  let z = Limb.to_field z in
  (* Current row: MSB-first crumbs and plookups, matching o1js rangeCheck1Helper *)
  let v2c0 = ws ~start:86 ~length:2 in
  let v2p0 = ws ~start:74 ~length:12 in
  let v2p1 = ws ~start:62 ~length:12 in
  let v2p2 = ws ~start:50 ~length:12 in
  let v2p3 = ws ~start:38 ~length:12 in
  let v2c1 = ws ~start:36 ~length:2 in
  let v2c2 = ws ~start:34 ~length:2 in
  let v2c3 = ws ~start:32 ~length:2 in
  let v2c4 = ws ~start:30 ~length:2 in
  let v2c5 = ws ~start:28 ~length:2 in
  let v2c6 = ws ~start:26 ~length:2 in
  let v2c7 = ws ~start:24 ~length:2 in
  let v2c8 = ws ~start:22 ~length:2 in
  (* Next row: MSB-first crumbs, matching o1js rangeCheck1Helper *)
  let v2c9 = ws ~start:20 ~length:2 in
  let v2c10 = ws ~start:18 ~length:2 in
  let v2c11 = ws ~start:16 ~length:2 in
  let v2c12 = ws ~start:14 ~length:2 in
  let v2c13 = ws ~start:12 ~length:2 in
  let v2c14 = ws ~start:10 ~length:2 in
  let v2c15 = ws ~start:8 ~length:2 in
  let v2c16 = ws ~start:6 ~length:2 in
  let v2c17 = ws ~start:4 ~length:2 in
  let v2c18 = ws ~start:2 ~length:2 in
  let v2c19 = ws ~start:0 ~length:2 in
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

(** Emit a Generic gate: ql*left + qr*right + qo*out + qm*left*right + qc = 0. *)
let generic ~(ql : Circuit.Field.Constant.t) ~(qr : Circuit.Field.Constant.t)
    ~(qo : Circuit.Field.Constant.t) ~(qm : Circuit.Field.Constant.t)
    ~(qc : Circuit.Field.Constant.t) ~(left : Circuit.Field.t)
    ~(right : Circuit.Field.t) ~(out : Circuit.Field.t) : unit =
  Circuit.assert_
    (Basic { l = (ql, left); r = (qr, right); o = (qo, out); m = qm; c = qc })

(** Witness z = a*x*y + b*x + c*y + d and emit a Generic gate constraining it. *)
let bilinear (x : Circuit.Field.t) (y : Circuit.Field.t)
    ~(a : Circuit.Field.Constant.t) ~(b : Circuit.Field.Constant.t)
    ~(c : Circuit.Field.Constant.t) ~(d : Circuit.Field.Constant.t) :
    Circuit.Field.t =
  let z =
    Circuit.exists Circuit.Field.typ ~compute:(fun () ->
        let x0 = Circuit.As_prover.read_var x in
        let y0 = Circuit.As_prover.read_var y in
        Circuit.Field.Constant.((a * x0 * y0) + (b * x0) + (c * y0) + d) )
  in
  (* b*x + c*y - z + a*x*y + d = 0 *)
  generic ~ql:b ~qr:c
    ~qo:Circuit.Field.Constant.(zero - one)
    ~qm:a ~qc:d ~left:x ~right:y ~out:z ;
  z

(** Assert a*x*y + b*x + c*y + d = 0. *)
let assert_bilinear (x : Circuit.Field.t) (y : Circuit.Field.t)
    ~(a : Circuit.Field.Constant.t) ~(b : Circuit.Field.Constant.t)
    ~(c : Circuit.Field.Constant.t) ~(d : Circuit.Field.Constant.t) : unit =
  let empty =
    Circuit.exists Circuit.Field.typ ~compute:(fun () ->
        Circuit.Field.Constant.zero )
  in
  (* b*x + c*y + 0*out + a*x*y + d = 0 *)
  generic ~ql:b ~qr:c ~qo:Circuit.Field.Constant.zero ~qm:a ~qc:d ~left:x
    ~right:y ~out:empty

(** Matches o1js's ifField: b*(x-y)+y, sealed. *)
let if_field (b : Circuit.Field.t) ~(then_ : Circuit.Field.t)
    ~(else_ : Circuit.Field.t) : Circuit.Field.t =
  seal Circuit.Field.((b * (then_ - else_)) + else_)

(** Assert x is one of the allowed values.
    Emits (n-1) Generic gates for n allowed values. *)
let assert_one_of (x : Circuit.Field.t) (allowed : Circuit.Field.Constant.t list)
    : unit =
  let x = to_var x in
  match allowed with
  | [] ->
      failwith "assert_one_of: empty list"
  | [ c1 ] ->
      (* x - c1 = 0 *)
      Circuit.assert_ (Equal (x, Circuit.Field.constant c1))
  | c1 :: c2 :: rest ->
      let module C = Circuit.Field.Constant in
      let n = List.length rest in
      if n = 0 then
        (* (x - c1)*(x - c2) = 0 *)
        assert_bilinear x x ~a:C.one
          ~b:C.(zero - (c1 + c2))
          ~c:C.zero
          ~d:C.(c1 * c2)
      else
        (* z = (x - c1)*(x - c2) *)
        let z =
          ref
            (bilinear x x ~a:C.one
               ~b:C.(zero - (c1 + c2))
               ~c:C.zero
               ~d:C.(c1 * c2) )
        in
        List.iteri rest ~f:(fun i ci ->
            if i < n - 1 then
              (* z = z*(x - ci) *)
              z := bilinear !z x ~a:C.one ~b:C.(zero - ci) ~c:C.zero ~d:C.zero
            else
              (* z*(x - ci) = 0 *)
              assert_bilinear !z x ~a:C.one ~b:C.(zero - ci) ~c:C.zero ~d:C.zero )

(* ------------------------------------------------------------------ *)
(* Multi-range checks                                                  *)
(* ------------------------------------------------------------------ *)

(** Range check all three limbs of a Field3 to [0, 2^88). *)
let multi_range_check ((x, y, z) : Field3.t) : unit =
  if Field3.is_constant (x, y, z) then (
    let check l name =
      let v_bignum = Option.value_exn (Limb.to_constant l) in
      if Bignum_bigint.(v_bignum >= two_to_limb) then
        failwith (sprintf "multi_range_check: %s >= 2^%d" name limb_bits)
    in
    check x "x" ; check y "y" ; check z "z" )
  else
    let x = Limb.to_var x in
    let y = Limb.to_var y in
    let z = Limb.to_var z in
    let zero = to_var (Circuit.Field.constant Circuit.Field.Constant.zero) in
    let x64, x76 = range_check0 x ~compact:false in
    let y64, y76 = range_check0 y ~compact:false in
    range_check1 ~x64 ~x76 ~y64 ~y76 ~z ~yz:zero

(* Initialize the Field3.typ check function now that multi_range_check exists *)
let () = Field3.check_ref := multi_range_check

(** Range check a compact 2-limb value [xy] (176 bits) and a single
    limb [z] (88 bits). Returns the three individual limbs. *)
let compact_multi_range_check (xy : Circuit.Field.t) (z : Limb.t) :
    Field3.t =
  if
    Option.is_some (Circuit.Field.to_constant xy)
    && Option.is_some (Limb.to_constant z)
  then (
    let xy_bignum =
      field_const_to_bignum (Option.value_exn (Circuit.Field.to_constant xy))
    in
    let z_bignum = Option.value_exn (Limb.to_constant z) in
    if Bignum_bigint.(xy_bignum >= two_to_2limb) then
      failwith "compact_multi_range_check: xy >= 2^176" ;
    if Bignum_bigint.(z_bignum >= two_to_limb) then
      failwith "compact_multi_range_check: z >= 2^88" ;
    let x = Bignum_bigint.(xy_bignum land limb_mask) in
    let y = Bignum_bigint.(shift_right xy_bignum limb_bits) in
    (Limb.of_constant x, Limb.of_constant y, Limb.of_constant z_bignum) )
  else
    let xy = to_var xy in
    let x =
      Circuit.exists Limb.typ ~compute:(fun () ->
          let xy_v = Circuit.As_prover.read_var xy in
          let xy_bignum = field_const_to_bignum xy_v in
          Bignum_bigint.(xy_bignum land limb_mask) )
    in
    let y =
      Circuit.exists Limb.typ ~compute:(fun () ->
          let xy_v = Circuit.As_prover.read_var xy in
          let xy_bignum = field_const_to_bignum xy_v in
          Bignum_bigint.(shift_right xy_bignum limb_bits) )
    in
    let z64, z76 = range_check0 (Limb.to_var z) ~compact:false in
    let x64, x76 = range_check0 x ~compact:true in
    range_check1 ~x64:z64 ~x76:z76 ~y64:x64 ~y76:x76 ~z:y ~yz:xy ;
    (x, y, z)

(* ------------------------------------------------------------------ *)
(* Almost-reduced assertion                                            *)
(* ------------------------------------------------------------------ *)

(** Compute a bound value for the high limb that proves x < f
    (or x <= f depending on the modulus structure). *)
let weak_bound (x2 : Limb.t) ~(f : Bignum_bigint.t) : Limb.t =
  let l2_mask = Bignum_bigint.(two_to_2limb - one) in
  let bound =
    if Bignum_bigint.(f land l2_mask = zero) then
      Bignum_bigint.(two_to_limb - shift_right f (Int.( * ) 2 limb_bits))
    else
      Bignum_bigint.(limb_mask - shift_right f (Int.( * ) 2 limb_bits))
  in
  Limb.add_const x2 bound

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
  let mrc_count = ref 0 in
  List.iter xs ~f:(fun ((_, _, x2) as x) ->
      if not skip_mrc then (
        let was_constant = Field3.is_constant x in
        multi_range_check x ;
        if not was_constant then (
          incr mrc_count ;
          check_abort (sprintf "after_mrc%d" !mrc_count) ) ) ;
      bounds := !bounds @ [ weak_bound x2 ~f ] ;
      if List.length !bounds = 3 then flush_bounds () ) ;
  match !bounds with
  | [ b1 ] ->
      multi_range_check
        (b1, Limb.of_constant Bignum_bigint.zero, Limb.of_constant Bignum_bigint.zero)
  | [ b1; b2 ] ->
      multi_range_check
        (b1, b2, Limb.of_constant Bignum_bigint.zero)
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
    let xl0, xl1, xl2 = x in
    let yl0, yl1, yl2 = y in
    let xv0 = Circuit.As_prover.read Limb.typ xl0 in
    let xv1 = Circuit.As_prover.read Limb.typ xl1 in
    let xv2 = Circuit.As_prover.read Limb.typ xl2 in
    let yv0 = Circuit.As_prover.read Limb.typ yl0 in
    let yv1 = Circuit.As_prover.read Limb.typ yl1 in
    let yv2 = Circuit.As_prover.read Limb.typ yl2 in
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
    let x01 = Bignum_bigint.(xv0 + shift_left xv1 limb_bits) in
    let y01 = Bignum_bigint.(yv0 + shift_left yv1 limb_bits) in
    let f01 = Bignum_bigint.(f0 + shift_left f1 limb_bits) in
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
  let r0 = Circuit.exists Limb.typ ~compute: (fun () -> let r0, _, _, _, _ = get_cached () in r0) in
  let r1 = Circuit.exists Limb.typ ~compute: (fun () -> let _, r1, _, _, _ = get_cached () in r1) in
  let r2 = Circuit.exists Limb.typ ~compute: (fun () -> let _, _, r2, _, _ = get_cached () in r2) in
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
  let x0, x1, x2 = Field3.vars x in
  let y0, y1, y2 = Field3.vars y in
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
    let xs = xs
    in
    let result = ref (List.hd_exn xs) in
    List.iter2_exn (List.tl_exn xs) signs ~f:(fun xi sign_i ->
        let r, _overflow = single_add !result xi ~sign:sign_i ~f in
        result := r ) ;
    let r0v, r1v, r2v = Field3.vars !result in
    Circuit.assert_
      (Raw { kind = Zero; values = [| r0v; r1v; r2v |]; coeffs = [||] }) ;
    (* Indirect range check *)
    let rl0, rl1, rl2 = !result in
    let r0_trunc =
      Circuit.exists Limb.typ ~compute: (fun () ->
          Bignum_bigint.(Circuit.As_prover.read Limb.typ rl0 land limb_mask) )
    in
    let r1_trunc =
      Circuit.exists Limb.typ ~compute: (fun () ->
          Bignum_bigint.(Circuit.As_prover.read Limb.typ rl1 land limb_mask) )
    in
    let r2_trunc =
      Circuit.exists Limb.typ ~compute: (fun () ->
          Bignum_bigint.(Circuit.As_prover.read Limb.typ rl2 land limb_mask) )
    in
    multi_range_check (r0_trunc, r1_trunc, r2_trunc) ;
    Circuit.assert_ (Equal (r0v, Limb.to_field r0_trunc)) ;
    Circuit.assert_ (Equal (r1v, Limb.to_field r1_trunc)) ;
    Circuit.assert_ (Equal (r2v, Limb.to_field r2_trunc)) ;
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
    : Field3.t * Circuit.Field.t * Limb.t =
  let f_ =
    Bignum_bigint.(pow (of_int 2) (of_int (Int.( * ) 3 limb_bits)) - f)
  in
  let f_0, f_1, f_2 = Field3.Constant.split f_ in
  let f2 = Bignum_bigint.(shift_right f (Int.( * ) 2 limb_bits)) in
  let f2_bound = Bignum_bigint.(two_to_limb - f2 - one) in
  let module T = struct
    type t = {
      r01 : Bignum_bigint.t;
      r2 : Bignum_bigint.t;
      q0 : Bignum_bigint.t;
      q1 : Bignum_bigint.t;
      q2 : Bignum_bigint.t;
      q2_bound : Bignum_bigint.t;
      p10 : Bignum_bigint.t;
      p110 : Bignum_bigint.t;
      p111 : Bignum_bigint.t;
      c0 : Bignum_bigint.t;
      c1_00 : Bignum_bigint.t;
      c1_12 : Bignum_bigint.t;
      c1_24 : Bignum_bigint.t;
      c1_36 : Bignum_bigint.t;
      c1_48 : Bignum_bigint.t;
      c1_60 : Bignum_bigint.t;
      c1_72 : Bignum_bigint.t;
      c1_84 : Bignum_bigint.t;
      c1_86 : Bignum_bigint.t;
      c1_88 : Bignum_bigint.t;
      c1_90 : Bignum_bigint.t;
    }

    let typ : (_, t) Circuit.Typ.t = Circuit.Typ.prover_value ()
  end in
  let witness =
    Circuit.exists T.typ ~compute:(fun () ->
        let al0, al1, al2 = a in
        let bl0, bl1, bl2 = b in
        let av0 = Circuit.As_prover.read Limb.typ al0 in
        let av1 = Circuit.As_prover.read Limb.typ al1 in
        let av2 = Circuit.As_prover.read Limb.typ al2 in
        let bv0 = Circuit.As_prover.read Limb.typ bl0 in
        let bv1 = Circuit.As_prover.read Limb.typ bl1 in
        let bv2 = Circuit.As_prover.read Limb.typ bl2 in
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
            + shift_left (shift_right r limb_bits land limb_mask) limb_bits)
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
        let _p11 = Bignum_bigint.(p110 + shift_left p111 limb_bits) in
        let c0 =
          Bignum_bigint.(
            shift_right
              (p0 + shift_left p10 limb_bits - r01)
              (Int.( * ) 2 limb_bits))
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
        {
          T.r01;
          r2;
          q0;
          q1;
          q2;
          q2_bound;
          p10;
          p110;
          p111;
          c0;
          c1_00;
          c1_12;
          c1_24;
          c1_36;
          c1_48;
          c1_60;
          c1_72;
          c1_84;
          c1_86;
          c1_88;
          c1_90;
        })
  in
  let open Circuit in
  let w_field f =
    exists Field.typ ~compute:(fun () ->
        bignum_to_field_const (f (As_prover.read T.typ witness)))
  in
  let r01 = w_field (fun x -> x.T.r01) in
  let r2 =
    exists Limb.typ ~compute:(fun () -> (As_prover.read T.typ witness).T.r2)
  in
  let q0 =
    exists Limb.typ ~compute:(fun () -> (As_prover.read T.typ witness).q0)
  in
  let q1 =
    exists Limb.typ ~compute:(fun () -> (As_prover.read T.typ witness).q1)
  in
  let q2 =
    exists Limb.typ ~compute:(fun () -> (As_prover.read T.typ witness).q2)
  in
  let q2_bound =
    exists Limb.typ ~compute:(fun () -> (As_prover.read T.typ witness).q2_bound)
  in
  let p10 =
    exists Limb.typ ~compute:(fun () -> (As_prover.read T.typ witness).p10)
  in
  let p110 =
    exists Limb.typ ~compute:(fun () -> (As_prover.read T.typ witness).p110)
  in
  let p111 = w_field (fun x -> x.T.p111) in
  let c0 = w_field (fun x -> x.T.c0) in
  let c1_00 = w_field (fun x -> x.T.c1_00) in
  let c1_12 = w_field (fun x -> x.T.c1_12) in
  let c1_24 = w_field (fun x -> x.T.c1_24) in
  let c1_36 = w_field (fun x -> x.T.c1_36) in
  let c1_48 = w_field (fun x -> x.T.c1_48) in
  let c1_60 = w_field (fun x -> x.T.c1_60) in
  let c1_72 = w_field (fun x -> x.T.c1_72) in
  let c1_84 = w_field (fun x -> x.T.c1_84) in
  let c1_86 = w_field (fun x -> x.T.c1_86) in
  let c1_88 = w_field (fun x -> x.T.c1_88) in
  let c1_90 = w_field (fun x -> x.T.c1_90) in
  let a0, a1, a2 = Field3.vars a in
  let b0, b1, b2 = Field3.vars b in
  Circuit.assert_
    (ForeignFieldMul
       {
         left_input0 = a0;
         left_input1 = a1;
         left_input2 = a2;
         right_input0 = b0;
         right_input1 = b1;
         right_input2 = b2;
         remainder01 = r01;
         remainder2 = Limb.to_field r2;
         quotient0 = Limb.to_field q0;
         quotient1 = Limb.to_field q1;
         quotient2 = Limb.to_field q2;
         quotient_hi_bound = Limb.to_field q2_bound;
         product1_lo = Limb.to_field p10;
         product1_hi_0 = Limb.to_field p110;
         product1_hi_1 = p111;
         carry0 = c0;
         carry1_0 = c1_00;
         carry1_12 = c1_12;
         carry1_24 = c1_24;
         carry1_36 = c1_36;
         carry1_48 = c1_48;
         carry1_60 = c1_60;
         carry1_72 = c1_72;
         carry1_84 = c1_84;
         carry1_86 = c1_86;
         carry1_88 = c1_88;
         carry1_90 = c1_90;
         foreign_field_modulus2 = bignum_to_field_const f2;
         neg_foreign_field_modulus0 = bignum_to_field_const f_0;
         neg_foreign_field_modulus1 = bignum_to_field_const f_1;
         neg_foreign_field_modulus2 = bignum_to_field_const f_2;
       });
  multi_range_check (p10, p110, q2_bound);
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
  Circuit.assert_ (Equal (Limb.to_field r2, xy2))

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
    let xy0, xy1, xy2 = Field3.vars xy in
    let q, r01, r2 = multiply_no_range_check x y ~f in
    multi_range_check q ;
    let xy01 =
      Circuit.Field.(xy0 + (xy1 * constant (bignum_to_field_const two_to_limb)))
    in
    Circuit.assert_ (Equal (r01, xy01)) ;
    Circuit.assert_ (Equal (Limb.to_field r2, xy2))

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
    let xl0, xl1, xl2 = x in
    let inv_witness =
      Circuit.exists (Circuit.Typ.prover_value ()) ~compute:(fun () ->
          let xv0 = Circuit.As_prover.read Limb.typ xl0 in
          let xv1 = Circuit.As_prover.read Limb.typ xl1 in
          let xv2 = Circuit.As_prover.read Limb.typ xl2 in
          let x_big = Field3.Constant.combine (xv0, xv1, xv2) in
          match bignum_mod_inverse x_big ~f with
          | Some v -> Field3.Constant.split v
          | None -> Bignum_bigint.(zero, zero, zero) )
    in
    let open Circuit in
    let wl i =
      exists Limb.typ ~compute:(fun () ->
          let l0, l1, l2 =
            As_prover.read (Typ.prover_value ()) inv_witness
          in
          [| l0; l1; l2 |].(i) )
    in
    let v0 = wl 0 in
    let v1 = wl 1 in
    let v2 = wl 2 in
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
      , Limb.of_constant Bignum_bigint.zero
      , Limb.of_constant Bignum_bigint.zero ) ;
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
    Circuit.assert_ (Equal (Limb.to_field x0, Limb.to_field y0)) ;
    Circuit.assert_ (Equal (Limb.to_field x1, Limb.to_field y1)) ;
    Circuit.assert_ (Equal (Limb.to_field x2, Limb.to_field y2)) )

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

(** Check if a circuit field variable equals another field variable.
    Matches o1js's Field.equals() gate sequence exactly:
    seal(x-y), exists [b,z] as raw fields (no boolean check),
    assertMul(b, diff, 0), assertMul(z, diff, 1-b). *)
let field_var_equal (x : Circuit.Field.t) (y : Circuit.Field.t) :
    Circuit.Boolean.var =
  match (Circuit.Field.to_constant x, Circuit.Field.to_constant y) with
  | Some cx, Some cy ->
      if Circuit.Field.Constant.(equal cx cy) then Circuit.Boolean.true_
      else Circuit.Boolean.false_
  | _ ->
      let diff = seal Circuit.Field.(x - y) in
      (* Allocate b and z as raw fields — no Boolean check constraint.
         o1js uses exists(2, ...) + Bool.Unsafe.fromField, which skips
         the boolean constraint since R1CS constraints already imply it. *)
      let b, z =
        Circuit.exists
          Circuit.Typ.(tuple2 field field)
          ~compute:(fun () ->
            let dv = Circuit.As_prover.read_var diff in
            if Circuit.Field.Constant.(equal dv zero) then
              (Circuit.Field.Constant.one, Circuit.Field.Constant.zero)
            else (Circuit.Field.Constant.zero, Circuit.Field.Constant.(inv dv))
            )
      in
      (* b * diff = 0 (if b=true then diff must be 0) *)
      Circuit.assert_ (R1CS (b, diff, Circuit.Field.zero)) ;
      (* z * diff = 1 - b (if diff != 0 then b must be false) *)
      Circuit.assert_ (R1CS (z, diff, Circuit.Field.(constant Constant.one - b))) ;
      Circuit.Boolean.Unsafe.of_cvar b

let field_equal (x : Circuit.Field.t) (c : Bignum_bigint.t) :
    Circuit.Boolean.var =
  field_var_equal x (Circuit.Field.constant (bignum_to_field_const c))

(* ------------------------------------------------------------------ *)
(* Sum accumulator                                                     *)
(* ------------------------------------------------------------------ *)

(** Lazy accumulator for chaining additions/subtractions.
    Operations are collected and materialized at once when [finish]
    is called. *)
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
      Used for the xy (result) operand in assertMul. *)
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
      let xs = t.summands in
      let result = ref (List.hd_exn xs) in
      List.iter2_exn (List.tl_exn xs) t.ops ~f:(fun xi sign_i ->
          let r, _overflow = single_add !result xi ~sign:sign_i ~f in
          result := r ) ;
      let r0, r1, r2 = Field3.vars !result in
      Circuit.assert_
        (Raw { kind = Zero; values = [| r0; r1; r2 |]; coeffs = [||] }) ;
      t.result <- Some !result ;
      !result

  (** Materialize the sum for use as a multiplication input.
      Produces ForeignFieldAdd gates + Zero gate + Generic gates for
      low-limb tracking, but skips the multi_range_check.
      Uses Generic gates to constrain the lowest limb individually,
      since FFAdd only constrains the low+middle limbs together. *)
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
        let xs = xs in
        let f0 = Bignum_bigint.(f land limb_mask) in
        let n = List.length signs in
        (* Generic gates for low limbs.
           Track the full accumulated value (matching o1js xRef) to
           correctly determine overflow across iterations. *)
        let x0 =
          ref
            (let l0, _, _ = List.hd_exn xs in
             to_var (Limb.to_field l0) )
        in
        (* Track the full accumulated value across iterations, matching
           o1js's Unconstrained.witness(xRef). Overflow depends on the
           full value, not just the low limb. *)
        let x_full_ref =
          Circuit.exists (Circuit.Typ.prover_value ()) ~compute:(fun () ->
              let l0, l1, l2 = List.hd_exn xs in
              let rl l = Circuit.As_prover.read Limb.typ l in
              ref (Field3.Constant.combine (rl l0, rl l1, rl l2)) )
        in
        let x0s = Array.create ~len:n Circuit.Field.zero in
        let overflows = Array.create ~len:n Circuit.Field.zero in
        List.iteri (List.tl_exn xs) ~f:(fun i xi ->
            let xi0, _, _ = xi in
            let xi0v = Limb.to_field xi0 in
            let sign_i = List.nth_exn signs i in
            let sign_bi = sign_to_bigint sign_i in
            let carry, overflow =
              let c =
                Circuit.exists
                  (Circuit.Typ.tuple2 Circuit.Field.typ Circuit.Field.typ)
                  ~compute:(fun () ->
                    let xr =
                      Circuit.As_prover.read
                        (Circuit.Typ.prover_value ())
                        x_full_ref
                    in
                    let x_full = !xr in
                    let x0v =
                      field_const_to_bignum (Circuit.As_prover.read_var !x0)
                    in
                    let xi_full =
                      let l0, l1, l2 = xi in
                      let rl l = Circuit.As_prover.read Limb.typ l in
                      Field3.Constant.combine (rl l0, rl l1, rl l2)
                    in
                    let x_new = Bignum_bigint.(x_full + (sign_bi * xi_full)) in
                    let overflow =
                      if Bignum_bigint.(sign_bi > zero && x_new >= f) then
                        Bignum_bigint.one
                      else if Bignum_bigint.(sign_bi < zero && x_new < zero)
                      then Bignum_bigint.(neg one)
                      else Bignum_bigint.zero
                    in
                    (xr := Bignum_bigint.(x_new - (overflow * f))) ;
                    let x0_new =
                      Bignum_bigint.(
                        x0v
                        + sign_bi
                          * Circuit.As_prover.read Limb.typ xi0
                        - (overflow * f0))
                    in
                    let carry = Bignum_bigint.(shift_right x0_new limb_bits) in
                    (bignum_to_field_const carry, bignum_to_field_const overflow) )
              in
              (fst c, snd c)
            in
            overflows.(i) <- overflow ;
            (* Constrain carry to {0, 1, -1}. *)
            let neg_one = Circuit.Field.Constant.(zero - one) in
            assert_one_of carry
              [ Circuit.Field.Constant.zero
              ; Circuit.Field.Constant.one
              ; neg_one
              ] ;
            (* x0 <- x0 + sign*xi0 - overflow*f0 - carry*2^l *)
            let sign_field = bignum_to_field_const sign_bi in
            let f0_field = bignum_to_field_const f0 in
            let two_l_field = bignum_to_field_const two_to_limb in
            let x0_expr =
              Circuit.Field.(
                !x0
                + (xi0v * constant sign_field)
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
            Circuit.assert_ (Equal (Limb.to_field r0, x0s.(i))) ;
            Circuit.assert_ (Equal (overflow, overflows.(i))) ;
            result := r ) ;
        ( if not t.chained then
          let r0, r1, r2 = Field3.vars !result in
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

    Note: finishForMulInput replaces the range check with generic-gate
    low-limb constraints. Our Sum.finish uses the standard range check
    approach. Matching the exact gate sequence requires implementing
    generic-gate low-limb tracking. *)

(** Convert a Field3 to variables if not already pure variables.
    Ensures finished sum values don't break the gate chain. *)
let to_var_field3 ((l0, l1, l2) : Field3.t) : Field3.t =
  (Limb.to_var l0, Limb.to_var l1, Limb.to_var l2)

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
    ( match x with
    | Sum_input s ->
        Sum.is_constant s
    | Field3_input f3 ->
        Field3.is_constant f3 )
    && Field3.is_constant y_val && Field3.is_constant xy_val
  in
  let y_val, xy_val =
    if all_constant then (y_val, xy_val)
    else
      let y_val = to_var_field3 y_val in
      let xy_val = to_var_field3 xy_val in
      (y_val, xy_val)
  in
  let x_val = finish_chained x in
  assert_mul x_val y_val xy_val ~f

(* ------------------------------------------------------------------ *)
(* FpU / FpA: Typed foreign field hierarchy                            *)
(*                                                                     *)
(*   ForeignField (base)     — add, sub, neg, sum                      *)
(*     └ UnreducedForeignField  — check = MRC                          *)
(*     └ ForeignFieldWithMul    — mul, inv, div                        *)
(*         └ AlmostForeignField — check = MRC + weakBound              *)
(*         └ CanonicalForeignField — check = MRC + canonical           *)
(*                                                                     *)
(* Return types:                                                       *)
(*   add/sub → Unreduced,  neg → AlmostReduced                        *)
(*   mul → Unreduced,  inv/div → AlmostReduced                        *)
(* ------------------------------------------------------------------ *)

(** Unreduced foreign field element. Limbs are range-checked (< 2^88)
    but the high limb is NOT weakly bounded.

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
      Note: neg canonically returns AlmostReduced. We return FpU here
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

  (* add/sub return FpU *)
  let add (x : t) (y : t) ~(f : Bignum_bigint.t) : FpU.t =
    FpU.of_field3_unsafe (add x y ~f)

  let sub (x : t) (y : t) ~(f : Bignum_bigint.t) : FpU.t =
    FpU.of_field3_unsafe (sub x y ~f)

  (* neg returns FpA because negation proves r = f - x >= 0, so r < f *)
  let neg (x : t) ~(f : Bignum_bigint.t) : t = negate x ~f

  (* mul returns FpU *)
  let mul (x : t) (y : t) ~(f : Bignum_bigint.t) : FpU.t =
    FpU.of_field3_unsafe (mul x y ~f)

  (* inv/div return FpA *)
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
                  , Limb.of_constant Bignum_bigint.zero
                  , Limb.of_constant Bignum_bigint.zero ) ) )
      }
end

(** Canonical foreign field element.  Limbs are range-checked (< 2^88)
    AND the full value is proven < f.

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
