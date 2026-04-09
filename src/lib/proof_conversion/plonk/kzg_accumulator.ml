(** KzgAccumulator: in-circuit type for zkp12-23.

    After zkp12 transitions from the PLONK Accumulator,
    circuits zkp13-23 operate on this KZG-specific accumulator.

    Reference: nori-proof-conversion/src/kzg/structs.ts *)

open! Core_kernel
module Step = Pickles.Impls.Step
module FF = Snarky_foreign_field.Foreign_field

(** ATE_LOOP_COUNT for BN254 pairing. Length = 65. *)
let ate_loop_count =
  [| 1; 1; 0; 1; 0; 0; -1; 0; 1; 1; 0; 0; 0; -1; 0; 0
   ; 1; 1; 0; 0; -1; 0; 0; 0; 0; 0; 1; 0; 0; -1; 0; 0
   ; 1; 1; 1; 0; 0; 0; 0; -1; 0; 1; 0; 0; -1; 0; 1; 1
   ; 0; 0; 1; 0; 0; -1; 1; 0; 0; -1; 0; 1; 0; 1; 0; 0; 0
  |]

let ate_loop_len = Array.length ate_loop_count  (* 65 *)

(** ArrayListHasher.empty() = Poseidon.hashPacked(Array(Field, 65), zeros).
    Precomputed constant matching nori's ArrayListHasher.empty(). *)
let array_list_hasher_empty =
  Step.Field.constant
    (Step.Field.Constant.of_string
       "28832630828976582602038031409816593539422152810927507906214302524112741671461")

(** KZG proof: pairing points + shift + c values. *)
type kzg_proof =
  { a_x : FF.FpA.t  (** G1Affine A point *)
  ; a_y : FF.FpA.t
  ; neg_b_x : FF.FpA.t  (** G1Affine negB point *)
  ; neg_b_y : FF.FpA.t
  ; shift_power : Step.Field.t  (** Native field: 0, 1, or 2 *)
  ; c : Fp12.Circuit.t
  ; c_inv : Fp12.Circuit.t
  ; pi0 : FF.FpA.t  (** FrC *)
  ; pi1 : FF.FpA.t
  }

(** KZG state: f accumulator + lines hash digest. *)
type kzg_state =
  { mutable f : Fp12.Circuit.t
  ; mutable lines_hashes_digest : Step.Field.t
  }

(** Full KZG accumulator. *)
type t =
  { proof : kzg_proof
  ; state : kzg_state
  }

(** Build Random_oracle_input.Chunked.t matching nori's
    Poseidon.hashPacked(KzgAccumulator, acc).

    KzgProof fields: A (G1Affine), negB (G1Affine), shift_power (Field),
      c (Fp12), c_inv (Fp12), pi0 (FrC), pi1 (FrC)
    KzgState fields: f (Fp12), lines_hashes_digest (Field) *)
let to_input (acc : t) : Step.Field.t Random_oracle_input.Chunked.t =
  let fields = Queue.create () in
  let packeds = Queue.create () in
  let l = 88 in
  let add_fpa (x : FF.FpA.t) =
    let l0, l1, l2 = FF.FpA.to_field3 x in
    Queue.enqueue packeds (l0, l) ;
    Queue.enqueue packeds (l1, l) ;
    Queue.enqueue packeds (l2, l)
  in
  let add_fp12 (x : Fp12.Circuit.t) =
    (* Fp12 = { c0: Fp6, c1: Fp6 }
       Fp6 = { c0: Fp2, c1: Fp2, c2: Fp2 }
       Fp2 = { c0: FpA, c1: FpA }
       Each FpA → 3 packed entries *)
    let add_fp2 (fp2 : Fp2.Circuit.t) =
      add_fpa fp2.c0 ; add_fpa fp2.c1
    in
    let add_fp6 (fp6 : Fp6.Circuit.t) =
      add_fp2 fp6.c0 ; add_fp2 fp6.c1 ; add_fp2 fp6.c2
    in
    add_fp6 x.c0 ; add_fp6 x.c1
  in
  (* === proof fields (Struct declaration order) === *)
  (* G1Affine A *)
  add_fpa acc.proof.a_x ;
  add_fpa acc.proof.a_y ;
  (* G1Affine negB *)
  add_fpa acc.proof.neg_b_x ;
  add_fpa acc.proof.neg_b_y ;
  (* shift_power: native Field, unpacked (matching o1js Field.toInput → {fields: [value]}) *)
  Queue.enqueue fields acc.proof.shift_power ;
  (* c: Fp12 *)
  add_fp12 acc.proof.c ;
  (* c_inv: Fp12 *)
  add_fp12 acc.proof.c_inv ;
  (* pi0, pi1: FrC *)
  add_fpa acc.proof.pi0 ;
  add_fpa acc.proof.pi1 ;
  (* === state fields === *)
  (* f: Fp12 *)
  add_fp12 acc.state.f ;
  (* lines_hashes_digest: native Field, unpacked (matching o1js Field.toInput → {fields: [value]}) *)
  Queue.enqueue fields acc.state.lines_hashes_digest ;
  { field_elements = Queue.to_array fields
  ; packeds = Queue.to_array packeds
  }

(** Hash with Poseidon, matching hashPacked(KzgAccumulator, acc). *)
let hash_packed (acc : t) : Step.Field.t =
  let input = to_input acc in
  let packed_fields = Random_oracle.Checked.pack_input input in
  Random_oracle.Checked.hash packed_fields

(** Constant types for KzgAccumulator. *)
type kzg_proof_const =
  { a_x : FF.Field3.Constant.t ; a_y : FF.Field3.Constant.t
  ; neg_b_x : FF.Field3.Constant.t ; neg_b_y : FF.Field3.Constant.t
  ; shift_power : Step.Field.Constant.t
  ; c : Fp12.Constant.t ; c_inv : Fp12.Constant.t
  ; pi0 : FF.Field3.Constant.t ; pi1 : FF.Field3.Constant.t
  }

type kzg_state_const =
  { f : Fp12.Constant.t
  ; lines_hashes_digest : Step.Field.Constant.t
  }

type t_const =
  { proof : kzg_proof_const
  ; state : kzg_state_const
  }

let default_const : t_const =
  let z3 = FF.Field3.Constant.zero in
  { proof =
      { a_x = z3; a_y = z3; neg_b_x = z3; neg_b_y = z3
      ; shift_power = Step.Field.Constant.zero
      ; c = Fp12.Constant.one; c_inv = Fp12.Constant.one
      ; pi0 = z3; pi1 = z3
      }
  ; state =
      { f = Fp12.Constant.one
      ; lines_hashes_digest = Step.Field.Constant.zero
      }
  }

(** Typ.t for KzgAccumulator with proper range checks. *)
let typ : (t, t_const) Step.Typ.t =
  let p = Bn254_params.p in
  let r = Bn254_params.r in
  (* G1Affine (x:FpA, y:FpA) and Fp12 components use FpA.typ (assertAlmostReduced).
     pi0/pi1 use FrC (canonical with assertLessThan), matching nori's FrC.provable. *)
  let fpc_typ = FF.FpA.typ ~f:p in
  let frc_typ =
    Step.Typ.transport_var (FF.FpC.typ ~f:r)
      ~there:(fun a -> FF.FpC.of_fpa_unsafe a)
      ~back:(fun c -> (c :> FF.FpA.t)) in
  let proof_typ =
    Step.Typ.of_hlistable
      [ fpc_typ; fpc_typ; fpc_typ; fpc_typ
      ; Step.Field.typ
      ; Fp12.typ; Fp12.typ
      ; frc_typ; frc_typ
      ]
      ~var_to_hlist:(fun (p : kzg_proof) ->
        [ p.a_x; p.a_y; p.neg_b_x; p.neg_b_y
        ; p.shift_power
        ; p.c; p.c_inv
        ; p.pi0; p.pi1 ] )
      ~var_of_hlist:(fun
        ([ a_x; a_y; neg_b_x; neg_b_y; shift_power; c; c_inv; pi0; pi1 ] :
           (unit, _) Snarky_backendless.H_list.t) ->
        { a_x; a_y; neg_b_x; neg_b_y; shift_power; c; c_inv; pi0; pi1 } )
      ~value_to_hlist:(fun (p : kzg_proof_const) ->
        [ p.a_x; p.a_y; p.neg_b_x; p.neg_b_y
        ; p.shift_power
        ; p.c; p.c_inv
        ; p.pi0; p.pi1 ] )
      ~value_of_hlist:(fun
        ([ a_x; a_y; neg_b_x; neg_b_y; shift_power; c; c_inv; pi0; pi1 ] :
           (unit, _) Snarky_backendless.H_list.t) ->
        { a_x; a_y; neg_b_x; neg_b_y; shift_power; c; c_inv; pi0; pi1 } )
  in
  let state_typ =
    Step.Typ.of_hlistable
      [ Fp12.typ; Step.Field.typ ]
      ~var_to_hlist:(fun (s : kzg_state) ->
        [ s.f; s.lines_hashes_digest ] )
      ~var_of_hlist:(fun
        ([ f; lines_hashes_digest ] :
           (unit, _) Snarky_backendless.H_list.t) ->
        { f; lines_hashes_digest } )
      ~value_to_hlist:(fun (s : kzg_state_const) ->
        [ s.f; s.lines_hashes_digest ] )
      ~value_of_hlist:(fun
        ([ f; lines_hashes_digest ] :
           (unit, _) Snarky_backendless.H_list.t) ->
        { f; lines_hashes_digest } )
  in
  Step.Typ.of_hlistable
    [ proof_typ; state_typ ]
    ~var_to_hlist:(fun (a : t) -> [ a.proof; a.state ] )
    ~var_of_hlist:(fun
      ([ proof; state ] : (unit, _) Snarky_backendless.H_list.t) ->
      { proof; state } )
    ~value_to_hlist:(fun (a : t_const) -> [ a.proof; a.state ] )
    ~value_of_hlist:(fun
      ([ proof; state ] : (unit, _) Snarky_backendless.H_list.t) ->
      { proof; state } )

(** Witness a KzgAccumulator using the proper Typ.t. *)
let witness () : t =
  Step.exists typ ~compute:(fun () -> default_const)
