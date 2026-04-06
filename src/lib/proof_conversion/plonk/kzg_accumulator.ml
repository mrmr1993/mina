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
  (* shift_power: native Field, unpacked *)
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
  (* lines_hashes_digest: native Field, unpacked *)
  Queue.enqueue fields acc.state.lines_hashes_digest ;
  { field_elements = Queue.to_array fields
  ; packeds = Queue.to_array packeds
  }

(** Hash with Poseidon, matching hashPacked(KzgAccumulator, acc). *)
let hash_packed (acc : t) : Step.Field.t =
  let input = to_input acc in
  let packed_fields = Random_oracle.Checked.pack_input input in
  Random_oracle.Checked.hash packed_fields

(** Witness a KzgAccumulator with dummy values. *)
let witness () : t =
  let witness_fpa () =
    let limbs = Array.init 3 ~f:(fun _ ->
      Step.exists Step.Field.typ
        ~compute:(fun () -> Step.Field.Constant.zero)) in
    FF.FpA.of_field3_unsafe (limbs.(0), limbs.(1), limbs.(2))
  in
  let witness_fp12 () = Fp12.witness () in
  let witness_field () =
    Step.exists Step.Field.typ ~compute:(fun () -> Step.Field.Constant.zero)
  in
  let proof =
    { a_x = witness_fpa () ; a_y = witness_fpa ()
    ; neg_b_x = witness_fpa () ; neg_b_y = witness_fpa ()
    ; shift_power = witness_field ()
    ; c = witness_fp12 () ; c_inv = witness_fp12 ()
    ; pi0 = witness_fpa () ; pi1 = witness_fpa ()
    }
  in
  let state =
    { f = witness_fp12 ()
    ; lines_hashes_digest = witness_field ()
    }
  in
  { proof; state }
