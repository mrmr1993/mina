(** In-circuit PLONK Accumulator for recursive proof conversion.

    Reference: nori-proof-conversion/src/plonk/accumulator.ts *)

open! Core_kernel
open Proof_conversion_bn254
module Step = Pickles.Impls.Step
module FF = Snarky_foreign_field.Foreign_field

let p = Bn254_params.p

let r = Bn254_params.r

type bytes32 = Step.Field.t array

type field3_const = FF.Field3.Constant.t

(** Typ for a UInt8 field element with rangeCheck8.
    Matches o1js UInt8.check: rangeCheckHelper(16, x).assertEquals(x)
    then rangeCheckHelper(16, x*256).assertEquals(x*256). *)
let uint8_typ : (Step.Field.t, Step.Field.Constant.t) Step.Typ.t =
  let (Step.Typ.Typ base) = Step.Field.typ in
  Step.Typ.Typ
    { base with
      check =
        (fun x ->
          Step.make_checked (fun () ->
              (* rangeCheckHelper(16, x).assertEquals(x) *)
              let _a, _b, x0 =
                Pickles.Scalar_challenge.to_field_checked' ~num_bits:16
                  (module Pickles.Impls.Step)
                  { inner = x }
              in
              Step.assert_ (Equal (x0, x)) ;
              (* x256 = x * 256; seal *)
              let x256 =
                FF.seal Step.Field.(scale x (Step.Field.Constant.of_int 256))
              in
              let _a2, _b2, x256_0 =
                Pickles.Scalar_challenge.to_field_checked' ~num_bits:16
                  (module Pickles.Impls.Step)
                  { inner = x256 }
              in
              Step.assert_ (Equal (x256_0, x256)) ) )
    }

let bytes32_typ : (bytes32, Step.Field.Constant.t array) Step.Typ.t =
  Step.Typ.array ~length:32 uint8_typ

(** Typ for a UInt32 field element with rangeCheck32.
    Matches o1js UInt32.check: rangeCheck32(x). *)
let uint32_checked_typ : (Step.Field.t, Step.Field.Constant.t) Step.Typ.t =
  let (Step.Typ.Typ base) = Step.Field.typ in
  Step.Typ.Typ
    { base with
      check =
        (fun x ->
          Step.make_checked (fun () ->
              let _a, _b, x0 =
                Pickles.Scalar_challenge.to_field_checked' ~num_bits:32
                  (module Pickles.Impls.Step)
                  { inner = x }
              in
              Step.assert_ (Equal (x0, x)) ) )
    }

(** Typ for canonical foreign field, returning FpA.t.
    Uses FpC.typ internally, then transports FpC.t ↔ FpA.t.
    Check: multiRangeCheck + assertLessThan (matching nori CanonicalForeignField.check). *)
let fpc_typ : (FF.FpA.t, field3_const) Step.Typ.t =
  Step.Typ.transport_var (FF.FpC.typ ~f:p)
    ~there:(fun (a : FF.FpA.t) -> FF.FpC.of_fpa_unsafe a)
    ~back:(fun (c : FF.FpC.t) -> (c :> FF.FpA.t))

let frc_typ : (FF.FpA.t, field3_const) Step.Typ.t =
  Step.Typ.transport_var (FF.FpC.typ ~f:r)
    ~there:(fun (a : FF.FpA.t) -> FF.FpC.of_fpa_unsafe a)
    ~back:(fun (c : FF.FpC.t) -> (c :> FF.FpA.t))

(** In-circuit proof structure. *)
type circuit_proof =
  { l_com_x : FF.FpA.t
  ; l_com_y : FF.FpA.t
  ; r_com_x : FF.FpA.t
  ; r_com_y : FF.FpA.t
  ; o_com_x : FF.FpA.t
  ; o_com_y : FF.FpA.t
  ; h0_x : FF.FpA.t
  ; h0_y : FF.FpA.t
  ; h1_x : FF.FpA.t
  ; h1_y : FF.FpA.t
  ; h2_x : FF.FpA.t
  ; h2_y : FF.FpA.t
  ; l_at_zeta : FF.FpA.t
  ; r_at_zeta : FF.FpA.t
  ; o_at_zeta : FF.FpA.t
  ; s1_at_zeta : FF.FpA.t
  ; s2_at_zeta : FF.FpA.t
  ; grand_product_x : FF.FpA.t
  ; grand_product_y : FF.FpA.t
  ; grand_product_at_omega_zeta : FF.FpA.t
  ; batch_opening_at_zeta_x : FF.FpA.t
  ; batch_opening_at_zeta_y : FF.FpA.t
  ; batch_opening_at_zeta_omega_x : FF.FpA.t
  ; batch_opening_at_zeta_omega_y : FF.FpA.t
  ; qcp_0_at_zeta : FF.FpA.t
  ; qcp_0_wire_x : FF.FpA.t
  ; qcp_0_wire_y : FF.FpA.t
  }

type proof_const =
  { l_com_x : field3_const
  ; l_com_y : field3_const
  ; r_com_x : field3_const
  ; r_com_y : field3_const
  ; o_com_x : field3_const
  ; o_com_y : field3_const
  ; h0_x : field3_const
  ; h0_y : field3_const
  ; h1_x : field3_const
  ; h1_y : field3_const
  ; h2_x : field3_const
  ; h2_y : field3_const
  ; l_at_zeta : field3_const
  ; r_at_zeta : field3_const
  ; o_at_zeta : field3_const
  ; s1_at_zeta : field3_const
  ; s2_at_zeta : field3_const
  ; grand_product_x : field3_const
  ; grand_product_y : field3_const
  ; grand_product_at_omega_zeta : field3_const
  ; batch_opening_at_zeta_x : field3_const
  ; batch_opening_at_zeta_y : field3_const
  ; batch_opening_at_zeta_omega_x : field3_const
  ; batch_opening_at_zeta_omega_y : field3_const
  ; qcp_0_at_zeta : field3_const
  ; qcp_0_wire_x : field3_const
  ; qcp_0_wire_y : field3_const
  }

(* Fp = base field, Fr = scalar field *)
let proof_typ : (circuit_proof, proof_const) Step.Typ.t =
  let fp = fpc_typ in
  let fr = frc_typ in
  Step.Typ.of_hlistable
    [ fp
    ; fp
    ; fp
    ; fp
    ; fp
    ; fp (* l_com, r_com, o_com *)
    ; fp
    ; fp
    ; fp
    ; fp
    ; fp
    ; fp (* h0, h1, h2 *)
    ; fr
    ; fr
    ; fr (* l/r/o_at_zeta *)
    ; fr
    ; fr (* s1/s2_at_zeta *)
    ; fp
    ; fp (* grand_product *)
    ; fr (* grand_product_at_omega_zeta *)
    ; fp
    ; fp (* batch_opening_at_zeta *)
    ; fp
    ; fp (* batch_opening_at_zeta_omega *)
    ; fr (* qcp_0_at_zeta *)
    ; fp
    ; fp (* qcp_0_wire *)
    ]
    ~var_to_hlist:(fun (p : circuit_proof) ->
      [ p.l_com_x
      ; p.l_com_y
      ; p.r_com_x
      ; p.r_com_y
      ; p.o_com_x
      ; p.o_com_y
      ; p.h0_x
      ; p.h0_y
      ; p.h1_x
      ; p.h1_y
      ; p.h2_x
      ; p.h2_y
      ; p.l_at_zeta
      ; p.r_at_zeta
      ; p.o_at_zeta
      ; p.s1_at_zeta
      ; p.s2_at_zeta
      ; p.grand_product_x
      ; p.grand_product_y
      ; p.grand_product_at_omega_zeta
      ; p.batch_opening_at_zeta_x
      ; p.batch_opening_at_zeta_y
      ; p.batch_opening_at_zeta_omega_x
      ; p.batch_opening_at_zeta_omega_y
      ; p.qcp_0_at_zeta
      ; p.qcp_0_wire_x
      ; p.qcp_0_wire_y
      ] )
    ~var_of_hlist:(fun ([ l_com_x
                        ; l_com_y
                        ; r_com_x
                        ; r_com_y
                        ; o_com_x
                        ; o_com_y
                        ; h0_x
                        ; h0_y
                        ; h1_x
                        ; h1_y
                        ; h2_x
                        ; h2_y
                        ; l_at_zeta
                        ; r_at_zeta
                        ; o_at_zeta
                        ; s1_at_zeta
                        ; s2_at_zeta
                        ; grand_product_x
                        ; grand_product_y
                        ; grand_product_at_omega_zeta
                        ; batch_opening_at_zeta_x
                        ; batch_opening_at_zeta_y
                        ; batch_opening_at_zeta_omega_x
                        ; batch_opening_at_zeta_omega_y
                        ; qcp_0_at_zeta
                        ; qcp_0_wire_x
                        ; qcp_0_wire_y
                        ] :
                         (unit, _) Snarky_backendless.H_list.t ) ->
      { l_com_x
      ; l_com_y
      ; r_com_x
      ; r_com_y
      ; o_com_x
      ; o_com_y
      ; h0_x
      ; h0_y
      ; h1_x
      ; h1_y
      ; h2_x
      ; h2_y
      ; l_at_zeta
      ; r_at_zeta
      ; o_at_zeta
      ; s1_at_zeta
      ; s2_at_zeta
      ; grand_product_x
      ; grand_product_y
      ; grand_product_at_omega_zeta
      ; batch_opening_at_zeta_x
      ; batch_opening_at_zeta_y
      ; batch_opening_at_zeta_omega_x
      ; batch_opening_at_zeta_omega_y
      ; qcp_0_at_zeta
      ; qcp_0_wire_x
      ; qcp_0_wire_y
      } )
    ~value_to_hlist:(fun (p : proof_const) ->
      [ p.l_com_x
      ; p.l_com_y
      ; p.r_com_x
      ; p.r_com_y
      ; p.o_com_x
      ; p.o_com_y
      ; p.h0_x
      ; p.h0_y
      ; p.h1_x
      ; p.h1_y
      ; p.h2_x
      ; p.h2_y
      ; p.l_at_zeta
      ; p.r_at_zeta
      ; p.o_at_zeta
      ; p.s1_at_zeta
      ; p.s2_at_zeta
      ; p.grand_product_x
      ; p.grand_product_y
      ; p.grand_product_at_omega_zeta
      ; p.batch_opening_at_zeta_x
      ; p.batch_opening_at_zeta_y
      ; p.batch_opening_at_zeta_omega_x
      ; p.batch_opening_at_zeta_omega_y
      ; p.qcp_0_at_zeta
      ; p.qcp_0_wire_x
      ; p.qcp_0_wire_y
      ] )
    ~value_of_hlist:(fun ([ l_com_x
                          ; l_com_y
                          ; r_com_x
                          ; r_com_y
                          ; o_com_x
                          ; o_com_y
                          ; h0_x
                          ; h0_y
                          ; h1_x
                          ; h1_y
                          ; h2_x
                          ; h2_y
                          ; l_at_zeta
                          ; r_at_zeta
                          ; o_at_zeta
                          ; s1_at_zeta
                          ; s2_at_zeta
                          ; grand_product_x
                          ; grand_product_y
                          ; grand_product_at_omega_zeta
                          ; batch_opening_at_zeta_x
                          ; batch_opening_at_zeta_y
                          ; batch_opening_at_zeta_omega_x
                          ; batch_opening_at_zeta_omega_y
                          ; qcp_0_at_zeta
                          ; qcp_0_wire_x
                          ; qcp_0_wire_y
                          ] :
                           (unit, _) Snarky_backendless.H_list.t ) ->
      { l_com_x
      ; l_com_y
      ; r_com_x
      ; r_com_y
      ; o_com_x
      ; o_com_y
      ; h0_x
      ; h0_y
      ; h1_x
      ; h1_y
      ; h2_x
      ; h2_y
      ; l_at_zeta
      ; r_at_zeta
      ; o_at_zeta
      ; s1_at_zeta
      ; s2_at_zeta
      ; grand_product_x
      ; grand_product_y
      ; grand_product_at_omega_zeta
      ; batch_opening_at_zeta_x
      ; batch_opening_at_zeta_y
      ; batch_opening_at_zeta_omega_x
      ; batch_opening_at_zeta_omega_y
      ; qcp_0_at_zeta
      ; qcp_0_wire_x
      ; qcp_0_wire_y
      } )

(** Fiat-Shamir transcript state. *)
type circuit_fs =
  { mutable gamma_digest : bytes32
  ; mutable gamma : FF.FpA.t
  ; mutable beta_digest : bytes32
  ; mutable beta : FF.FpA.t
  ; mutable alpha_digest : bytes32
  ; mutable alpha : FF.FpA.t
  ; mutable zeta_digest : bytes32
  ; mutable zeta : FF.FpA.t
  ; mutable gamma_kzg_digest : bytes32
  ; mutable gamma_kzg : FF.FpA.t
  }

type fs_const =
  { gamma_digest : Step.Field.Constant.t array
  ; gamma : field3_const
  ; beta_digest : Step.Field.Constant.t array
  ; beta : field3_const
  ; alpha_digest : Step.Field.Constant.t array
  ; alpha : field3_const
  ; zeta_digest : Step.Field.Constant.t array
  ; zeta : field3_const
  ; gamma_kzg_digest : Step.Field.Constant.t array
  ; gamma_kzg : field3_const
  }

let fs_typ : (circuit_fs, fs_const) Step.Typ.t =
  let b = bytes32_typ in
  let fr = frc_typ in
  Step.Typ.of_hlistable
    [ b; fr; b; fr; b; fr; b; fr; b; fr ]
    ~var_to_hlist:(fun (f : circuit_fs) ->
      [ f.gamma_digest
      ; f.gamma
      ; f.beta_digest
      ; f.beta
      ; f.alpha_digest
      ; f.alpha
      ; f.zeta_digest
      ; f.zeta
      ; f.gamma_kzg_digest
      ; f.gamma_kzg
      ] )
    ~var_of_hlist:(fun ([ gamma_digest
                        ; gamma
                        ; beta_digest
                        ; beta
                        ; alpha_digest
                        ; alpha
                        ; zeta_digest
                        ; zeta
                        ; gamma_kzg_digest
                        ; gamma_kzg
                        ] :
                         (unit, _) Snarky_backendless.H_list.t ) ->
      { gamma_digest
      ; gamma
      ; beta_digest
      ; beta
      ; alpha_digest
      ; alpha
      ; zeta_digest
      ; zeta
      ; gamma_kzg_digest
      ; gamma_kzg
      } )
    ~value_to_hlist:(fun (f : fs_const) ->
      [ f.gamma_digest
      ; f.gamma
      ; f.beta_digest
      ; f.beta
      ; f.alpha_digest
      ; f.alpha
      ; f.zeta_digest
      ; f.zeta
      ; f.gamma_kzg_digest
      ; f.gamma_kzg
      ] )
    ~value_of_hlist:(fun ([ gamma_digest
                          ; gamma
                          ; beta_digest
                          ; beta
                          ; alpha_digest
                          ; alpha
                          ; zeta_digest
                          ; zeta
                          ; gamma_kzg_digest
                          ; gamma_kzg
                          ] :
                           (unit, _) Snarky_backendless.H_list.t ) ->
      { gamma_digest
      ; gamma
      ; beta_digest
      ; beta
      ; alpha_digest
      ; alpha
      ; zeta_digest
      ; zeta
      ; gamma_kzg_digest
      ; gamma_kzg
      } )

(** Verification state. *)
type circuit_state =
  { mutable pi0 : FF.FpA.t
  ; mutable pi1 : FF.FpA.t
  ; mutable zeta_pow_n : FF.FpA.t
  ; mutable zh_eval : FF.FpA.t
  ; mutable alpha_2_l0 : FF.FpA.t
  ; mutable hx : FF.FpA.t
  ; mutable hy : FF.FpA.t
  ; mutable pi : FF.FpA.t
  ; mutable linearized_opening : FF.FpA.t
  ; mutable lcm_x : FF.FpA.t
  ; mutable lcm_y : FF.FpA.t
  ; mutable cm_x : FF.FpA.t
  ; mutable cm_y : FF.FpA.t
  ; mutable cm_opening : FF.FpA.t
  ; mutable kzg_random : FF.FpA.t
  ; mutable kzg_cm_x : FF.FpA.t
  ; mutable kzg_cm_y : FF.FpA.t
  ; mutable neg_fq_x : FF.FpA.t
  ; mutable neg_fq_y : FF.FpA.t
  ; mutable h_state : Uint32.t array
  }

type state_const =
  { pi0 : field3_const
  ; pi1 : field3_const
  ; zeta_pow_n : field3_const
  ; zh_eval : field3_const
  ; alpha_2_l0 : field3_const
  ; hx : field3_const
  ; hy : field3_const
  ; pi : field3_const
  ; linearized_opening : field3_const
  ; lcm_x : field3_const
  ; lcm_y : field3_const
  ; cm_x : field3_const
  ; cm_y : field3_const
  ; cm_opening : field3_const
  ; kzg_random : field3_const
  ; kzg_cm_x : field3_const
  ; kzg_cm_y : field3_const
  ; neg_fq_x : field3_const
  ; neg_fq_y : field3_const
  ; h_state : Step.Field.Constant.t array
  }

let uint32_array_typ : (Uint32.t array, Step.Field.Constant.t array) Step.Typ.t
    =
  Step.Typ.array ~length:8 uint32_checked_typ

let state_typ : (circuit_state, state_const) Step.Typ.t =
  let fr = frc_typ in
  let fp = fpc_typ in
  Step.Typ.of_hlistable
    [ fr
    ; fr (* pi0, pi1 *)
    ; fr
    ; fr
    ; fr (* zeta_pow_n, zh_eval, alpha_2_l0 *)
    ; fp
    ; fp (* hx, hy *)
    ; fr
    ; fr (* pi, linearized_opening *)
    ; fp
    ; fp
    ; fp
    ; fp (* lcm_x/y, cm_x/y *)
    ; fr
    ; fr (* cm_opening, kzg_random *)
    ; fp
    ; fp
    ; fp
    ; fp (* kzg_cm_x/y, neg_fq_x/y *)
    ; uint32_array_typ (* h_state *)
    ]
    ~var_to_hlist:(fun (s : circuit_state) ->
      [ s.pi0
      ; s.pi1
      ; s.zeta_pow_n
      ; s.zh_eval
      ; s.alpha_2_l0
      ; s.hx
      ; s.hy
      ; s.pi
      ; s.linearized_opening
      ; s.lcm_x
      ; s.lcm_y
      ; s.cm_x
      ; s.cm_y
      ; s.cm_opening
      ; s.kzg_random
      ; s.kzg_cm_x
      ; s.kzg_cm_y
      ; s.neg_fq_x
      ; s.neg_fq_y
      ; s.h_state
      ] )
    ~var_of_hlist:(fun ([ pi0
                        ; pi1
                        ; zeta_pow_n
                        ; zh_eval
                        ; alpha_2_l0
                        ; hx
                        ; hy
                        ; pi
                        ; linearized_opening
                        ; lcm_x
                        ; lcm_y
                        ; cm_x
                        ; cm_y
                        ; cm_opening
                        ; kzg_random
                        ; kzg_cm_x
                        ; kzg_cm_y
                        ; neg_fq_x
                        ; neg_fq_y
                        ; h_state
                        ] :
                         (unit, _) Snarky_backendless.H_list.t ) ->
      { pi0
      ; pi1
      ; zeta_pow_n
      ; zh_eval
      ; alpha_2_l0
      ; hx
      ; hy
      ; pi
      ; linearized_opening
      ; lcm_x
      ; lcm_y
      ; cm_x
      ; cm_y
      ; cm_opening
      ; kzg_random
      ; kzg_cm_x
      ; kzg_cm_y
      ; neg_fq_x
      ; neg_fq_y
      ; h_state
      } )
    ~value_to_hlist:(fun (s : state_const) ->
      [ s.pi0
      ; s.pi1
      ; s.zeta_pow_n
      ; s.zh_eval
      ; s.alpha_2_l0
      ; s.hx
      ; s.hy
      ; s.pi
      ; s.linearized_opening
      ; s.lcm_x
      ; s.lcm_y
      ; s.cm_x
      ; s.cm_y
      ; s.cm_opening
      ; s.kzg_random
      ; s.kzg_cm_x
      ; s.kzg_cm_y
      ; s.neg_fq_x
      ; s.neg_fq_y
      ; s.h_state
      ] )
    ~value_of_hlist:(fun ([ pi0
                          ; pi1
                          ; zeta_pow_n
                          ; zh_eval
                          ; alpha_2_l0
                          ; hx
                          ; hy
                          ; pi
                          ; linearized_opening
                          ; lcm_x
                          ; lcm_y
                          ; cm_x
                          ; cm_y
                          ; cm_opening
                          ; kzg_random
                          ; kzg_cm_x
                          ; kzg_cm_y
                          ; neg_fq_x
                          ; neg_fq_y
                          ; h_state
                          ] :
                           (unit, _) Snarky_backendless.H_list.t ) ->
      { pi0
      ; pi1
      ; zeta_pow_n
      ; zh_eval
      ; alpha_2_l0
      ; hx
      ; hy
      ; pi
      ; linearized_opening
      ; lcm_x
      ; lcm_y
      ; cm_x
      ; cm_y
      ; cm_opening
      ; kzg_random
      ; kzg_cm_x
      ; kzg_cm_y
      ; neg_fq_x
      ; neg_fq_y
      ; h_state
      } )

(** Full Accumulator. *)
type t = { proof : circuit_proof; fs : circuit_fs; state : circuit_state }

type t_const = { proof : proof_const; fs : fs_const; state : state_const }

let typ : (t, t_const) Step.Typ.t =
  Step.Typ.of_hlistable
    [ proof_typ; fs_typ; state_typ ]
    ~var_to_hlist:(fun (a : t) -> [ a.proof; a.fs; a.state ])
    ~var_of_hlist:(fun ([ proof; fs; state ] :
                         (unit, _) Snarky_backendless.H_list.t ) ->
      { proof; fs; state } )
    ~value_to_hlist:(fun (a : t_const) -> [ a.proof; a.fs; a.state ])
    ~value_of_hlist:(fun ([ proof; fs; state ] :
                           (unit, _) Snarky_backendless.H_list.t ) ->
      { proof; fs; state } )

(** Inject a constant accumulator as circuit variables using [Cvar.constant].
    No variable allocation, no type-check constraints — O(1) overhead.
    Used by [compute-state] to avoid the cost of [Step.exists]. *)
let of_constant (c : t_const) : t = Step.constant typ c

(** Build Random_oracle_input.Chunked.t from Accumulator. *)
let to_input (acc : t) : Step.Field.t Random_oracle_input.Chunked.t =
  let fields = Queue.create () in
  let packeds = Queue.create () in
  let l = 88 in
  let add_fpa (x : FF.FpA.t) =
    let l0, l1, l2 = FF.FpA.to_field3 x in
    Queue.enqueue packeds (FF.Limb.to_field l0, l) ;
    Queue.enqueue packeds (FF.Limb.to_field l1, l) ;
    Queue.enqueue packeds (FF.Limb.to_field l2, l)
  in
  let add_bytes32 (b : bytes32) =
    (* Each UInt8 → packed entry of 8 bits, matching o1js UInt8.toInput *)
    Array.iter b ~f:(fun byte -> Queue.enqueue packeds (byte, 8))
  in
  let add_uint32 (w : Uint32.t) =
    Queue.enqueue packeds (Uint32.to_field w, 32)
  in
  (* proof *)
  add_fpa acc.proof.l_com_x ;
  add_fpa acc.proof.l_com_y ;
  add_fpa acc.proof.r_com_x ;
  add_fpa acc.proof.r_com_y ;
  add_fpa acc.proof.o_com_x ;
  add_fpa acc.proof.o_com_y ;
  add_fpa acc.proof.h0_x ;
  add_fpa acc.proof.h0_y ;
  add_fpa acc.proof.h1_x ;
  add_fpa acc.proof.h1_y ;
  add_fpa acc.proof.h2_x ;
  add_fpa acc.proof.h2_y ;
  add_fpa acc.proof.l_at_zeta ;
  add_fpa acc.proof.r_at_zeta ;
  add_fpa acc.proof.o_at_zeta ;
  add_fpa acc.proof.s1_at_zeta ;
  add_fpa acc.proof.s2_at_zeta ;
  add_fpa acc.proof.grand_product_x ;
  add_fpa acc.proof.grand_product_y ;
  add_fpa acc.proof.grand_product_at_omega_zeta ;
  add_fpa acc.proof.batch_opening_at_zeta_x ;
  add_fpa acc.proof.batch_opening_at_zeta_y ;
  add_fpa acc.proof.batch_opening_at_zeta_omega_x ;
  add_fpa acc.proof.batch_opening_at_zeta_omega_y ;
  add_fpa acc.proof.qcp_0_at_zeta ;
  add_fpa acc.proof.qcp_0_wire_x ;
  add_fpa acc.proof.qcp_0_wire_y ;
  (* fs *)
  add_bytes32 acc.fs.gamma_digest ;
  add_fpa acc.fs.gamma ;
  add_bytes32 acc.fs.beta_digest ;
  add_fpa acc.fs.beta ;
  add_bytes32 acc.fs.alpha_digest ;
  add_fpa acc.fs.alpha ;
  add_bytes32 acc.fs.zeta_digest ;
  add_fpa acc.fs.zeta ;
  add_bytes32 acc.fs.gamma_kzg_digest ;
  add_fpa acc.fs.gamma_kzg ;
  (* state *)
  add_fpa acc.state.pi0 ;
  add_fpa acc.state.pi1 ;
  add_fpa acc.state.zeta_pow_n ;
  add_fpa acc.state.zh_eval ;
  add_fpa acc.state.alpha_2_l0 ;
  add_fpa acc.state.hx ;
  add_fpa acc.state.hy ;
  add_fpa acc.state.pi ;
  add_fpa acc.state.linearized_opening ;
  add_fpa acc.state.lcm_x ;
  add_fpa acc.state.lcm_y ;
  add_fpa acc.state.cm_x ;
  add_fpa acc.state.cm_y ;
  add_fpa acc.state.cm_opening ;
  add_fpa acc.state.kzg_random ;
  add_fpa acc.state.kzg_cm_x ;
  add_fpa acc.state.kzg_cm_y ;
  add_fpa acc.state.neg_fq_x ;
  add_fpa acc.state.neg_fq_y ;
  Array.iter acc.state.h_state ~f:add_uint32 ;
  { field_elements = Queue.to_array fields; packeds = Queue.to_array packeds }

let hash_packed (acc : t) : Step.Field.t =
  let input = to_input acc in
  let packed_fields = Random_oracle.Checked.pack_input input in
  Random_oracle.Checked.hash packed_fields

(** Default constant value for exists. *)
let default_const : t_const =
  let z3 = Bignum_bigint.zero in
  let z32 = Array.create ~len:32 Step.Field.Constant.zero in
  let z8 = Array.create ~len:8 Step.Field.Constant.zero in
  { proof =
      { l_com_x = z3
      ; l_com_y = z3
      ; r_com_x = z3
      ; r_com_y = z3
      ; o_com_x = z3
      ; o_com_y = z3
      ; h0_x = z3
      ; h0_y = z3
      ; h1_x = z3
      ; h1_y = z3
      ; h2_x = z3
      ; h2_y = z3
      ; l_at_zeta = z3
      ; r_at_zeta = z3
      ; o_at_zeta = z3
      ; s1_at_zeta = z3
      ; s2_at_zeta = z3
      ; grand_product_x = z3
      ; grand_product_y = z3
      ; grand_product_at_omega_zeta = z3
      ; batch_opening_at_zeta_x = z3
      ; batch_opening_at_zeta_y = z3
      ; batch_opening_at_zeta_omega_x = z3
      ; batch_opening_at_zeta_omega_y = z3
      ; qcp_0_at_zeta = z3
      ; qcp_0_wire_x = z3
      ; qcp_0_wire_y = z3
      }
  ; fs =
      { gamma_digest = z32
      ; gamma = z3
      ; beta_digest = z32
      ; beta = z3
      ; alpha_digest = z32
      ; alpha = z3
      ; zeta_digest = z32
      ; zeta = z3
      ; gamma_kzg_digest = z32
      ; gamma_kzg = z3
      }
  ; state =
      { pi0 = z3
      ; pi1 = z3
      ; zeta_pow_n = z3
      ; zh_eval = z3
      ; alpha_2_l0 = z3
      ; hx = z3
      ; hy = z3
      ; pi = z3
      ; linearized_opening = z3
      ; lcm_x = z3
      ; lcm_y = z3
      ; cm_x = z3
      ; cm_y = z3
      ; cm_opening = z3
      ; kzg_random = z3
      ; kzg_cm_x = z3
      ; kzg_cm_y = z3
      ; neg_fq_x = z3
      ; neg_fq_y = z3
      ; h_state = z8
      }
  }

(** String-leaved, named mirror of {!t_const} for transfer across a process
    boundary. Every foreign-field element becomes a decimal string and every
    digest an array of field-element strings, so the wire form holds only
    primitives — no abstract crypto types. The field layout mirrors
    {!t_const} exactly. *)
module Wire = struct
  type proof =
    { l_com_x : string
    ; l_com_y : string
    ; r_com_x : string
    ; r_com_y : string
    ; o_com_x : string
    ; o_com_y : string
    ; h0_x : string
    ; h0_y : string
    ; h1_x : string
    ; h1_y : string
    ; h2_x : string
    ; h2_y : string
    ; l_at_zeta : string
    ; r_at_zeta : string
    ; o_at_zeta : string
    ; s1_at_zeta : string
    ; s2_at_zeta : string
    ; grand_product_x : string
    ; grand_product_y : string
    ; grand_product_at_omega_zeta : string
    ; batch_opening_at_zeta_x : string
    ; batch_opening_at_zeta_y : string
    ; batch_opening_at_zeta_omega_x : string
    ; batch_opening_at_zeta_omega_y : string
    ; qcp_0_at_zeta : string
    ; qcp_0_wire_x : string
    ; qcp_0_wire_y : string
    }

  type fs =
    { gamma_digest : string array
    ; gamma : string
    ; beta_digest : string array
    ; beta : string
    ; alpha_digest : string array
    ; alpha : string
    ; zeta_digest : string array
    ; zeta : string
    ; gamma_kzg_digest : string array
    ; gamma_kzg : string
    }

  type state =
    { pi0 : string
    ; pi1 : string
    ; zeta_pow_n : string
    ; zh_eval : string
    ; alpha_2_l0 : string
    ; hx : string
    ; hy : string
    ; pi : string
    ; linearized_opening : string
    ; lcm_x : string
    ; lcm_y : string
    ; cm_x : string
    ; cm_y : string
    ; cm_opening : string
    ; kzg_random : string
    ; kzg_cm_x : string
    ; kzg_cm_y : string
    ; neg_fq_x : string
    ; neg_fq_y : string
    ; h_state : string array
    }

  type t = { proof : proof; fs : fs; state : state }

  let to_json (w : t) : Yojson.Safe.t =
    let s x : Yojson.Safe.t = `String x in
    let sa a : Yojson.Safe.t =
      `List
        (Array.to_list (Array.map a ~f:(fun x : Yojson.Safe.t -> `String x)))
    in
    `Assoc
      [ ( "proof"
        , `Assoc
            [ ("l_com_x", s w.proof.l_com_x)
            ; ("l_com_y", s w.proof.l_com_y)
            ; ("r_com_x", s w.proof.r_com_x)
            ; ("r_com_y", s w.proof.r_com_y)
            ; ("o_com_x", s w.proof.o_com_x)
            ; ("o_com_y", s w.proof.o_com_y)
            ; ("h0_x", s w.proof.h0_x)
            ; ("h0_y", s w.proof.h0_y)
            ; ("h1_x", s w.proof.h1_x)
            ; ("h1_y", s w.proof.h1_y)
            ; ("h2_x", s w.proof.h2_x)
            ; ("h2_y", s w.proof.h2_y)
            ; ("l_at_zeta", s w.proof.l_at_zeta)
            ; ("r_at_zeta", s w.proof.r_at_zeta)
            ; ("o_at_zeta", s w.proof.o_at_zeta)
            ; ("s1_at_zeta", s w.proof.s1_at_zeta)
            ; ("s2_at_zeta", s w.proof.s2_at_zeta)
            ; ("grand_product_x", s w.proof.grand_product_x)
            ; ("grand_product_y", s w.proof.grand_product_y)
            ; ( "grand_product_at_omega_zeta"
              , s w.proof.grand_product_at_omega_zeta )
            ; ("batch_opening_at_zeta_x", s w.proof.batch_opening_at_zeta_x)
            ; ("batch_opening_at_zeta_y", s w.proof.batch_opening_at_zeta_y)
            ; ( "batch_opening_at_zeta_omega_x"
              , s w.proof.batch_opening_at_zeta_omega_x )
            ; ( "batch_opening_at_zeta_omega_y"
              , s w.proof.batch_opening_at_zeta_omega_y )
            ; ("qcp_0_at_zeta", s w.proof.qcp_0_at_zeta)
            ; ("qcp_0_wire_x", s w.proof.qcp_0_wire_x)
            ; ("qcp_0_wire_y", s w.proof.qcp_0_wire_y)
            ] )
      ; ( "fs"
        , `Assoc
            [ ("gamma_digest", sa w.fs.gamma_digest)
            ; ("gamma", s w.fs.gamma)
            ; ("beta_digest", sa w.fs.beta_digest)
            ; ("beta", s w.fs.beta)
            ; ("alpha_digest", sa w.fs.alpha_digest)
            ; ("alpha", s w.fs.alpha)
            ; ("zeta_digest", sa w.fs.zeta_digest)
            ; ("zeta", s w.fs.zeta)
            ; ("gamma_kzg_digest", sa w.fs.gamma_kzg_digest)
            ; ("gamma_kzg", s w.fs.gamma_kzg)
            ] )
      ; ( "state"
        , `Assoc
            [ ("pi0", s w.state.pi0)
            ; ("pi1", s w.state.pi1)
            ; ("zeta_pow_n", s w.state.zeta_pow_n)
            ; ("zh_eval", s w.state.zh_eval)
            ; ("alpha_2_l0", s w.state.alpha_2_l0)
            ; ("hx", s w.state.hx)
            ; ("hy", s w.state.hy)
            ; ("pi", s w.state.pi)
            ; ("linearized_opening", s w.state.linearized_opening)
            ; ("lcm_x", s w.state.lcm_x)
            ; ("lcm_y", s w.state.lcm_y)
            ; ("cm_x", s w.state.cm_x)
            ; ("cm_y", s w.state.cm_y)
            ; ("cm_opening", s w.state.cm_opening)
            ; ("kzg_random", s w.state.kzg_random)
            ; ("kzg_cm_x", s w.state.kzg_cm_x)
            ; ("kzg_cm_y", s w.state.kzg_cm_y)
            ; ("neg_fq_x", s w.state.neg_fq_x)
            ; ("neg_fq_y", s w.state.neg_fq_y)
            ; ("h_state", sa w.state.h_state)
            ] )
      ]

  let of_json (j : Yojson.Safe.t) : t =
    let open Yojson.Safe.Util in
    let sa j = to_list j |> List.map ~f:to_string |> Array.of_list in
    let proof = member "proof" j in
    let fs = member "fs" j in
    let state = member "state" j in
    let ps k = to_string (member k proof) in
    let fss k = to_string (member k fs) in
    let fsa k = sa (member k fs) in
    let sts k = to_string (member k state) in
    { proof =
        { l_com_x = ps "l_com_x"
        ; l_com_y = ps "l_com_y"
        ; r_com_x = ps "r_com_x"
        ; r_com_y = ps "r_com_y"
        ; o_com_x = ps "o_com_x"
        ; o_com_y = ps "o_com_y"
        ; h0_x = ps "h0_x"
        ; h0_y = ps "h0_y"
        ; h1_x = ps "h1_x"
        ; h1_y = ps "h1_y"
        ; h2_x = ps "h2_x"
        ; h2_y = ps "h2_y"
        ; l_at_zeta = ps "l_at_zeta"
        ; r_at_zeta = ps "r_at_zeta"
        ; o_at_zeta = ps "o_at_zeta"
        ; s1_at_zeta = ps "s1_at_zeta"
        ; s2_at_zeta = ps "s2_at_zeta"
        ; grand_product_x = ps "grand_product_x"
        ; grand_product_y = ps "grand_product_y"
        ; grand_product_at_omega_zeta = ps "grand_product_at_omega_zeta"
        ; batch_opening_at_zeta_x = ps "batch_opening_at_zeta_x"
        ; batch_opening_at_zeta_y = ps "batch_opening_at_zeta_y"
        ; batch_opening_at_zeta_omega_x = ps "batch_opening_at_zeta_omega_x"
        ; batch_opening_at_zeta_omega_y = ps "batch_opening_at_zeta_omega_y"
        ; qcp_0_at_zeta = ps "qcp_0_at_zeta"
        ; qcp_0_wire_x = ps "qcp_0_wire_x"
        ; qcp_0_wire_y = ps "qcp_0_wire_y"
        }
    ; fs =
        { gamma_digest = fsa "gamma_digest"
        ; gamma = fss "gamma"
        ; beta_digest = fsa "beta_digest"
        ; beta = fss "beta"
        ; alpha_digest = fsa "alpha_digest"
        ; alpha = fss "alpha"
        ; zeta_digest = fsa "zeta_digest"
        ; zeta = fss "zeta"
        ; gamma_kzg_digest = fsa "gamma_kzg_digest"
        ; gamma_kzg = fss "gamma_kzg"
        }
    ; state =
        { pi0 = sts "pi0"
        ; pi1 = sts "pi1"
        ; zeta_pow_n = sts "zeta_pow_n"
        ; zh_eval = sts "zh_eval"
        ; alpha_2_l0 = sts "alpha_2_l0"
        ; hx = sts "hx"
        ; hy = sts "hy"
        ; pi = sts "pi"
        ; linearized_opening = sts "linearized_opening"
        ; lcm_x = sts "lcm_x"
        ; lcm_y = sts "lcm_y"
        ; cm_x = sts "cm_x"
        ; cm_y = sts "cm_y"
        ; cm_opening = sts "cm_opening"
        ; kzg_random = sts "kzg_random"
        ; kzg_cm_x = sts "kzg_cm_x"
        ; kzg_cm_y = sts "kzg_cm_y"
        ; neg_fq_x = sts "neg_fq_x"
        ; neg_fq_y = sts "neg_fq_y"
        ; h_state = sa (member "h_state" state)
        }
    }
end

(** Reduce an accumulator constant to its string-leaved {!Wire.t} form. *)
let to_wire (c : t_const) : Wire.t =
  let bi = Bignum_bigint.to_string in
  let fa = Array.map ~f:Step.Field.Constant.to_string in
  { Wire.proof =
      { Wire.l_com_x = bi c.proof.l_com_x
      ; l_com_y = bi c.proof.l_com_y
      ; r_com_x = bi c.proof.r_com_x
      ; r_com_y = bi c.proof.r_com_y
      ; o_com_x = bi c.proof.o_com_x
      ; o_com_y = bi c.proof.o_com_y
      ; h0_x = bi c.proof.h0_x
      ; h0_y = bi c.proof.h0_y
      ; h1_x = bi c.proof.h1_x
      ; h1_y = bi c.proof.h1_y
      ; h2_x = bi c.proof.h2_x
      ; h2_y = bi c.proof.h2_y
      ; l_at_zeta = bi c.proof.l_at_zeta
      ; r_at_zeta = bi c.proof.r_at_zeta
      ; o_at_zeta = bi c.proof.o_at_zeta
      ; s1_at_zeta = bi c.proof.s1_at_zeta
      ; s2_at_zeta = bi c.proof.s2_at_zeta
      ; grand_product_x = bi c.proof.grand_product_x
      ; grand_product_y = bi c.proof.grand_product_y
      ; grand_product_at_omega_zeta = bi c.proof.grand_product_at_omega_zeta
      ; batch_opening_at_zeta_x = bi c.proof.batch_opening_at_zeta_x
      ; batch_opening_at_zeta_y = bi c.proof.batch_opening_at_zeta_y
      ; batch_opening_at_zeta_omega_x = bi c.proof.batch_opening_at_zeta_omega_x
      ; batch_opening_at_zeta_omega_y = bi c.proof.batch_opening_at_zeta_omega_y
      ; qcp_0_at_zeta = bi c.proof.qcp_0_at_zeta
      ; qcp_0_wire_x = bi c.proof.qcp_0_wire_x
      ; qcp_0_wire_y = bi c.proof.qcp_0_wire_y
      }
  ; fs =
      { Wire.gamma_digest = fa c.fs.gamma_digest
      ; gamma = bi c.fs.gamma
      ; beta_digest = fa c.fs.beta_digest
      ; beta = bi c.fs.beta
      ; alpha_digest = fa c.fs.alpha_digest
      ; alpha = bi c.fs.alpha
      ; zeta_digest = fa c.fs.zeta_digest
      ; zeta = bi c.fs.zeta
      ; gamma_kzg_digest = fa c.fs.gamma_kzg_digest
      ; gamma_kzg = bi c.fs.gamma_kzg
      }
  ; state =
      { Wire.pi0 = bi c.state.pi0
      ; pi1 = bi c.state.pi1
      ; zeta_pow_n = bi c.state.zeta_pow_n
      ; zh_eval = bi c.state.zh_eval
      ; alpha_2_l0 = bi c.state.alpha_2_l0
      ; hx = bi c.state.hx
      ; hy = bi c.state.hy
      ; pi = bi c.state.pi
      ; linearized_opening = bi c.state.linearized_opening
      ; lcm_x = bi c.state.lcm_x
      ; lcm_y = bi c.state.lcm_y
      ; cm_x = bi c.state.cm_x
      ; cm_y = bi c.state.cm_y
      ; cm_opening = bi c.state.cm_opening
      ; kzg_random = bi c.state.kzg_random
      ; kzg_cm_x = bi c.state.kzg_cm_x
      ; kzg_cm_y = bi c.state.kzg_cm_y
      ; neg_fq_x = bi c.state.neg_fq_x
      ; neg_fq_y = bi c.state.neg_fq_y
      ; h_state = fa c.state.h_state
      }
  }

(** Reconstruct an accumulator constant from its {!Wire.t} form. *)
let of_wire (w : Wire.t) : t_const =
  let bi = Bignum_bigint.of_string in
  let fa = Array.map ~f:Step.Field.Constant.of_string in
  { proof =
      { l_com_x = bi w.proof.l_com_x
      ; l_com_y = bi w.proof.l_com_y
      ; r_com_x = bi w.proof.r_com_x
      ; r_com_y = bi w.proof.r_com_y
      ; o_com_x = bi w.proof.o_com_x
      ; o_com_y = bi w.proof.o_com_y
      ; h0_x = bi w.proof.h0_x
      ; h0_y = bi w.proof.h0_y
      ; h1_x = bi w.proof.h1_x
      ; h1_y = bi w.proof.h1_y
      ; h2_x = bi w.proof.h2_x
      ; h2_y = bi w.proof.h2_y
      ; l_at_zeta = bi w.proof.l_at_zeta
      ; r_at_zeta = bi w.proof.r_at_zeta
      ; o_at_zeta = bi w.proof.o_at_zeta
      ; s1_at_zeta = bi w.proof.s1_at_zeta
      ; s2_at_zeta = bi w.proof.s2_at_zeta
      ; grand_product_x = bi w.proof.grand_product_x
      ; grand_product_y = bi w.proof.grand_product_y
      ; grand_product_at_omega_zeta = bi w.proof.grand_product_at_omega_zeta
      ; batch_opening_at_zeta_x = bi w.proof.batch_opening_at_zeta_x
      ; batch_opening_at_zeta_y = bi w.proof.batch_opening_at_zeta_y
      ; batch_opening_at_zeta_omega_x = bi w.proof.batch_opening_at_zeta_omega_x
      ; batch_opening_at_zeta_omega_y = bi w.proof.batch_opening_at_zeta_omega_y
      ; qcp_0_at_zeta = bi w.proof.qcp_0_at_zeta
      ; qcp_0_wire_x = bi w.proof.qcp_0_wire_x
      ; qcp_0_wire_y = bi w.proof.qcp_0_wire_y
      }
  ; fs =
      { gamma_digest = fa w.fs.gamma_digest
      ; gamma = bi w.fs.gamma
      ; beta_digest = fa w.fs.beta_digest
      ; beta = bi w.fs.beta
      ; alpha_digest = fa w.fs.alpha_digest
      ; alpha = bi w.fs.alpha
      ; zeta_digest = fa w.fs.zeta_digest
      ; zeta = bi w.fs.zeta
      ; gamma_kzg_digest = fa w.fs.gamma_kzg_digest
      ; gamma_kzg = bi w.fs.gamma_kzg
      }
  ; state =
      { pi0 = bi w.state.pi0
      ; pi1 = bi w.state.pi1
      ; zeta_pow_n = bi w.state.zeta_pow_n
      ; zh_eval = bi w.state.zh_eval
      ; alpha_2_l0 = bi w.state.alpha_2_l0
      ; hx = bi w.state.hx
      ; hy = bi w.state.hy
      ; pi = bi w.state.pi
      ; linearized_opening = bi w.state.linearized_opening
      ; lcm_x = bi w.state.lcm_x
      ; lcm_y = bi w.state.lcm_y
      ; cm_x = bi w.state.cm_x
      ; cm_y = bi w.state.cm_y
      ; cm_opening = bi w.state.cm_opening
      ; kzg_random = bi w.state.kzg_random
      ; kzg_cm_x = bi w.state.kzg_cm_x
      ; kzg_cm_y = bi w.state.kzg_cm_y
      ; neg_fq_x = bi w.state.neg_fq_x
      ; neg_fq_y = bi w.state.neg_fq_y
      ; h_state = fa w.state.h_state
      }
  }
