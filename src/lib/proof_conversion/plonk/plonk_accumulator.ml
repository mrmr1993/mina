(** In-circuit PLONK Accumulator for recursive proof conversion.

    Reference: nori-proof-conversion/src/plonk/accumulator.ts *)

open! Core_kernel
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
    Queue.enqueue packeds (l0, l) ;
    Queue.enqueue packeds (l1, l) ;
    Queue.enqueue packeds (l2, l)
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
