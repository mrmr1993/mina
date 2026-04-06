(** In-circuit PLONK Accumulator for recursive proof conversion.

    The Accumulator passes through all 24 PLONK circuits, carrying the
    proof data, Fiat-Shamir transcript state, and verification
    intermediate values.

    Each circuit witnesses the Accumulator, hashes it to verify the
    public input, performs computation, then hashes the updated
    Accumulator for the public output.

    The hash uses Poseidon.hashPacked which packs foreign field limbs
    at 88 bits, UInt32 at 32 bits, and Bytes32 as 32 unpacked fields.

    Reference: nori-proof-conversion/src/plonk/accumulator.ts *)

open! Core_kernel
module Step = Pickles.Impls.Step
module FF = Snarky_foreign_field.Foreign_field

(** A Bytes32 is 32 native field elements (each representing a UInt8). *)
type bytes32 = Step.Field.t array

(** In-circuit proof structure.
    Matches Sp1PlonkProof Struct field order exactly. *)
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
  ; l_at_zeta : FF.FpA.t  (* FrC in nori *)
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

(** In-circuit Fiat-Shamir transcript state.
    Matches Sp1PlonkFiatShamir Struct field order.
    Fields are mutable since squeezeGamma/Beta/etc update them. *)
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

(** In-circuit verification state.
    Matches StateUntilPairing Struct field order. *)
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

(** The full Accumulator = proof + fs + state. *)
type t =
  { proof : circuit_proof
  ; fs : circuit_fs
  ; state : circuit_state
  }

(** Build a Random_oracle_input.Chunked.t from the Accumulator,
    matching o1js Struct.toInput() field traversal order.

    FpC/FrC → 3 packed entries of 88 bits each
    Bytes32 → 32 unpacked field elements
    UInt32 → 1 packed entry of 32 bits *)
let to_input (acc : t) : Step.Field.t Random_oracle_input.Chunked.t =
  let fields = Queue.create () in
  let packeds = Queue.create () in
  let l = 88 in
  (* Add a FpA (foreign field, 3 limbs) as 3 packed entries *)
  let add_fpa (x : FF.FpA.t) =
    let l0, l1, l2 = FF.FpA.to_field3 x in
    Queue.enqueue packeds (l0, l) ;
    Queue.enqueue packeds (l1, l) ;
    Queue.enqueue packeds (l2, l)
  in
  (* Add a Bytes32 as 32 unpacked field elements *)
  let add_bytes32 (b : bytes32) =
    Array.iter b ~f:(fun byte -> Queue.enqueue fields byte)
  in
  (* Add a UInt32 as 1 packed entry *)
  let add_uint32 (w : Uint32.t) =
    Queue.enqueue packeds (Uint32.to_field w, 32)
  in
  (* === proof fields (in Struct declaration order) === *)
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
  (* === fs fields === *)
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
  (* === state fields === *)
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
  { field_elements = Queue.to_array fields
  ; packeds = Queue.to_array packeds
  }

(** Hash the Accumulator using Poseidon, matching
    nori's Poseidon.hashPacked(Accumulator, acc). *)
let hash_packed (acc : t) : Step.Field.t =
  let input = to_input acc in
  let packed_fields = Random_oracle.Checked.pack_input input in
  Random_oracle.Checked.hash packed_fields
