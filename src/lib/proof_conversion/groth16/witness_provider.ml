(** Witness provider for Groth16 circuits.

    Supplies proof/VK data to circuit bodies by witnessing Field3 values
    from bignum constants. Each circuit body receives its data through
    closures that capture the proof and VK. *)

module FF = Snarky_foreign_field.Foreign_field
module Step = Pickles.Impls.Step

(** Witness a Field3 from a bignum constant. Each limb is witnessed
    separately to match o1js's allocation pattern. *)
let witness_field3 (v : FF.Bignum_bigint.t) : FF.Field3.t =
  let l0, l1, l2 = FF.Field3.Constant.split v in
  let w big =
    Step.exists Step.Field.typ ~compute:(fun () ->
        FF.bignum_to_field_const big )
  in
  (w l0, w l1, w l2)

(** Witness a G1 point from constant coordinates. *)
let witness_g1 (pt : G1.Constant.t) : G1.Circuit.t =
  { G1.Circuit.x = witness_field3 pt.x
  ; y = witness_field3 pt.y
  }

(** Witness an Fp2 value from constant pair. *)
let witness_fp2 ((c0, c1) : Fp2.Constant.t) : Fp2.Circuit.t =
  { Fp2.Circuit.c0 = witness_field3 c0
  ; c1 = witness_field3 c1
  }

(** Witness a G2 point from constant coordinates. *)
let witness_g2 (pt : G2.Constant.t) : G2.Circuit.t =
  { G2.Circuit.x = witness_fp2 pt.x
  ; y = witness_fp2 pt.y
  }

(** Witness an Fp6 from 3 Fp2 constants. *)
let witness_fp6 ((c0, c1, c2) :
    Fp2.Constant.t * Fp2.Constant.t * Fp2.Constant.t) : Fp6.Circuit.t =
  { Fp6.Circuit.c0 = witness_fp2 c0
  ; c1 = witness_fp2 c1
  ; c2 = witness_fp2 c2
  }

(** Witness an Fp12 from 2 Fp6 constants. *)
let witness_fp12
    ((c0, c1) :
      (Fp2.Constant.t * Fp2.Constant.t * Fp2.Constant.t)
      * (Fp2.Constant.t * Fp2.Constant.t * Fp2.Constant.t)) :
    Fp12.Circuit.t =
  { Fp12.Circuit.c0 = witness_fp6 c0
  ; c1 = witness_fp6 c1
  }

(** Proof data packaged for circuit consumption. *)
type circuit_witness_data =
  { neg_a : G1.Constant.t
  ; b : G2.Constant.t
  ; c : G1.Constant.t
  ; ic : G1.Constant.t array
  ; public_inputs : FF.Bignum_bigint.t array
  }

(** Extract witness data from parsed proof and VK. *)
let make_witness_data ~(proof : Proof_json.proof) ~(vk : Proof_json.vk) :
    circuit_witness_data =
  { neg_a = proof.neg_a
  ; b =
      { x = vk.beta.x  (* Using beta as placeholder for B's G2 type *)
      ; y = vk.beta.y
      }
  ; c = proof.c
  ; ic = vk.ic
  ; public_inputs = proof.public_inputs
  }
