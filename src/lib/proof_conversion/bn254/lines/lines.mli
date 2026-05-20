(** Line coefficients for BN254 pairing computation. *)

module FF = Snarky_foreign_field.Foreign_field
module Step = Pickles.Impls.Step

module G2Line : sig
  type t = { lambda : Fp2.Circuit.t; neg_mu : Fp2.Circuit.t }

  type constant = Fp2.Constant.t * Fp2.Constant.t

  val typ : (t, constant) Step.Typ.t

  (** Embed a constant line as a circuit value. *)
  val of_constant : constant -> t

  (** Evaluate the line at a G2 point. *)
  val evaluate : t -> G2.Circuit.t -> Fp2.Circuit.t

  (** Assert that a line passes through two G2 points. *)
  val assert_is_line : t -> G2.Circuit.t -> G2.Circuit.t -> unit

  (** Assert that a line is tangent to the curve at a point. *)
  val assert_is_tangent : t -> G2.Circuit.t -> unit

  (** Evaluate a line into a sparse Fp12 element. *)
  val psi : t -> x_over_y:FF.FpA.t -> y_inv:FF.FpA.t -> Fp12.Circuit.t
end

module AffineCache : sig
  type t = { x_over_y : FF.FpC.t; y_inv : FF.FpC.t }

  val make : G1.Circuit.t -> t

  val x_over_y_fpa : t -> FF.FpA.t

  val y_inv_fpa : t -> FF.FpA.t
end

(** Evaluate a line into a sparse Fp12 via psi, using an {!AffineCache}. *)
val psi : G2Line.t -> AffineCache.t -> Fp12.Circuit.t

(** Sparse-multiply [f] by a line evaluation. *)
val mul_by_line : Fp12.Circuit.t -> G2Line.t -> AffineCache.t -> Fp12.Circuit.t

val assert_is_tangent : G2Line.t -> G2.Circuit.t -> unit

val assert_is_line : G2Line.t -> G2.Circuit.t -> G2.Circuit.t -> unit
