(** Groth16 witness tracker — out-of-circuit computation.

    Pre-computes all intermediate values needed by the 16 recursive
    circuits, using pure bignum arithmetic (no circuit constraints). *)

(** Out-of-circuit Fp arithmetic. *)
module Fp : sig
  val add : Bignum_bigint.t -> Bignum_bigint.t -> Bignum_bigint.t

  val sub : Bignum_bigint.t -> Bignum_bigint.t -> Bignum_bigint.t

  val mul : Bignum_bigint.t -> Bignum_bigint.t -> Bignum_bigint.t

  val inv : Bignum_bigint.t -> Bignum_bigint.t

  val neg : Bignum_bigint.t -> Bignum_bigint.t

  val div : Bignum_bigint.t -> Bignum_bigint.t -> Bignum_bigint.t
end

(** Out-of-circuit Fp2 arithmetic. *)
module Fp2 : sig
  type t = Bignum_bigint.t * Bignum_bigint.t [@@deriving sexp]

  val add : t -> t -> t

  val sub : t -> t -> t

  val mul : t -> t -> t

  val neg : t -> t

  val conjugate : t -> t

  val square : t -> t

  val inverse : t -> t

  val zero : t

  val one : t

  val mul_by_fp : t -> Bignum_bigint.t -> t
end

(** Out-of-circuit Fp6 arithmetic. *)
module Fp6 : sig
  type t = Fp2.t * Fp2.t * Fp2.t

  val xi : Fp2.t

  val mul_by_nr : Fp2.t -> Fp2.t

  val add : t -> t -> t

  val sub : t -> t -> t

  val neg : t -> t

  val mul : t -> t -> t

  val zero : t

  val one : t

  val square : t -> t

  val inverse : t -> t
end

(** Out-of-circuit Fp12 arithmetic. *)
module Fp12 : sig
  type t = Fp6.t * Fp6.t

  val mul : t -> t -> t

  val square : t -> t

  val conjugate : t -> t

  val cyclotomic_inverse : t -> t

  val inverse : t -> t

  val frobenius_pow_p : t -> t

  val frobenius_pow_p_squared : t -> t

  val frobenius_pow_p_cubed : t -> t

  val one : t
end

(** G1 affine point (out-of-circuit). *)
module G1 : sig
  type t = { x : Bignum_bigint.t; y : Bignum_bigint.t }

  val negate : t -> t

  val of_proof_json : Proof_json.G1_constant.t -> t

  val add : t -> t -> t

  val double : t -> t

  (** Scalar multiplication by double-and-add. *)
  val scale : t -> Bignum_bigint.t -> t
end

(** G2 affine point (out-of-circuit). *)
module G2 : sig
  type t = { x : Fp2.t; y : Fp2.t }

  val of_proof_json : Proof_json.G2_constant.t -> t

  val negate : t -> t

  val frobenius : t -> t

  val negative_frobenius : t -> t
end

(** Line coefficient from G2 point operations. *)
module Line : sig
  type t = { lambda : Fp2.t; neg_mu : Fp2.t } [@@deriving sexp]
end

(** Compute the affine cache [(x_over_y, y_inv)] for a G1 point. *)
val compute_affine_cache : G1.t -> Bignum_bigint.t * Bignum_bigint.t

(** Per-iteration witness data for ate-loop circuits. *)
type iteration_data =
  { f_before : Fp12.t
  ; double_line : Line.t
  ; add_line : Line.t option
  ; f_after : Fp12.t
  ; delta_double_line : Line.t
  ; delta_add_line : Line.t option
  ; gamma_double_line : Line.t
  ; gamma_add_line : Line.t option
  }

(** The witness-tracker state. *)
type t =
  { proof : Proof_json.proof
  ; vk : Proof_json.vk
  ; c : Fp12.t
  ; c_inv : Fp12.t
  ; shift_power : int
  ; mutable t_point : G2.t
  ; mutable f : Fp12.t
  ; mutable g_digest : Bignum_bigint.t
  ; mutable g_values : Fp12.t array
  ; mutable iterations : iteration_data array
  ; mutable line_hashes : Bignum_bigint.t array
  ; mutable frobenius_lines : Fp12.t array
  ; mutable frobenius_b_lines : Line.t array
  ; mutable frobenius_delta_lines : Line.t array
  ; mutable frobenius_gamma_lines : Line.t array
  }

val get_neg_a : t -> G1.t

val get_c : t -> G1.t

val get_ic : t -> int -> G1.t

val num_ic : t -> int

val get_public_input : t -> int -> Bignum_bigint.t

val num_public_inputs : t -> int

(** Compute [ic_ic_idx] scaled by [pis.(pi_idx)]. *)
val get_scaled_ic : t -> int -> int -> G1.t

(** Partial IC accumulation for zkp14. *)
val get_partial_ic_acc : t -> G1.t

(** Full IC accumulation for zkp15. *)
val get_full_ic_acc : t -> G1.t

(** The PI point (public-input commitment) used in the pairing. *)
val get_pi : t -> G1.t

(** Compute PI from proof + VK without building a full tracker. *)
val compute_pi : proof:Proof_json.proof -> vk:Proof_json.vk -> G1.t

(** Build the full [Accumulator.Constant.t] from the current state. *)
val get_accumulator_constant : t -> Accumulator.Constant.t

val get_f : t -> Fp12.t

val get_g_values : t -> Fp12.t array

val get_g : t -> int -> Fp12.t

val get_alpha_beta : t -> Fp12.t

val get_w27 : t -> Fp12.t

val get_w27_square : t -> Fp12.t

(** Out-of-circuit Poseidon hash of an Fp12 value. *)
val hash_fp12_out_of_circuit : Fp12.t -> Kimchi_pasta.Pasta.Fp.t

(** The line-hashes array (one Poseidon hash per g value). *)
val get_line_hashes : t -> Kimchi_pasta.Pasta.Fp.t array

(** The [(lhs_hashes, g_chunk, rhs_hashes)] for an f-update circuit's
    [ArrayListHasher.open] call. *)
val get_g_digest_opening :
     t
  -> g_start:int
  -> n_iters:int
  -> Kimchi_pasta.Pasta.Fp.t array
     * Fp12.t array
     * Kimchi_pasta.Pasta.Fp.t array

(** All B-lines as a flat array in nori's order. *)
val get_all_b_lines : t -> Line.t array

val get_c_inv_frob_p : t -> Fp12.t

val get_c_frob_p2 : t -> Fp12.t

val get_c_inv_frob_p3 : t -> Fp12.t

(** Compute a doubling-line coefficient and the doubled point. *)
val compute_double_line : G2.t -> Line.t * G2.t

(** Compute an addition-line coefficient and the summed point. *)
val compute_add_line : G2.t -> G2.t -> Line.t * G2.t

(** Evaluate a line at a G1 point via the affine cache. *)
val evaluate_line :
  Line.t -> x_over_y:Bignum_bigint.t -> y_inv:Bignum_bigint.t -> Fp12.t

(** Run the full out-of-circuit Miller loop, populating the tracker. *)
val compute_miller_loop : t -> unit

(** The g value at a specific ate-loop iteration. *)
val get_g_at_iteration : t -> int -> Fp12.t

(** Per-iteration witness data. *)
val get_iteration : t -> int -> iteration_data

(** Compute the Miller-loop output from proof + VK without aux data. *)
val compute_mlo : proof:Proof_json.proof -> vk:Proof_json.vk -> Fp12.t

(** Compute the KZG pairing MLO [e(A, g2) * e(-B, tau)]. *)
val compute_kzg_pairing_mlo :
  a:G1.t -> neg_b:G1.t -> g2:G2.t -> tau:G2.t -> Fp12.t

(** Create a tracker from proof, VK and aux witness; immediately runs
    the full Miller loop. *)
val create :
  proof:Proof_json.proof -> vk:Proof_json.vk -> aux:Proof_json.aux_witness -> t
