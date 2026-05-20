(** BN254 curve parameters for proof conversion.

    Pure constants with no circuit logic — used by both out-of-circuit
    witness computation and in-circuit verification. *)

(** BN254 base field modulus (Fp). *)
val p : Bignum_bigint.t

(** BN254 scalar field modulus (Fr). *)
val r : Bignum_bigint.t

(** [(p - 1) / 6], used for Frobenius computations. *)
val p_minus_1_div_6 : Bignum_bigint.t

(** BN254 G1 generator x-coordinate (= 1). *)
val g1_generator_x : Bignum_bigint.t

(** BN254 G1 generator y-coordinate (= 2). *)
val g1_generator_y : Bignum_bigint.t

(** BN254 curve parameter [b] in [y^2 = x^3 + b] (= 3). *)
val curve_b : Bignum_bigint.t

(** BN254 G2 generator coordinates over Fp2. *)
val g2_generator_x0 : Bignum_bigint.t

val g2_generator_x1 : Bignum_bigint.t

val g2_generator_y0 : Bignum_bigint.t

val g2_generator_y1 : Bignum_bigint.t

(** ATE loop count in NAF form, big-endian (MSB first); entries are
    [-1], [0] or [1]. *)
val ate_loop_count : int array

(** Frobenius gamma constants, each an Fp2 pair [(c0, c1)]. *)
val gamma_1s : (Bignum_bigint.t * Bignum_bigint.t) array

val gamma_2s : (Bignum_bigint.t * Bignum_bigint.t) array

val gamma_3s : (Bignum_bigint.t * Bignum_bigint.t) array

(** GLV endomorphism constant: cube root of unity in Fp. *)
val glv_beta : Bignum_bigint.t

(** GLV eigenvalue: cube root of unity in Fr. *)
val glv_lambda : Bignum_bigint.t

(** LLL-reduced lattice basis vectors for GLV scalar decomposition. *)
val glv_n11 : Bignum_bigint.t

val glv_n12 : Bignum_bigint.t

val glv_n21 : Bignum_bigint.t

val glv_n22 : Bignum_bigint.t

(** Fp2 non-residue used for tower extension: [xi = 9 + u]. *)
val fp2_non_residue : Bignum_bigint.t * Bignum_bigint.t

(** [w27]: 27th root of unity in Fp12, used for the KZG shift power.
    The result is shaped as a native Fp12 value ([Fp_const.Fp12.t]). *)
val w27 :
     unit
  -> ( (Bignum_bigint.t * Bignum_bigint.t)
     * (Bignum_bigint.t * Bignum_bigint.t)
     * (Bignum_bigint.t * Bignum_bigint.t) )
     * ( (Bignum_bigint.t * Bignum_bigint.t)
       * (Bignum_bigint.t * Bignum_bigint.t)
       * (Bignum_bigint.t * Bignum_bigint.t) )

(** [w27^2]: precomputed square of [w27]. *)
val w27_sq :
     unit
  -> ( (Bignum_bigint.t * Bignum_bigint.t)
     * (Bignum_bigint.t * Bignum_bigint.t)
     * (Bignum_bigint.t * Bignum_bigint.t) )
     * ( (Bignum_bigint.t * Bignum_bigint.t)
       * (Bignum_bigint.t * Bignum_bigint.t)
       * (Bignum_bigint.t * Bignum_bigint.t) )
