(** Line coefficients for BN254 pairing computation. *)

open! Core_kernel
module FF = Snarky_foreign_field.Foreign_field
module Step = Pickles.Impls.Step

module G2Line = struct
  type t = { lambda : Fp2.Circuit.t; neg_mu : Fp2.Circuit.t }

  type constant = Fp2.Constant.t * Fp2.Constant.t

  let typ : (t, constant) Step.Typ.t =
    Step.Typ.transport
      (Step.Typ.tuple2 Fp2.Circuit.typ Fp2.Circuit.typ)
      ~there:(fun (l, m) -> (l, m))
      ~back:(fun (l, m) -> (l, m))
    |> Step.Typ.transport_var
         ~there:(fun { lambda; neg_mu } -> (lambda, neg_mu))
         ~back:(fun (lambda, neg_mu) -> { lambda; neg_mu })

  (** Embed a constant line as a circuit value. *)
  let of_constant (l : constant) : t =
    let lambda, neg_mu = l in
    { lambda = Fp2.of_constant lambda; neg_mu = Fp2.of_constant neg_mu }

  (** Evaluate the line at a G2 point: -lambda*x + neg_mu + y. *)
  let evaluate (line : t) (p : G2.Circuit.t) : Fp2.Circuit.t =
    let t = Fp2.neg (Fp2.mul line.lambda p.x) in
    let t = Fp2.add t line.neg_mu in
    Fp2.add t p.y

  (** Assert that a line passes through two G2 points. *)
  let assert_is_line (line : t) (t_point : G2.Circuit.t) (q : G2.Circuit.t) :
      unit =
    let e1 = evaluate line t_point in
    let e2 = evaluate line q in
    Fp2.assert_equal e1 (Fp2.of_constant Fp2.Constant.zero) ;
    Fp2.assert_equal e2 (Fp2.of_constant Fp2.Constant.zero)

  (** Assert that a line is tangent to the curve at point p:
        evaluate(p) == 0
        2*lambda*y == x^2 * 3 *)
  let assert_is_tangent (line : t) (p : G2.Circuit.t) : unit =
    let e = evaluate line p in
    Fp2.assert_equal e (Fp2.of_constant Fp2.Constant.zero) ;
    let dbl_lambda_y = Fp2.mul (Fp2.add line.lambda line.lambda) p.y in
    let x_square = Fp2.square p.x in
    let three = FF.FpA.of_constant (Bignum_bigint.of_int 3) in
    Fp2.assert_equal dbl_lambda_y (Fp2.mul_by_fp x_square three)

  (** Evaluate a line into a sparse Fp12 element:
        c0 = (1, 0, 0), c1 = (lambda*x_over_y, neg_mu*y_inv, 0) *)
  let psi (line : t) ~(x_over_y : FF.FpA.t) ~(y_inv : FF.FpA.t) : Fp12.Circuit.t
      =
    let g0 : Fp2.Circuit.t =
      { c0 = FF.FpA.of_constant FF.Bignum_bigint.one
      ; c1 = FF.FpA.of_constant FF.Bignum_bigint.zero
      }
    in
    let h0 = Fp2.mul_by_fp line.lambda x_over_y in
    let g1 = Fp2.of_constant Fp2.Constant.zero in
    let h1 = Fp2.mul_by_fp line.neg_mu y_inv in
    let g2 = Fp2.of_constant Fp2.Constant.zero in
    let h2 = Fp2.of_constant Fp2.Constant.zero in
    { Fp12.Circuit.c0 = { Fp6.Circuit.c0 = g0; c1 = g1; c2 = g2 }
    ; c1 = { Fp6.Circuit.c0 = h0; c1 = h1; c2 = h2 }
    }
end

module AffineCache = struct
  type t = { x_over_y : FF.FpC.t; y_inv : FF.FpC.t }

  let make (p : G1.Circuit.t) : t =
    let f = Bn254_params.p in
    let x_neg = FF.FpA.neg p.x ~f |> FF.FpC.assert_canonical ~f in
    (* This computation is unused but must remain: it emits constraints
       that are part of the circuit structure matching the TS reference. *)
    let _y_inv = FF.FpA.inv p.y ~f |> FF.FpC.assert_canonical ~f in
    let y_inv =
      Step.exists (FF.FpC.typ ~f) ~compute:(fun () ->
          let p_y = Step.As_prover.read (FF.FpA.typ ~f) p.y in
          Option.value_exn @@ FF.bignum_mod_inverse p_y ~f )
    in
    FF.assert_equal
      (FF.FpA.mul ~f (y_inv :> FF.FpA.t) p.y :> FF.Field3.t)
      (FF.Field3.of_constant Bigint.one) ;
    let x_over_y = FF.FpC.mul ~f x_neg y_inv in
    let x_over_y = FF.FpC.assert_canonical_ x_over_y ~f in
    { y_inv; x_over_y }

  let x_over_y_fpa (c : t) : FF.FpA.t = FF.FpC.to_fpa c.x_over_y

  let y_inv_fpa (c : t) : FF.FpA.t = FF.FpC.to_fpa c.y_inv
end

(** Evaluate a line into a sparse Fp12 via psi, using an AffineCache. *)
let psi (line : G2Line.t) (cache : AffineCache.t) : Fp12.Circuit.t =
  G2Line.psi line
    ~x_over_y:(AffineCache.x_over_y_fpa cache)
    ~y_inv:(AffineCache.y_inv_fpa cache)

(** Sparse-multiply f by a line evaluation: f.sparse_mul(line.psi(cache)).
    Convenience wrapper for the common pattern in ate loop iterations. *)
let mul_by_line (f : Fp12.Circuit.t) (line : G2Line.t) (cache : AffineCache.t) :
    Fp12.Circuit.t =
  Fp12.sparse_mul f (psi line cache)

(* Re-export G2Line assertion functions at module level for convenience *)
let assert_is_tangent = G2Line.assert_is_tangent

let assert_is_line = G2Line.assert_is_line
