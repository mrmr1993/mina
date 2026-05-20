(** Miller loop for the BN254 ate pairing.

    Computes the ate pairing [e(P, Q)] by iterating over [ate_loop_count],
    accumulating line evaluations into an Fp12 value. *)

(** Run the ate-loop body for one iteration. *)
val ate_loop_iteration :
     Fp12.Circuit.t
  -> double_line:Lines.G2Line.t
  -> add_line:Lines.G2Line.t option
  -> cache:Lines.AffineCache.t
  -> bit:int
  -> Fp12.Circuit.t

(** Run the full Miller loop over [ate_loop_count] using precomputed
    line coefficients for each iteration. *)
val run :
     initial_f:Fp12.Circuit.t
  -> double_lines:Lines.G2Line.t array
  -> add_lines:Lines.G2Line.t option array
  -> cache:Lines.AffineCache.t
  -> Fp12.Circuit.t
