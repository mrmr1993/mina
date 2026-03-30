(** Circuit witness injection — bridges tracker data to circuit bodies.

    Provides functions that witness Fp12/Fp2/Field3 values inside circuits
    from the precomputed tracker data. Each function uses [exists ~compute]
    where the compute closure reads from the tracker. *)

module Step = Pickles.Impls.Step
module FF = Snarky_foreign_field.Foreign_field
module WT = Witness_tracker

(** Witness a Field3 value from a bignum via 3 limb allocations. *)
let witness_field3 (v : FF.Bignum_bigint.t) : FF.Field3.t =
  Witness_provider.witness_field3 v

(** Witness an Fp2 from tracker's Fp2.t *)
let witness_fp2 ((c0, c1) : WT.Fp2.t) : Fp2.Circuit.t =
  { Fp2.Circuit.c0 = witness_field3 c0
  ; c1 = witness_field3 c1 }

(** Witness an Fp6 from tracker's Fp6.t *)
let witness_fp6 ((c0, c1, c2) : WT.Fp6.t) : Fp6.Circuit.t =
  { Fp6.Circuit.c0 = witness_fp2 c0
  ; c1 = witness_fp2 c1
  ; c2 = witness_fp2 c2 }

(** Witness an Fp12 from tracker's Fp12.t *)
let witness_fp12 ((c0, c1) : WT.Fp12.t) : Fp12.Circuit.t =
  { Fp12.Circuit.c0 = witness_fp6 c0
  ; c1 = witness_fp6 c1 }

(** Witness a G1 point from tracker's G1.t *)
let witness_g1 (pt : WT.G1.t) : G1.Circuit.t =
  { G1.Circuit.x = witness_field3 pt.x
  ; y = witness_field3 pt.y }

(** Witness a line coefficient from tracker's Line.t *)
let witness_line (line : WT.Line.t) : Lines.G2Line.t =
  { Lines.G2Line.lambda = witness_fp2 line.lambda
  ; neg_mu = witness_fp2 line.neg_mu }

(** Witness an affine cache from precomputed values. *)
let witness_affine_cache ~(x_over_y : FF.Bignum_bigint.t)
    ~(y_inv : FF.Bignum_bigint.t) : Lines.AffineCache.t =
  { Lines.AffineCache.x_over_y = witness_field3 x_over_y
  ; y_inv = witness_field3 y_inv }

(** Whether to use real (variable) witnesses from the tracker.
    When false, circuits use constant witnesses which fold to fewer gates
    and don't require foreign field feature flags. Set to true once
    the feature flag configuration is resolved. *)
let use_variable_witnesses = false

(** Get the Fp12 accumulator for a specific circuit from the tracker.
    Returns None when variable witnesses are disabled or tracker unavailable. *)
let get_circuit_fp12 ~(circuit_index : int) : WT.Fp12.t option =
  if not use_variable_witnesses then None
  else
    match Circuit_config.get_tracker () with
    | None -> None
    | Some tracker ->
        let ate_ranges =
          [| (1, 13); (13, 24); (24, 35); (35, 47); (47, 59); (59, 65) |]
        in
        if circuit_index >= 0 && circuit_index <= 5 then
          let begin_idx, _ = ate_ranges.(circuit_index) in
          if begin_idx <= 1 then Some WT.Fp12.one
          else Some (WT.get_f_at_iteration tracker (begin_idx - 2))
        else if circuit_index <= 12 then
          Some (WT.get_f tracker)
        else Some WT.Fp12.one
