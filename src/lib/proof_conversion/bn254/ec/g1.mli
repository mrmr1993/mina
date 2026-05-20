(** G1 affine point operations on BN254.

    Matches o1js [EllipticCurve.add] / [double] / [scale]. Add and double
    use the witness-and-assertMul pattern; scale uses GLV decomposition
    plus a windowed MSM. *)

module Step = Pickles.Impls.Step
module FF = Snarky_foreign_field.Foreign_field
module FpA = FF.FpA

module Constant : sig
  type t = { x : FF.Bignum_bigint.t; y : FF.Bignum_bigint.t }
end

module Circuit : sig
  type t = { x : FpA.t; y : FpA.t }

  (** FpA check (MRC + weakBound) on each coordinate. *)
  val typ : (t, Constant.t) Step.Typ.t

  (** Raw provable type without checks, for [array_get_generic]. *)
  val provable_typ : (t, Constant.t) Step.Typ.t
end

val of_constant : Constant.t -> Circuit.t

val negate : Circuit.t -> Circuit.t

(** Negate a G1 point with a full MRC on the resulting [-y]. *)
val negate_point : Circuit.t -> Circuit.t

(** Alias of {!negate_point}. *)
val negate_constant_y : Circuit.t -> Circuit.t

(** EC point addition (witness-and-assertMul); also checks [x1 <> x2]. *)
val add : Circuit.t -> Circuit.t -> Circuit.t

(** EC point doubling (witness-and-assertMul). *)
val double : Circuit.t -> Circuit.t

(** Alias of {!add}, kept for non-MSM call sites. *)
val add_nonzero : Circuit.t -> Circuit.t -> Circuit.t

(** GLV [decomposeMaxBits]: the scalar-decomposition bit width. *)
val glv_max_bits : int

(** GLV decompose [s = s0 + s1*lambda (mod r)]; returns the sign flag
    and Field3 magnitude of each component. *)
val glv_decompose :
  FF.Field3.t -> (Step.Field.t * FF.Field3.t) * (Step.Field.t * FF.Field3.t)

type slice_result = { chunks : Step.Field.t array; leftover_size : int }

(** Slice a limb into [chunk_size]-bit chunks; doubles as a range check. *)
val slice_field :
     FF.Limb.t
  -> max_bits:int
  -> chunk_size:int
  -> ?leftover:slice_result
  -> unit
  -> slice_result

(** Slice a Field3 into [chunk_size]-bit chunks. *)
val slice_field3 :
  FF.Field3.t -> max_bits:int -> chunk_size:int -> Step.Field.t array

(** Provable array lookup [array.(index)]. *)
val array_get : Step.Field.t array -> Step.Field.t -> Step.Field.t

(** Provable array lookup over an arbitrary [Typ.t]. *)
val array_get_generic :
  ('var, 'value) Step.Typ.t -> 'var array -> Step.Field.t -> 'var

(** Build the table [[zero; P; 2P; ...; (2^w - 1)*P]]. *)
val get_point_table : Circuit.t -> window_size:int -> Circuit.t array

(** Conditionally negate a point. *)
val negate_if : Step.Field.t -> Circuit.t -> Circuit.t

(** Precomputed initial aggregator for BN254. *)
val initial_aggregator : Constant.t

(** [2^(maxBits-1) * initial_aggregator], precomputed out-of-circuit. *)
val ia_final : Constant.t

(** Check whether a point equals a constant point. *)
val point_equals : Circuit.t -> Constant.t -> Step.Boolean.var

(** Generic [Provable.if] over an arbitrary [Typ.t]. *)
val provable_if :
     ('var, 'value) Step.Typ.t
  -> Step.Field.t
  -> if_true:'var
  -> if_false:'var
  -> 'var

(** Batch range-check weak bounds (nori's [reduceMrcStack]). *)
val reduce_mrc_stack : FF.Limb.t array -> unit

(** Multi-scalar multiplication, matching o1js [multiScalarMul]. *)
val multi_scalar_mul :
  FF.Field3.t array -> Circuit.t array -> window_sizes_in:int array -> Circuit.t

(** Scalar multiplication [scalar * point]. *)
val scale : Circuit.t -> FF.Field3.t -> Circuit.t
