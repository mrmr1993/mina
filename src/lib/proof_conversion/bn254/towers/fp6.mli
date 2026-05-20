(** Fp6 = Fp2[v] / (v^3 - xi) arithmetic over BN254.

    Elements are triples [(c0, c1, c2)] representing [c0 + c1*v + c2*v^2]
    with [v^3 = xi] and [xi = 9 + u]. *)

module Constant : sig
  type t = Fp2.Constant.t * Fp2.Constant.t * Fp2.Constant.t

  val zero : t

  val one : t
end

module Circuit : sig
  type t = { c0 : Fp2.Circuit.t; c1 : Fp2.Circuit.t; c2 : Fp2.Circuit.t }

  val typ : (t, Constant.t) Pickles.Impls.Step.Typ.t
end

val of_constant : Constant.t -> Circuit.t

(** Multiply an Fp2 element by the non-residue [xi]. *)
val mul_by_non_residue : Fp2.Circuit.t -> Fp2.Circuit.t

(** Multiply by [v]: [{ c0 = c2 * xi; c1 = c0; c2 = c1 }]. *)
val mul_by_v : Circuit.t -> Circuit.t

val add : Circuit.t -> Circuit.t -> Circuit.t

val sub : Circuit.t -> Circuit.t -> Circuit.t

val neg : Circuit.t -> Circuit.t

(** Fp6 multiplication via Karatsuba (6 Fp2 mults). *)
val mul : Circuit.t -> Circuit.t -> Circuit.t

val inverse : Circuit.t -> Circuit.t

val assert_equal : Circuit.t -> Circuit.t -> unit

(** Multiply Fp6 by a native Fp scalar. *)
val mul_by_fp :
  Circuit.t -> Snarky_foreign_field.Foreign_field.FpA.t -> Circuit.t

(** Multiply Fp6 by a single Fp2 element. *)
val mul_by_fp2 : Circuit.t -> Fp2.Circuit.t -> Circuit.t

(** Multiply Fp6 by a sparse Fp6 element [(rhs.c0, rhs.c1, 0)]. *)
val mul_by_sparse_fp6 : Circuit.t -> Circuit.t -> Circuit.t

(** Multiply Fp6 by the sparse element with components [b0], [b1]. *)
val mul_by_01 : Circuit.t -> Fp2.Circuit.t -> Fp2.Circuit.t -> Circuit.t
