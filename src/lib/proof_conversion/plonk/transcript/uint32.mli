(** 32-bit unsigned integer arithmetic for SHA-256.

    Uses constrained kimchi gadgets (XOR, AND, NOT, range checks) to
    match the o1js UInt32 gate sequence exactly. *)

module Step = Pickles.Impls.Step
module Field = Step.Field

type t = Field.t

(** Wrap a field element as a UInt32 (no range check). *)
val of_field : Field.t -> t

(** Get the underlying field element. *)
val to_field : t -> Field.t

(** Constant UInt32 from an int. *)
val of_int : int -> t

val two_to_32 : Bignum_bigint.t

val two_to_32_field : Field.Constant.t

val mask_32 : Bignum_bigint.t

val is_constant : t -> bool

val to_bigint_const : t -> Bignum_bigint.t

(** Range-check a value to [num_bits] bits ([num_bits] a multiple of 16). *)
val range_check_n : Field.t -> num_bits:int -> unit

val range_check_32 : Field.t -> unit

val range_check_16 : Field.t -> unit

val range_check_8 : Field.t -> unit

(** [divMod32]: divide by [2^32], returning [(quotient, remainder)]. *)
val div_mod_32 : Field.t -> n_bits:int -> t * t

(** Add two UInt32 values modulo [2^32]. *)
val add : t -> t -> t

(** Ensure a UInt32 is a variable (not a constant). *)
val ensure_var : t -> t

val read_bigint : Field.t -> Bignum_bigint.t

val bigint_to_const : Bignum_bigint.t -> Field.Constant.t

(** Extract bits [[start, start+len)] from a bigint. *)
val bit_slice : Bignum_bigint.t -> start:int -> len:int -> Bignum_bigint.t

(** Build a chain of Xor16 gates matching o1js [buildXor]. *)
val build_xor : Field.t -> Field.t -> Field.t -> num_bits:int -> unit

(** Bitwise XOR over [length] bits. *)
val xor_n : Field.t -> Field.t -> length:int -> Field.t

(** 32-bit XOR. *)
val xor : t -> t -> t

(** Bitwise AND (32-bit). *)
val bit_and : t -> t -> t

(** Bitwise NOT (32-bit). *)
val bit_not : t -> t

(** Bitwise right rotation (32-bit). *)
val rotr : t -> n:int -> t

(** Bitwise right shift (32-bit). *)
val shr : t -> n:int -> t
