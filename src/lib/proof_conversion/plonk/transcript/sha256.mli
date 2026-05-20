(** SHA-256 provable gadget.

    Reference: o1js [src/lib/provable/gadgets/sha256.ts]. *)

(** Round constants (§4.2.2). *)
val k_constants : int array

(** Initial hash values (§5.3.3). *)
val h_init : int array

val seal : Pickles.Impls.Step.Field.t -> Pickles.Impls.Step.Field.t

(** [ch(x, y, z) = (x & y) ^ (~x & z)]. *)
val ch : Uint32.t -> Uint32.t -> Uint32.t -> Uint32.t

(** [maj(x, y, z) = (x & y) ^ (x & z) ^ (y & z)]. *)
val maj : Uint32.t -> Uint32.t -> Uint32.t -> Uint32.t

val rotr : int -> Uint32.t -> Uint32.t

val shr : int -> Uint32.t -> Uint32.t

(** Sigma via individual ROTR/SHR + XOR (for constant inputs). *)
val sigma_simple :
  Uint32.t -> bits:int * int * int -> first_shifted:bool -> Uint32.t

(** Fused sigma: decompose, reassemble 3 rotations, XOR. *)
val sigma : Uint32.t -> bits:int * int * int -> first_shifted:bool -> Uint32.t

val sigma_zero : Uint32.t -> Uint32.t

val sigma_one : Uint32.t -> Uint32.t

val delta_zero : Uint32.t -> Uint32.t

val delta_one : Uint32.t -> Uint32.t

(** SHA-256 compression function. *)
val compress : Uint32.t array -> Uint32.t array -> Uint32.t array

(** Prepare the 64-word message schedule from a 16-word block. *)
val message_schedule : Uint32.t array -> Uint32.t array

(** Initial SHA-256 state as circuit UInt32 constants. *)
val initial_state : unit -> Uint32.t array

(** Hash pre-padded message blocks (16 UInt32 words each). *)
val hash_blocks : Uint32.t array array -> Uint32.t array
