(** Convert BN254 foreign-field elements to byte arrays for SHA-256 input.

    Matches nori's [provableBn254BaseFieldToBytes] /
    [provableBn254ScalarFieldToBytes]. *)

module Step = Pickles.Impls.Step
module FF = Snarky_foreign_field.Foreign_field

(** A byte: a native field element constrained to [[0, 256)]. *)
type byte = Step.Field.t

(** Convert a foreign-field element to 32 bytes (big-endian). *)
val field3_to_bytes : FF.Field3.t -> size_in_bits:int -> byte array

(** Convert a BN254 base-field element to 32 bytes. *)
val fp_to_bytes : FF.FpA.t -> byte array

(** Convert a BN254 scalar-field element to 32 bytes. *)
val fr_to_bytes : FF.FpA.t -> byte array

(** Convert 4 big-endian bytes to one UInt32 word. *)
val bytes_to_word : byte array -> Uint32.t

(** Convert a foreign-field element to 8 UInt32 words. *)
val field3_to_words : FF.Field3.t -> size_in_bits:int -> Uint32.t array
