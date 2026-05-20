(** End-to-end Groth16 (RISC Zero) proof conversion. *)

(** Human-readable proof-system name ([groth16]). *)
val name : string

(** Convert a Groth16 proof at [input_path] into a Mina-compatible proof,
    written as JSON to [output_path].

    [vk_path] and [aux_path] override the verification-key and auxiliary-
    witness JSON locations. When omitted, each falls back to its environment
    variable ([GROTH16_VK_PATH] / [GROTH16_AUX_PATH]) and then to the
    conventional sibling of [input_path]. *)
val convert :
     ?vk_path:string
  -> ?aux_path:string
  -> input_path:string
  -> output_path:string
  -> unit
  -> unit
