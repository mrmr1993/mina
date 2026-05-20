(** Extract circuit information (gate counts, types) for comparison
    against nori-proof-conversion fixtures. *)

(** Compile a circuit and extract its step-circuit gate count. *)
val get_gate_count : vk:Vk_constants.t -> n:int -> int

(** Report circuit information for all 16 Groth16 circuits. *)
val report_all : vk:Vk_constants.t -> unit -> unit
