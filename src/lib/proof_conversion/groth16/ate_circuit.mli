(** Ate-loop circuit body shared by zkp0-6. *)

open Proof_conversion_bn254
module Step = Pickles.Impls.Step
module WT = Witness_tracker

(** Three-cache line-evaluation context (negA / C / PI). *)
type three_cache =
  { a_cache : Lines.AffineCache.t
  ; c_cache : Lines.AffineCache.t
  ; pi_cache : Lines.AffineCache.t
  }

(** Process one ate-loop iteration in-circuit with 3-party line
    evaluation. Returns [(g, updated_T)]; does not update [f]. *)
val process_iteration :
     G2.Circuit.t
  -> b_point:G2.Circuit.t
  -> neg_b:G2.Circuit.t
  -> bit:int
  -> double_line:Lines.G2Line.t
  -> delta_double:Lines.G2Line.t
  -> gamma_double:Lines.G2Line.t
  -> caches:three_cache
  -> add_line:Lines.G2Line.t option
  -> delta_add:Lines.G2Line.t option
  -> gamma_add:Lines.G2Line.t option
  -> Fp12.Circuit.t * G2.Circuit.t

(** Witness a G2Line from tracker iteration data. *)
val witness_line : (WT.iteration_data -> WT.Line.t) -> int -> Lines.G2Line.t

(** Witness an optional G2Line from the tracker. *)
val witness_opt_line :
  (WT.iteration_data -> WT.Line.t option) -> int -> Lines.G2Line.t

(** Run a chunk of ate-loop iterations with T tracking and 3-party
    lines. Returns [(final_T, g_values)]. *)
val run_chunk :
     G2.Circuit.t
  -> b_point:G2.Circuit.t
  -> neg_b:G2.Circuit.t
  -> begin_idx:int
  -> end_idx:int
  -> b_lines:Lines.G2Line.t array
  -> delta_lines:Lines.G2Line.t array
  -> gamma_lines:Lines.G2Line.t array
  -> lines_hashes:Step.Field.t array
  -> caches:three_cache
  -> G2.Circuit.t * Fp12.Circuit.t array

(** Ate-loop iteration ranges per circuit (zkp0-6). *)
val circuit_ranges : (int * int) array

(** Number of B-lines in the flat array for a range of ate iterations. *)
val b_line_count : from:int -> to_:int -> int

(** Total B-lines across all ate iterations. *)
val total_b_lines : int

(** B-line start offset in the flat array for a circuit range. *)
val b_line_offset : begin_idx:int -> int
