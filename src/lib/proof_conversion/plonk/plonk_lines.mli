(** Precomputed line coefficients for the PLONK KZG pairing.

    Parses g2_lines and tau_lines from JSON (embedded as string constants
    by a dune rule), matching nori's [LineParser]. *)

open Proof_conversion_bn254

(** Parse a single G2Line from JSON. *)
val parse_line : Yojson.Safe.t -> Lines.G2Line.constant

(** Parse all lines from a JSON string. *)
val parse_lines : string -> Lines.G2Line.constant array

(** Count lines needed for ate-loop iterations [[from, to_)]. *)
val ate_cnt_slice : from:int -> to_:int -> int

(** Slice the g2 lines for iterations [[from, to_)]. *)
val parse_g2 :
     Lines.G2Line.constant array
  -> from:int
  -> to_:int
  -> Lines.G2Line.constant array

(** Slice the tau lines for iterations [[from, to_)]. *)
val parse_tau :
     Lines.G2Line.constant array
  -> from:int
  -> to_:int
  -> Lines.G2Line.constant array

(** The last 2 Frobenius lines. *)
val frobenius_lines :
  Lines.G2Line.constant array -> Lines.G2Line.constant * Lines.G2Line.constant
