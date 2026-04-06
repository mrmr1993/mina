(** Precomputed line coefficients for PLONK KZG pairing.

    Loads g2_lines and tau_lines from JSON, matching nori's LineParser.
    Lines are embedded as circuit constants.

    Reference: nori-proof-conversion/src/plonk/recursion/line_parser.ts *)

open! Core_kernel
module FF = Snarky_foreign_field.Foreign_field

(** Parse a G2Line from JSON: { lambda: { c0, c1 }, neg_mu: { c0, c1 } } *)
let parse_line (j : Yojson.Safe.t) : Lines.G2Line.constant =
  let open Yojson.Safe.Util in
  let fp2 key =
    let obj = member key j in
    let c0 = Bignum_bigint.of_string (to_string (member "c0" obj)) in
    let c1 = Bignum_bigint.of_string (to_string (member "c1" obj)) in
    (c0, c1)
  in
  (fp2 "lambda", fp2 "neg_mu")

(** Load all lines from a JSON file. *)
let load_lines_from_json (path : string) : Lines.G2Line.constant array =
  let json = Yojson.Safe.from_file path in
  let entries = Yojson.Safe.Util.to_list json in
  Array.of_list (List.map entries ~f:parse_line)

(** Count lines needed for ATE loop iterations [from, to). *)
let ate_cnt_slice ~(from : int) ~(to_ : int) : int =
  let ate = Bn254_params.ate_loop_count in
  let cnt = ref 0 in
  for i = from to to_ - 1 do
    if ate.(i) = 0 then incr cnt
    else cnt := !cnt + 2
  done ;
  !cnt

(** Parse g2 lines for iterations [from, to). *)
let parse_g2 (all_g2 : Lines.G2Line.constant array) ~(from : int) ~(to_ : int)
    : Lines.G2Line.constant array =
  let start = ate_cnt_slice ~from:1 ~to_:from in
  let len = ate_cnt_slice ~from ~to_ in
  Array.sub all_g2 ~pos:start ~len

(** Parse tau lines for iterations [from, to). *)
let parse_tau (all_tau : Lines.G2Line.constant array) ~(from : int) ~(to_ : int)
    : Lines.G2Line.constant array =
  let start = ate_cnt_slice ~from:1 ~to_:from in
  let len = ate_cnt_slice ~from ~to_ in
  Array.sub all_tau ~pos:start ~len

(** Get the last 2 frobenius lines. *)
let frobenius_lines (all : Lines.G2Line.constant array) :
    Lines.G2Line.constant * Lines.G2Line.constant =
  let n = Array.length all in
  (all.(n - 2), all.(n - 1))
