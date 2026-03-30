(** Gate comparison test.

    Compares OCaml circuit gate sequences against nori reference fixtures.

    Usage:
      # First, generate reference fixtures from nori:
      ./generate_gate_fixtures.sh groth16

      # Then, dump OCaml gates and compare:
      DUMP_PCS_GATES=/tmp/ocaml_gates \
        dune exec src/lib/proof_conversion/test/test_gate_comparison.exe -- \
          --reference fixtures/gates/groth16 \
          --candidate /tmp/ocaml_gates

      # Or just compare two existing dump directories:
      dune exec src/lib/proof_conversion/test/test_gate_comparison.exe -- \
          --reference /path/to/nori_gates \
          --candidate /path/to/ocaml_gates *)

let () =
  let reference_dir = ref "" in
  let candidate_dir = ref "" in
  let spec =
    [ ( "--reference"
      , Stdlib.Arg.Set_string reference_dir
      , "DIR  Directory with reference gate JSON files (from nori)" )
    ; ( "--candidate"
      , Stdlib.Arg.Set_string candidate_dir
      , "DIR  Directory with candidate gate JSON files (from OCaml)" )
    ]
  in
  Stdlib.Arg.parse spec
    (fun _ -> ())
    "test_gate_comparison --reference DIR --candidate DIR" ;
  if String.equal !reference_dir "" || String.equal !candidate_dir "" then (
    Printf.eprintf
      "Usage: test_gate_comparison --reference DIR --candidate DIR\n" ;
    Stdlib.exit 1 ) ;
  Gate_comparison.compare_dirs ~reference_dir:!reference_dir
    ~candidate_dir:!candidate_dir
