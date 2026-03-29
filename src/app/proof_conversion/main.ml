open Core

let () =
  let proof_type = ref "" in
  let input_path = ref "" in
  let output_path = ref "" in
  let spec =
    [ ( "--proof-type"
      , Arg.Set_string proof_type
      , "groth16|plonk  Type of proof to convert" )
    ; ("--input", Arg.Set_string input_path, "PATH  Input proof JSON file")
    ; ("--output", Arg.Set_string output_path, "PATH  Output proof JSON file")
    ]
  in
  Arg.parse spec
    (fun _ -> ())
    "mina-proof-conversion --proof-type <type> --input <path> --output <path>" ;
  if String.is_empty !proof_type then (
    Arg.usage spec "Missing --proof-type" ;
    exit 1 ) ;
  if String.is_empty !input_path then (
    Arg.usage spec "Missing --input" ;
    exit 1 ) ;
  if String.is_empty !output_path then (
    Arg.usage spec "Missing --output" ;
    exit 1 ) ;
  ( match !proof_type with
  | "groth16" ->
      eprintf "Groth16 proof conversion: not yet implemented\n"
  | "plonk" ->
      eprintf "PLONK proof conversion: not yet implemented\n"
  | other ->
      eprintf "Unknown proof type: %s (expected groth16 or plonk)\n" other ;
      exit 1 ) ;
  exit 1
