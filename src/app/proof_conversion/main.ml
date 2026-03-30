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
  let (module System : Proof_conversion.PROOF_SYSTEM) =
    match !proof_type with
    | "groth16" ->
        (module Proof_conversion.Groth16)
    | "plonk" ->
        (module Proof_conversion.Plonk)
    | other ->
        eprintf "Unknown proof type: %s (expected groth16 or plonk)\n" other ;
        exit 1
  in
  printf "Converting %s proof: %s -> %s\n" System.name !input_path !output_path ;
  System.convert ~input_path:!input_path ~output_path:!output_path
