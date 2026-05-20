open Core

let () =
  let proof_type = ref "" in
  let input_path = ref "" in
  let output_path = ref "" in
  let vk_path = ref "" in
  let info_mode = ref false in
  let spec =
    [ ( "--proof-type"
      , Arg.Set_string proof_type
      , "groth16|plonk  Type of proof to convert" )
    ; ("--input", Arg.Set_string input_path, "PATH  Input proof JSON file")
    ; ("--output", Arg.Set_string output_path, "PATH  Output proof JSON file")
    ; ("--vk", Arg.Set_string vk_path, "PATH  Verification key JSON file")
    ; ("--info", Arg.Set info_mode, "  Report circuit info without proving")
    ]
  in
  Arg.parse spec
    (fun _ -> ())
    "mina-proof-conversion --proof-type <type> [--info --vk <path> | --input \
     <path> --output <path>]" ;
  if String.is_empty !proof_type then (
    Arg.usage spec "Missing --proof-type" ;
    exit 1 ) ;
  if !info_mode then (
    (* Info mode: compile circuits and report gate information *)
    match !proof_type with
    | "groth16" ->
        if String.is_empty !vk_path then (
          eprintf "Groth16 --info requires --vk <path>\n" ;
          exit 1 ) ;
        let vk = Proof_conversion.Groth16.Proof_json.load_vk !vk_path in
        let vk_const = Proof_conversion.Groth16.Vk_constants.create vk in
        Proof_conversion.Groth16.Circuit_info.report_all ~vk:vk_const ()
    | "plonk" ->
        let circuits =
          match Stdlib.Sys.getenv_opt "COMPILE_ZKP" with
          | Some s ->
              let n = Int.of_string (String.chop_prefix_exn s ~prefix:"zkp") in
              [| n |]
          | None ->
              Array.init Proof_conversion.Plonk.Circuits.num_circuits ~f:Fn.id
        in
        Array.iter circuits ~f:(fun n ->
            let rule = Proof_conversion.Plonk.Pickles_rules.make_rule ~n in
            let _tag, _cache, (module Proof), _provers =
              Pickles.compile_promise
                ~public_input:
                  (Pickles.Inductive_rule.Input_and_output
                     (Pickles.Impls.Step.Field.typ, Pickles.Impls.Step.Field.typ)
                  )
                ~auxiliary_typ:Pickles.Impls.Step.Typ.unit
                ~max_proofs_verified:(module Pickles_types.Nat.N0)
                ~name:(sprintf "plonk-info-zkp%d" n)
                ~o1js_compatible_mode:false
                ~choices:(fun ~self:_ -> [ rule ])
                ()
            in
            try
              let _vk =
                Promise.block_on_async_exn (fun () ->
                    Lazy.force Proof.verification_key_promise )
              in
              ()
            with e ->
              eprintf "Warning: wrap compilation failed for zkp%d: %s\n" n
                (Exn.to_string e) )
    | other ->
        eprintf "Unknown proof type: %s\n" other ;
        exit 1 )
  else (
    if String.is_empty !input_path then (
      Arg.usage spec "Missing --input" ;
      exit 1 ) ;
    if String.is_empty !output_path then (
      Arg.usage spec "Missing --output" ;
      exit 1 ) ;
    let (module System : Proof_conversion.PROOF_SYSTEM) =
      match !proof_type with
      | "groth16" ->
          (module Proof_conversion.Convert.Groth16)
      | "plonk" ->
          eprintf
            "PLONK conversion is not available through mina-proof-conversion; \
             use nori-proof-converter (see src/app/proof_conversion/README.md).\n" ;
          exit 1
      | other ->
          eprintf "Unknown proof type: %s (expected groth16 or plonk)\n" other ;
          exit 1
    in
    printf "Converting %s proof: %s -> %s\n" System.name !input_path
      !output_path ;
    System.convert ~input_path:!input_path ~output_path:!output_path )
