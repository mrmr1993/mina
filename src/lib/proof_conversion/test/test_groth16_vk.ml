(** Compile individual Groth16 circuits and report VK hashes.

    Run from the workspace root:
      CIRCUIT=7 dune exec src/lib/proof_conversion/test/test_groth16_vk.exe
      dune exec src/lib/proof_conversion/test/test_groth16_vk.exe  (all circuits)

    Uses the committed example VK by default; override with GROTH16_VK_PATH. *)

open Core_kernel
module Step = Pickles.Impls.Step

let default_vk_path =
  "src/lib/proof_conversion/test/fixtures/groth16_example/vk.json"

let compile_circuit ~(vk : Proof_conversion.Groth16.Vk_constants.t) ~(n : int) :
    string =
  let rule = Proof_conversion.Groth16.Pickles_rules.make_rule ~vk ~n in
  let tag, _cache, (module Proof), _provers =
    Pickles.compile_promise
      ~public_input:
        (Pickles.Inductive_rule.Input_and_output (Step.Field.typ, Step.Field.typ)
        )
      ~auxiliary_typ:Step.Typ.unit
      ~max_proofs_verified:(module Pickles_types.Nat.N0)
      ~name:(sprintf "groth16-zkp%d" n)
      ~o1js_compatible_mode:false
      ~choices:(fun ~self:_ -> [ rule ])
      ()
  in
  let vk_promise =
    Pickles.Side_loaded.Verification_key.of_compiled_promise tag
  in
  let vk = Promise.block_on_async_exn (fun () -> vk_promise) in
  let hash = Mina_base.Zkapp_account.digest_vk vk in
  ignore
    ( Proof.verification_key_promise
      : Pickles.Verification_key.t Promise.t Lazy.t ) ;
  Kimchi_pasta.Pasta.Fp.to_string hash

let () =
  let vk_path =
    Option.value
      (Stdlib.Sys.getenv_opt "GROTH16_VK_PATH")
      ~default:default_vk_path
  in
  let vk = Proof_conversion.Groth16.Proof_json.load_vk vk_path in
  let vk_const = Proof_conversion.Groth16.Vk_constants.create vk in
  let circuits =
    match Stdlib.Sys.getenv_opt "CIRCUIT" with
    | Some s ->
        [| Int.of_string s |]
    | None ->
        Array.init 16 ~f:Fn.id
  in
  printf "Groth16 circuit VK hashes\n" ;
  printf "=========================\n" ;
  Array.iter circuits ~f:(fun n ->
      printf "  zkp%-2d: compiling... %!" n ;
      let hash = compile_circuit ~vk:vk_const ~n in
      printf "VK=%s\n%!" hash )
