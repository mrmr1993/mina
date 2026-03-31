(** Compile individual Groth16 circuits and report VK hashes.

    Usage:
      CIRCUIT=7 dune exec src/lib/proof_conversion/test/test_groth16_vk.exe
      dune exec src/lib/proof_conversion/test/test_groth16_vk.exe  (all circuits)

    Compare VK hashes against nori:
      cd ../nori-proof-conversion && \
        GROTH16_VK_PATH=./src/groth/example_jsons/vk.json \
        node build/src/groth/recursion/dump_digests.js *)

open Core_kernel
module Step = Pickles.Impls.Step

let compile_circuit ~(n : int) : string =
  let rule = Proof_conversion.Pickles_rules.make_rule ~n in
  let tag, _cache, (module Proof), _provers =
    Pickles.compile_promise
      ~public_input:
        (Pickles.Inductive_rule.Input_and_output
           ( Proof_conversion.Circuit_utils.public_input_typ 1
           , Proof_conversion.Circuit_utils.public_input_typ 1 ) )
      ~auxiliary_typ:Step.Typ.unit
      ~max_proofs_verified:(module Pickles_types.Nat.N0)
      ~name:(sprintf "groth16-zkp%d" n)
      ~o1js_compatible_mode:false
      ~override_wrap_domain:Pickles_base.Proofs_verified.N1
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
      let hash = compile_circuit ~n in
      printf "VK=%s\n%!" hash )
