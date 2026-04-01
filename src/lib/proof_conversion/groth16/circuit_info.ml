(** Extract circuit information (gate counts, types) for comparison
    against nori-proof-conversion fixtures. *)

open! Core_kernel
module Step = Pickles.Impls.Step

(** Compile a circuit and extract the step circuit gate count. *)
let get_gate_count ~(vk : Vk_constants.t) ~(n : int) : int =
  let rule = Pickles_rules.make_rule ~vk ~n in
  let _tag, _cache, (module Proof), _provers =
    Pickles.compile_promise
      ~public_input:
        (Pickles.Inductive_rule.Input_and_output
           (Circuit_utils.public_input_typ 1, Circuit_utils.public_input_typ 1)
        )
      ~auxiliary_typ:Step.Typ.unit
      ~max_proofs_verified:(module Pickles_types.Nat.N0)
      ~name:(sprintf "groth16-info-zkp%d" n)
      ~o1js_compatible_mode:false
      ~choices:(fun ~self:_ -> [ rule ])
      ()
  in
  (* Force VK computation to get the step circuit digest *)
  let vk =
    Promise.block_on_async_exn (fun () ->
        Lazy.force Proof.verification_key_promise )
  in
  ignore (vk : Pickles.Verification_key.t) ;
  (* The gate count is embedded in the VK — for now return a placeholder.
     The actual gate count can be extracted via DUMP_PCS_GATES. *)
  -1

(** Report circuit information for all 16 Groth16 circuits. *)
let report_all ~(vk : Vk_constants.t) () =
  printf "Groth16 Circuit Information\n" ;
  printf "==========================\n" ;
  printf "%-8s %-20s %s\n" "Circuit" "Description" "Status" ;
  let descriptions =
    [| "ate loop (12 iters)"
     ; "ate loop (11 iters)"
     ; "ate loop (11 iters)"
     ; "ate loop (12 iters)"
     ; "ate loop (12 iters)"
     ; "ate loop (6 iters)"
     ; "Frobenius corrections"
     ; "f-update (10 sq)"
     ; "f-update (10 sq)"
     ; "f-update (10 sq)"
     ; "f-update (10 sq)"
     ; "f-update (10 sq)"
     ; "f-update (12 sq)"
     ; "final exponentiation"
     ; "Fp multiplication"
     ; "pairing check"
    |]
  in
  let circuits =
    match Stdlib.Sys.getenv_opt "COMPILE_ZKP" with
    | Some s ->
        let n = Int.of_string (String.chop_prefix_exn s ~prefix:"zkp") in
        [| n |]
    | None ->
        Array.init Circuits.num_circuits ~f:Fn.id
  in
  Array.iter circuits ~f:(fun n ->
      printf "  zkp%-3d %-20s compiling... %!" n descriptions.(n) ;
      let _count = get_gate_count ~vk ~n in
      printf "done\n%!" ) ;
  printf "\nUse DUMP_PCS_GATES=<dir> for full gate JSON dumps.\n"
