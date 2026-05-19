(** Canonical regression gate for the proof_conversion library.

    Compiles every circuit (24 PLONK base + 2 compressor + 16 Groth16 base)
    under the production [~name:] strings, captures each circuit's
    step-circuit gate dump via Pickles' [DUMP_PCS_GATES] mechanism, and
    prints a sorted JSON map [{ "<circuit>": "<step_gate_sha256>" }] to
    stdout. A dune rule (see [dune]) diffs this output against the
    committed golden [golden/step_gate_digests.json].

    Why step-circuit gate digests, not VK hashes?
    - Step-circuit gate JSONs are pure functions of the OCaml constraint-
      system code: identical source → byte-identical dumps, across rebuilds.
    - Pickles VK hashes drift across rebuilds (the wrap-circuit dump varies
      bit-by-bit even when the step circuit is stable). VK byte-diffs
      therefore cannot serve as a per-commit regression gate.
    - Step dumps capture every gate, wire, and coefficient — strictly
      stronger than a VK hash even if VK hashes were stable.

    Each [Pickles.compile_promise] dumps the step constraint system twice
    (once at compile time, once at VK computation, producing identical
    files). The driver consumes the *first* dump of each compile and
    advances by 2 each time.

    The hash input is [name || "\n" || step_dump_bytes], so a refactor
    that changes a [~name:] string while leaving the circuit identical
    still flips the digest. *)

open Core_kernel
module Step = Pickles.Impls.Step

(** Locate the Groth16 example VK fixture. Works both from the workspace
    root (when invoked via [regen_golden.sh]) and from a dune sandbox
    (when invoked via the [check-proof-conversion] alias, which copies
    [fixtures/] into the rule's working directory). *)
let groth16_vk_path =
  let candidates =
    [ "fixtures/groth16_example/vk.json"
    ; "src/lib/proof_conversion/test/fixtures/groth16_example/vk.json"
    ]
  in
  match List.find candidates ~f:Stdlib.Sys.file_exists with
  | Some p ->
      p
  | None ->
      failwithf
        "test_step_gate_golden: could not locate groth16 example vk.json \
         (tried: %s)"
        (String.concat ~sep:", " candidates)
        ()

let dump_dir =
  match Stdlib.Sys.getenv_opt "DUMP_PCS_GATES" with
  | Some d ->
      d
  | None ->
      eprintf
        "test_step_gate_golden: DUMP_PCS_GATES must be set to a writable, \
         empty directory.\n" ;
      exit 2

(** Position in the [cs_30ED_0_<N>_gates.json] sequence. Each successful
    compile advances by 2 (Pickles dumps the step circuit twice per
    compile, with identical contents). *)
let next_step_dump_idx = ref 0

let read_step_dump idx =
  let path =
    Filename.concat dump_dir (sprintf "cs_30ED_0_%d_gates.json" idx)
  in
  In_channel.with_file path ~f:In_channel.input_all

let take_next_step_dump () =
  let content = read_step_dump !next_step_dump_idx in
  (* Sanity check: the next dump should be identical (Pickles emits twice). *)
  let dup = read_step_dump (!next_step_dump_idx + 1) in
  if not (String.equal content dup) then
    failwithf
      "test_step_gate_golden: expected dump idx %d and %d to be identical, \
       but they differ. Pickles dump convention may have changed."
      !next_step_dump_idx
      (!next_step_dump_idx + 1)
      () ;
  next_step_dump_idx := !next_step_dump_idx + 2 ;
  content

let digest_circuit ~name ~step_dump =
  let buf = Buffer.create (String.length step_dump + 64) in
  Buffer.add_string buf name ;
  Buffer.add_char buf '\n' ;
  Buffer.add_string buf step_dump ;
  let h = Digestif.SHA256.digest_string (Buffer.contents buf) in
  Digestif.SHA256.to_hex h

let compile_plonk_circuit ~n =
  let rule = Proof_conversion.Plonk_pickles_rules.make_rule ~n in
  let _tag, _cache, (module Proof), _provers =
    Pickles.compile_promise
      ~public_input:
        (Pickles.Inductive_rule.Input_and_output (Step.Field.typ, Step.Field.typ))
      ~auxiliary_typ:Step.Typ.unit
      ~max_proofs_verified:(module Pickles_types.Nat.N0)
      ~name:(sprintf "plonk-zkp%d" n)
      ~o1js_compatible_mode:false
      ~choices:(fun ~self:_ -> [ rule ])
      ()
  in
  let _vk =
    Promise.block_on_async_exn (fun () ->
        Lazy.force Proof.verification_key_promise )
  in
  ()

let compile_groth16_circuit ~vk:vk_const ~n =
  let rule = Proof_conversion.Pickles_rules.make_rule ~vk:vk_const ~n in
  let _tag, _cache, (module Proof), _provers =
    Pickles.compile_promise
      ~public_input:
        (Pickles.Inductive_rule.Input_and_output (Step.Field.typ, Step.Field.typ))
      ~auxiliary_typ:Step.Typ.unit
      ~max_proofs_verified:(module Pickles_types.Nat.N0)
      ~name:(sprintf "groth16-zkp%d" n)
      ~o1js_compatible_mode:false
      ~choices:(fun ~self:_ -> [ rule ])
      ()
  in
  let _vk =
    Promise.block_on_async_exn (fun () ->
        Lazy.force Proof.verification_key_promise )
  in
  ()

let compile_compressor which =
  let _tag, (module Proof : Pickles.Proof_intf
              with type t = Pickles_types.Nat.N2.n Pickles.Proof.t
               and type statement =
                unit * Proof_conversion.Tree_compressor.subtree_carry_const)
      , _prover =
    match which with
    | `Layer1 ->
        Proof_conversion.Tree_compressor.compile_layer1 ()
    | `Node ->
        Proof_conversion.Tree_compressor.compile_node ()
  in
  let _vk =
    Promise.block_on_async_exn (fun () ->
        Lazy.force Proof.verification_key_promise )
  in
  ()

let () =
  let entries = ref [] in
  let log_and_digest ~circuit_name ~pickles_name ~compile =
    eprintf "[step_gate_golden] %s ...%!" circuit_name ;
    let t0 = Stdlib.Sys.time () in
    compile () ;
    let step_dump = take_next_step_dump () in
    let digest = digest_circuit ~name:pickles_name ~step_dump in
    eprintf " %s (%.1fs)\n%!" digest (Stdlib.Sys.time () -. t0) ;
    entries := (circuit_name, `String digest) :: !entries
  in
  (* PLONK base circuits *)
  for n = 0 to Proof_conversion.Plonk_circuits.num_circuits - 1 do
    log_and_digest
      ~circuit_name:(sprintf "plonk/zkp%d" n)
      ~pickles_name:(sprintf "plonk-zkp%d" n)
      ~compile:(fun () -> compile_plonk_circuit ~n)
  done ;
  (* Tree compressor circuits *)
  log_and_digest ~circuit_name:"compressor/layer1" ~pickles_name:"layer1"
    ~compile:(fun () -> compile_compressor `Layer1) ;
  log_and_digest ~circuit_name:"compressor/node" ~pickles_name:"node"
    ~compile:(fun () -> compile_compressor `Node) ;
  (* Groth16 base circuits *)
  let vk_const =
    let vk = Proof_conversion.Proof_json.load_vk groth16_vk_path in
    Proof_conversion.Vk_constants.create vk
  in
  for n = 0 to Proof_conversion.Circuits.num_circuits - 1 do
    log_and_digest
      ~circuit_name:(sprintf "groth16/zkp%d" n)
      ~pickles_name:(sprintf "groth16-zkp%d" n)
      ~compile:(fun () -> compile_groth16_circuit ~vk:vk_const ~n)
  done ;
  (* Sort key by (system, numeric index) for stable, human-readable output. *)
  let key_order (name, _) =
    let system, idx =
      match String.split name ~on:'/' with
      | [ s; rest ] ->
          let n =
            match Int.of_string (String.chop_prefix rest ~prefix:"zkp" |> Option.value ~default:"") with
            | n ->
                n
            | exception _ ->
                -1
          in
          (s, n)
      | _ ->
          (name, -1)
    in
    (system, idx, name)
  in
  let sorted =
    List.sort !entries ~compare:(fun a b ->
        [%compare: string * int * string] (key_order a) (key_order b) )
  in
  let json = `Assoc sorted in
  print_endline (Yojson.Safe.pretty_to_string json)
