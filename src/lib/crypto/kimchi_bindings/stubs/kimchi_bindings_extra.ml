(* Hand-written FFI bindings that ocaml_gen cannot emit.

   The fat-proof step-prover entry point returns the proof together with the
   oracle challenges the prover already computed, so the wrap can skip
   recomputing them via [Kimchi_bindings.Protocol.Oracles.Fp.create_with_public_evals].

   This is declared by hand (rather than generated into [kimchi_bindings.ml])
   because ocaml_gen re-declares types per-module and cannot resolve
   [CamlOracles] in the generated Proof module's scope. We reference the already
   generated types directly. The C symbol comes from the Rust stub (see
   `pasta_fp_plonk_proof.rs::caml_pasta_fp_plonk_proof_create_with_oracles`). *)

external fp_proof_create_with_oracles :
     Kimchi_bindings.Protocol.Index.Fp.t
  -> Kimchi_bindings.FieldVectors.Fp.t array
  -> Pasta_bindings.Fp.t Kimchi_types.runtime_table array
  -> Pasta_bindings.Fp.t array
  -> Pasta_bindings.Fq.t Kimchi_types.or_infinity array
  -> ( Pasta_bindings.Fq.t Kimchi_types.or_infinity
     , Pasta_bindings.Fp.t )
     Kimchi_types.proof_with_public
     * Pasta_bindings.Fp.t Kimchi_types.oracles
  = "caml_pasta_fp_plonk_proof_create_with_oracles"
