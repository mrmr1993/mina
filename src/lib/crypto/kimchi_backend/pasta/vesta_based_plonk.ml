open Core_kernel
open Kimchi_backend_common
open Kimchi_pasta_basic
module Field = Fp
module Curve = Vesta

module Bigint = struct
  include Field.Bigint

  let of_data _ = failwith __LOC__

  let to_field = Field.of_bigint

  let of_field = Field.to_bigint
end

let field_size : Bigint.t = Field.size

module Verification_key = struct
  type t =
    ( Pasta_bindings.Fp.t
    , Kimchi_bindings.Protocol.SRS.Fp.t
    , Pasta_bindings.Fq.t Kimchi_types.or_infinity Kimchi_types.poly_comm )
    Kimchi_types.VerifierIndex.verifier_index

  let to_string _ = failwith __LOC__

  let of_string _ = failwith __LOC__

  let shifts (t : t) = t.shifts
end

module R1CS_constraint_system =
  Kimchi_pasta_constraint_system.Vesta_constraint_system

module Constraint = R1CS_constraint_system.Constraint

let lagrange srs domain_log2 : _ Kimchi_types.poly_comm array =
  let domain_size = Int.pow 2 domain_log2 in
  Kimchi_bindings.Protocol.SRS.Fp.lagrange_commitments_whole_domain srs
    domain_size

let with_lagrange f (vk : Verification_key.t) =
  f (lagrange vk.srs vk.domain.log_size_of_group) vk

let with_lagranges f (vks : Verification_key.t array) =
  let lgrs =
    Array.map vks ~f:(fun vk -> lagrange vk.srs vk.domain.log_size_of_group)
  in
  f lgrs vks

module Rounds_vector = Rounds.Step_vector
module Rounds = Rounds.Step

module Keypair = Dlog_plonk_based_keypair.Make (struct
  let name = "vesta"

  module Rounds = Rounds
  module Urs = Kimchi_bindings.Protocol.SRS.Fp
  module Index = Kimchi_bindings.Protocol.Index.Fp
  module Curve = Curve
  module Poly_comm = Fp_poly_comm
  module Scalar_field = Field
  module Verifier_index = Kimchi_bindings.Protocol.VerifierIndex.Fp
  module Gate_vector = Kimchi_bindings.Protocol.Gates.Vector.Fp
  module Constraint_system = R1CS_constraint_system
end)

module Vesta_inputs = struct
  let id = "pasta_vesta"

  module Scalar_field = Field
  module Base_field = Fq

  module Backend = struct
    type t =
      ( Pasta_bindings.Fq.t Kimchi_types.or_infinity
      , Pasta_bindings.Fp.t )
      Kimchi_types.prover_proof

    type with_public_evals =
      ( Pasta_bindings.Fq.t Kimchi_types.or_infinity
      , Pasta_bindings.Fp.t )
      Kimchi_types.proof_with_public

    include Kimchi_bindings.Protocol.Proof.Fp

    let batch_verify vks ts =
      Promise.run_in_thread (fun () -> batch_verify vks ts)

    let create_aux ~f:backend_create (pk : Keypair.t) primary auxiliary
        prev_chals prev_comms =
      (* external values contains [1, primary..., auxiliary ] *)
      let external_values i =
        let open Field.Vector in
        if i < length primary then get primary i
        else get auxiliary (i - length primary)
      in

      ( match Stdlib.Sys.getenv_opt "AUX_SIZE_LOG" with
      | Some _ ->
          let n = Field.Vector.length auxiliary in
          Stdlib.Printf.eprintf "[aux] len=%d (%.1f MB)\n%!" n
            (float_of_int n *. 32. /. 1048576.)
      | None ->
          () ) ;
      (* compute witness *)
      let computed_witness, runtime_tables =
        R1CS_constraint_system.compute_witness pk.cs external_values
      in
      (* The auxiliary witness is consumed; free its (large) Rust buffer now,
         since OCaml only sees the pointer and won't reclaim it under pressure. *)
      ( match Stdlib.Sys.getenv_opt "RESET_AUX_VECTOR" with
      | Some _ ->
          Kimchi_bindings.FieldVectors.Fp.clear auxiliary
      | None ->
          () ) ;
      let num_rows = Array.length computed_witness.(0) in

      (* convert to Rust vector *)
      let witness_cols =
        Array.init Kimchi_backend_common.Constants.columns ~f:(fun col ->
            let witness = Field.Vector.create () in
            for row = 0 to num_rows - 1 do
              Field.Vector.emplace_back witness computed_witness.(col).(row)
            done ;
            witness )
      in
      backend_create pk.index witness_cols runtime_tables prev_chals prev_comms

    let create_async (pk : Keypair.t) ~primary ~auxiliary ~prev_chals
        ~prev_comms =
      create_aux pk primary auxiliary prev_chals prev_comms
        ~f:(fun index witness runtime_tables prev_chals prev_sgs ->
          Promise.run_in_thread (fun () ->
              Kimchi_bindings.Protocol.Proof.Fp.create index witness
                runtime_tables prev_chals prev_sgs ) )

    let create (pk : Keypair.t) ~primary ~auxiliary ~prev_chals ~prev_comms =
      create_aux pk primary auxiliary prev_chals prev_comms
        ~f:Kimchi_bindings.Protocol.Proof.Fp.create

    (* Fat-proof variant of [create_async]: also returns the oracle challenges
       the prover already computed, so the wrap can skip recomputing them. *)
    let create_with_oracles_async (pk : Keypair.t) ~primary ~auxiliary
        ~prev_chals ~prev_comms =
      create_aux pk primary auxiliary prev_chals prev_comms
        ~f:(fun index witness runtime_tables prev_chals prev_sgs ->
          Promise.run_in_thread (fun () ->
              Kimchi_bindings_extra.fp_proof_create_with_oracles index witness
                runtime_tables prev_chals prev_sgs ) )
  end

  module Verifier_index = Kimchi_bindings.Protocol.VerifierIndex.Fp
  module Index = Keypair

  module Evaluations_backend = struct
    type t = Scalar_field.t Kimchi_types.proof_evaluations
  end

  module Opening_proof_backend = struct
    type t = (Curve.Affine.Backend.t, Scalar_field.t) Kimchi_types.opening_proof
  end

  module Poly_comm = Fp_poly_comm
  module Curve = Curve
end

module Proof = struct
  include Plonk_dlog_proof.Make (Vesta_inputs)

  (* Fat-proof variant of [create_async]: also returns the prover-computed
     oracle challenges, threaded to the wrap to skip recomputation. *)
  let create_with_oracles_async ?message pk ~primary ~auxiliary =
    let prev_chals, prev_comms = extract_challenges_and_commitments ~message in
    let%map.Promise res, oracles =
      Vesta_inputs.Backend.create_with_oracles_async pk ~primary ~auxiliary
        ~prev_chals ~prev_comms
    in
    (of_backend_with_public_evals res, oracles)
end

module Proving_key = struct
  type t = Keypair.t

  include
    Core_kernel.Binable.Of_binable
      (Core_kernel.Unit)
      (struct
        type nonrec t = t

        let to_binable _ = ()

        let of_binable () = failwith "TODO"
      end)

  let is_initialized _ = `Yes

  let set_constraint_system _ _ = ()

  let to_string _ = failwith "TODO"

  let of_string _ = failwith "TODO"
end

module Oracles = struct
  include Plonk_dlog_oracles.Make (struct
    module Verifier_index = Verification_key
    module Field = Field
    module Proof = Proof

    module Backend = struct
      include Kimchi_bindings.Protocol.Oracles.Fp

      let create = with_lagrange create

      let create_with_public_evals = with_lagrange create_with_public_evals
    end
  end)

  (* The oracle type, exposed for callers such as the fat-proof path. *)
  type t = Field.t Kimchi_types.oracles
end

module Cvar = Kimchi_pasta_snarky_backend.Vesta_based_plonk.Cvar

module Run_state = Kimchi_pasta_snarky_backend.Vesta_based_plonk.Run_state
