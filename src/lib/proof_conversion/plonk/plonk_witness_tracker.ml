(** Out-of-circuit computation for PLONK proof conversion witnesses.

    Computes values needed by the prover (e.g., Poseidon hashes of
    accumulator state) without circuit constraints. *)

open! Core_kernel
module Step = Pickles.Impls.Step

(** Convert a circuit-level Chunked input to constants.
    Works when all Cvars are [Cvar.constant] (as from [of_constant]). *)
let chunked_input_to_const
    (input : Step.Field.t Random_oracle_input.Chunked.t) :
    Step.Field.Constant.t Random_oracle_input.Chunked.t =
  let read x = Option.value_exn (Step.Field.to_constant x) in
  { field_elements = Array.map input.field_elements ~f:read
  ; packeds = Array.map input.packeds ~f:(fun (x, n) -> (read x, n))
  }

(** Compute the Poseidon hash of an accumulator constant, matching
    in-circuit hash_packed.  Uses native Poseidon (no snarky overhead). *)
let hash_accumulator_const (acc_const : Plonk_accumulator.t_const) :
    Step.Field.Constant.t =
  let acc = Plonk_accumulator.of_constant acc_const in
  let input = Plonk_accumulator.to_input acc in
  let input_const = chunked_input_to_const input in
  let packed = Random_oracle.pack_input input_const in
  Random_oracle.hash packed

(** Compute the Poseidon hash of a KZG accumulator constant.
    Uses native Poseidon (no snarky overhead). *)
let hash_kzg_accumulator_const (kzg_const : Kzg_accumulator.t_const) :
    Step.Field.Constant.t =
  let kzg = Kzg_accumulator.of_constant kzg_const in
  let input = Kzg_accumulator.to_input kzg in
  let input_const = chunked_input_to_const input in
  let packed = Random_oracle.pack_input input_const in
  Random_oracle.hash packed

(** Extract KZG A/B points from the accumulator state after circuit 11.
    Runs prepare_pairing_1 via run_unchecked (a few EC operations, fast).
    Returns (a_x, a_y, neg_b_x, neg_b_y) as Bignum_bigint values. *)
let extract_kzg_points_from_state11 (acc11 : Plonk_accumulator.t_const) :
    Bignum_bigint.t * Bignum_bigint.t * Bignum_bigint.t * Bignum_bigint.t =
  let module FF = Snarky_foreign_field.Foreign_field in
  let result =
    ref (Bignum_bigint.zero, Bignum_bigint.zero, Bignum_bigint.zero,
         Bignum_bigint.zero)
  in
  Snarky_backendless.Snark0.set_eval_constraints false ;
  Step.run_unchecked (fun () ->
      let acc = Plonk_accumulator.of_constant acc11 in
      let ax, ay =
        Piop.prepare_pairing_1 ~vk:Plonk_circuits.plonk_vk ~proof:acc.proof
          ~random:acc.state.kzg_random ~folded_cm_x:acc.state.kzg_cm_x
          ~folded_cm_y:acc.state.kzg_cm_y ~zeta:acc.fs.zeta
      in
      Step.as_prover (fun () ->
          let read f =
            Step.As_prover.read (FF.FpA.typ ~f:Bn254_params.p) f
          in
          result := (read ax, read ay,
                     read acc.state.neg_fq_x, read acc.state.neg_fq_y) ) ) ;
  Snarky_backendless.Snark0.set_eval_constraints true ;
  !result

(** Compute KZG Miller loop output from pre-extracted A/B points.
    Calls the Rust FFI pairing computation. *)
let compute_mlo_from_points ~(a_x : Bignum_bigint.t) ~(a_y : Bignum_bigint.t)
    ~(neg_b_x : Bignum_bigint.t) ~(neg_b_y : Bignum_bigint.t) :
    Fp12.Constant.t =
  let module WT = Witness_tracker in
  let module BI = Bignum_bigint in
  let g2 : WT.G2.t =
    { x =
        ( BI.of_string
            "10857046999023057135944570762232829481370756359578518086990519993285655852781"
        , BI.of_string
            "11559732032986387107991004021392285783925812861821192530917403151452391805634"
        )
    ; y =
        ( BI.of_string
            "8495653923123431417604973247489272438418190587263600148770280649306958101930"
        , BI.of_string
            "4082367875863433681332203403145435568316851327593401208105741076214120093531"
        )
    }
  in
  let tau : WT.G2.t =
    { x =
        ( BI.of_string
            "19089565590083334368588890253123139704298730990782503769911324779715431555531"
        , BI.of_string
            "15805639136721018565402881920352193254830339253282065586954346329754995870280"
        )
    ; y =
        ( BI.of_string
            "6779728121489434657638426458390319301070371227460768374343986326751507916979"
        , BI.of_string
            "9779648407879205346559610309258181044130619080926897934572699915909528404984"
        )
    }
  in
  let a_g1 : WT.G1.t = { x = a_x; y = a_y } in
  let neg_b_g1 : WT.G1.t = { x = neg_b_x; y = neg_b_y } in
  WT.compute_kzg_pairing_mlo ~a:a_g1 ~neg_b:neg_b_g1 ~g2 ~tau

(** Run a circuit via run_unchecked with a witness handler.
    Returns the output hash. *)
let run_circuit_unchecked ~(n : int) ~(input_hash : Step.Field.Constant.t)
    ~(witness : Plonk_requests.witness) : Step.Field.Constant.t =
  let handler = Plonk_requests.handler witness in
  Step.run_unchecked (fun () ->
      Step.handle
        (fun () ->
          let body = Plonk_circuits.circuit_body n in
          let input_var = Step.Field.constant input_hash in
          let output_var = body input_var in
          Step.As_prover.read_var output_var )
        handler )

(** Run circuits 0-11 unchecked to evolve the PLONK accumulator,
    then extract KZG A/B points from circuit 12 and compute the
    Miller loop output via Rust FFI. Returns the Fp12 MLO. *)
let compute_kzg_mlo (initial_acc : Plonk_accumulator.t_const) : Fp12.Constant.t
    =
  let module FF = Snarky_foreign_field.Foreign_field in
  (* Disable constraint evaluation for speed *)
  Snarky_backendless.Snark0.set_eval_constraints false ;
  (* Run circuits 0-11 to evolve the accumulator *)
  let current_hash = ref (hash_accumulator_const initial_acc) in
  let current_acc = ref initial_acc in
  let zkp_fns =
    Plonk_circuits.
      [| zkp0
       ; zkp1
       ; zkp2
       ; zkp3
       ; zkp4
       ; zkp5
       ; zkp6
       ; zkp7
       ; zkp8
       ; zkp9
       ; zkp10
       ; zkp11
      |]
  in
  for n = 0 to 11 do
    Printf.eprintf "  Running zkp%d unchecked...\n%!" n ;
    let witness : Plonk_requests.witness =
      { Plonk_requests.empty_witness with plonk_acc = Some !current_acc }
    in
    let handler = Plonk_requests.handler witness in
    let result = ref (Step.Field.Constant.zero, !current_acc) in
    Step.run_unchecked (fun () ->
        Step.handle
          (fun () ->
            let input_var = Step.Field.constant !current_hash in
            let output_hash, acc = zkp_fns.(n) input_var in
            Step.as_prover (fun () ->
                let oh = Step.As_prover.read_var output_hash in
                let acc_const = Step.As_prover.read Plonk_accumulator.typ acc in
                result := (oh, acc_const) ) )
          handler ) ;
    let output_hash, new_acc = !result in
    current_hash := output_hash ;
    current_acc := new_acc
  done ;
  (* Run circuit 12's logic unchecked to get KZG A/B points.
     c/shift_power don't affect A/B computation. *)
  let witness : Plonk_requests.witness =
    { Plonk_requests.empty_witness with
      plonk_acc = Some !current_acc
    ; shift_power = Some Step.Field.Constant.zero
    ; c_fp12 = Some Fp12.Constant.one
    }
  in
  let handler = Plonk_requests.handler witness in
  let module BI = Bignum_bigint in
  let kzg_result = ref (BI.zero, BI.zero, BI.zero, BI.zero) in
  Step.run_unchecked (fun () ->
      Step.handle
        (fun () ->
          let _output_hash, kzg =
            Plonk_circuits.zkp12 (Step.Field.constant !current_hash)
          in
          Step.as_prover (fun () ->
              let read_fpa f =
                Step.As_prover.read (FF.FpA.typ ~f:Bn254_params.p) f
              in
              let ax = read_fpa kzg.proof.a_x in
              let ay = read_fpa kzg.proof.a_y in
              let nbx = read_fpa kzg.proof.neg_b_x in
              let nby = read_fpa kzg.proof.neg_b_y in
              kzg_result := (ax, ay, nbx, nby) ) )
        handler ) ;
  let a_x, a_y, neg_b_x, neg_b_y = !kzg_result in
  Snarky_backendless.Snark0.set_eval_constraints true ;
  (* Compute the KZG MLO using the same out-of-circuit arithmetic
     as the Groth16 tracker (matching circuit convention). *)
  let module WT = Witness_tracker in
  let module BI = Bignum_bigint in
  (* SRS G2 points *)
  let g2 : WT.G2.t =
    { x =
        ( BI.of_string
            "10857046999023057135944570762232829481370756359578518086990519993285655852781"
        , BI.of_string
            "11559732032986387107991004021392285783925812861821192530917403151452391805634"
        )
    ; y =
        ( BI.of_string
            "8495653923123431417604973247489272438418190587263600148770280649306958101930"
        , BI.of_string
            "4082367875863433681332203403145435568316851327593401208105741076214120093531"
        )
    }
  in
  let tau : WT.G2.t =
    { x =
        ( BI.of_string
            "19089565590083334368588890253123139704298730990782503769911324779715431555531"
        , BI.of_string
            "15805639136721018565402881920352193254830339253282065586954346329754995870280"
        )
    ; y =
        ( BI.of_string
            "6779728121489434657638426458390319301070371227460768374343986326751507916979"
        , BI.of_string
            "9779648407879205346559610309258181044130619080926897934572699915909528404984"
        )
    }
  in
  let a_g1 : WT.G1.t = { x = a_x; y = a_y } in
  let neg_b_g1 : WT.G1.t = { x = neg_b_x; y = neg_b_y } in
  WT.compute_kzg_pairing_mlo ~a:a_g1 ~neg_b:neg_b_g1 ~g2 ~tau
