(** Dump initial Groth16 accumulator toFields for comparison with nori. *)
open Core_kernel

module Step = Pickles.Impls.Step
module WT = Proof_conversion.Witness_tracker
module FF = Snarky_foreign_field.Foreign_field

let () =
  let proof =
    Proof_conversion.Proof_json.load_proof "/tmp/groth16_test/proof.json"
  in
  let vk = Proof_conversion.Proof_json.load_vk "/tmp/groth16_test/vk.json" in
  let aux =
    Proof_conversion.Proof_json.load_aux_witness
      "/tmp/groth16_test/aux_witness.json"
  in
  let tracker = WT.create ~proof ~vk ~aux in
  let n_total = Array.length Proof_conversion.Bn254_params.ate_loop_count in
  let initial_g_digest =
    let zeros = Array.create ~len:n_total Step.Field.Constant.zero in
    Random_oracle.hash zeros
  in
  let initial_acc = WT.get_accumulator_constant tracker in
  let initial_acc =
    { initial_acc with
      state =
        { g_digest = initial_g_digest
        ; t_point = initial_acc.proof.b
        ; f =
            ( Proof_conversion.Fp6.Constant.zero
            , Proof_conversion.Fp6.Constant.zero )
        }
    }
  in
  (* Dump by witnessing and reading back each FpA limb *)
  let fields =
    Step.run_and_check_exn (fun () ->
        let acc =
          Step.exists Proof_conversion.Accumulator.typ ~compute:(fun () ->
              initial_acc )
        in
        (* Extract all FpA fields from the accumulator *)
        let q = Queue.create () in
        let add_fpa x =
          let l0, l1, l2 = FF.Field3.vars (FF.FpA.to_field3 x) in
          Queue.enqueue q l0 ; Queue.enqueue q l1 ; Queue.enqueue q l2
        in
        let add_g1 (g : Proof_conversion.G1.Circuit.t) =
          add_fpa g.x ; add_fpa g.y
        in
        let add_g2 (g : Proof_conversion.G2.Circuit.t) =
          add_fpa g.x.c0 ; add_fpa g.x.c1 ; add_fpa g.y.c0 ; add_fpa g.y.c1
        in
        let add_fp12 (f : Proof_conversion.Fp12.Circuit.t) =
          add_fpa f.c0.c0.c0 ;
          add_fpa f.c0.c0.c1 ;
          add_fpa f.c0.c1.c0 ;
          add_fpa f.c0.c1.c1 ;
          add_fpa f.c0.c2.c0 ;
          add_fpa f.c0.c2.c1 ;
          add_fpa f.c1.c0.c0 ;
          add_fpa f.c1.c0.c1 ;
          add_fpa f.c1.c1.c0 ;
          add_fpa f.c1.c1.c1 ;
          add_fpa f.c1.c2.c0 ;
          add_fpa f.c1.c2.c1
        in
        (* proof: negA, B, C, PI, c_fp12, c_inv, shift_power *)
        add_g1 acc.proof.neg_a ;
        add_g2 acc.proof.b ;
        add_g1 acc.proof.c ;
        add_g1 acc.proof.pi ;
        add_fp12 acc.proof.c_fp12 ;
        add_fp12 acc.proof.c_inv ;
        Queue.enqueue q acc.proof.shift_power ;
        (* state: T, f, g_digest *)
        add_g2 acc.state.t_point ;
        add_fp12 acc.state.f ;
        Queue.enqueue q acc.state.g_digest ;
        let arr = Queue.to_array q in
        fun () ->
          Printf.printf "Accumulator has %d fields\n%!" (Array.length arr) ;
          Array.iteri arr ~f:(fun i f ->
              let v = Step.As_prover.read_var f in
              Printf.printf "  [%d]: %s\n%!" i (Step.Field.Constant.to_string v) ) )
  in
  ignore fields ; Printf.eprintf "Done.\n%!"
