open Pickles.Impls.Step

module type Inputs = sig
  module G2Affine : sig
    module Circuit : sig
      type t

      val create : 'a -> 'a -> t

      val x : t -> 'a

      val y : t -> 'a

      val neg : t -> t

      val add_from_line : t -> 'a -> t -> t

      val double_from_line : t -> 'a -> t
    end
  end

  module Accumulator : sig
    type t

    module Circuit : sig
      type t

      val g_digest : t -> Field.t

      module Proof : sig
        val negA : t -> 'a

        val c : t -> 'a

        val pi : t -> 'a

        val b : t -> G2Affine.Circuit.t
      end

      val to_input : t -> Field.t Random_oracle_input.Chunked.t
    end

    val typ : (Circuit.t, t) Typ.t
  end

  val ate_loop_count : int array

  module ArrayListHasher : sig
    module Circuit : sig
      val hash : Field.t array -> Field.t
    end
  end

  module AffineCache : sig
    module Circuit : sig
      type t

      val create : 'a -> t
    end
  end

  module VK : sig
    val delta_lines : 'a

    val gamma_lines : 'a
  end

  module Fp12 : sig
    module Circuit : sig
      type t

      val sparse_mul : t -> t -> t

      val to_input : t -> Field.t Random_oracle_input.Chunked.t
    end
  end

  module G2Line : sig
    type t

    module Circuit : sig
      type t

      val assert_is_tangent : t -> G2Affine.Circuit.t -> unit

      val assert_is_line : t -> G2Affine.Circuit.t -> G2Affine.Circuit.t -> unit

      val psi : t -> AffineCache.Circuit.t -> Fp12.Circuit.t

      val lambda : t -> 'a
    end

    val typ : (Circuit.t, t) Typ.t
  end

  module LineParser : sig
    val parse : int -> int -> G2Line.Circuit.t array -> G2Line.Circuit.t array
  end
end

module Make (Inputs : Inputs) = struct
  open Inputs

  let begin_ = 1

  let end_ = Array.length ate_loop_count - 55

  let delta_lines = LineParser.parse begin_ end_ VK.delta_lines

  let gamma_lines = LineParser.parse begin_ end_ VK.gamma_lines

  let auxiliary_input_typ =
    Typ.tuple3 Accumulator.typ
      (Typ.array ~length:(Array.length ate_loop_count) Field.typ)
      (Typ.array ~length:91 G2Line.typ)

  let tags, cache, proof, provers =
    Pickles.compile
      ~public_input:(Input_and_output (Field.typ, Field.typ))
      ~auxiliary_typ:Typ.unit
      ~max_proofs_verified:(module Pickles_types.Nat.N0)
      ~name:"groth16_conversion_0"
      ~choices:(fun ~self:_ ->
        [ { identifier = "groth16_conversion_0"
          ; prevs = []
          ; main =
              (fun { public_input = input } ->
                let acc, lines_hashes, all_b_lines =
                  exists auxiliary_input_typ ~compute:(fun () ->
                      failwith "TODO" )
                in
                (* Accomodate rampant mutability in o1js *)
                let acc = ref acc in

                Field.Assert.equal input
                  (Random_oracle.Checked.hash
                     (Random_oracle.Checked.pack_input
                        (Accumulator.Circuit.to_input !acc) ) ) ;
                Field.Assert.equal
                  (Accumulator.Circuit.g_digest !acc)
                  (ArrayListHasher.Circuit.hash lines_hashes) ;

                let a_cache =
                  AffineCache.Circuit.create
                    (Accumulator.Circuit.Proof.negA !acc)
                in
                let c_cache =
                  AffineCache.Circuit.create (Accumulator.Circuit.Proof.c !acc)
                in
                let pi_cache =
                  AffineCache.Circuit.create (Accumulator.Circuit.Proof.pi !acc)
                in

                let t =
                  let b = Accumulator.Circuit.Proof.b !acc in
                  G2Affine.Circuit.create (G2Affine.Circuit.x b)
                    (G2Affine.Circuit.y b)
                in
                let t = ref t in
                let negB =
                  G2Affine.Circuit.neg (Accumulator.Circuit.Proof.b !acc)
                in

                ignore (negB : _) ;

                let b_lines = LineParser.parse begin_ end_ all_b_lines in

                let idx = ref 0 in
                let line_cnt = ref 0 in

                for i = begin_ to end_ - 1 do
                  idx := i - 1 ;

                  let b_line = b_lines.(!line_cnt) in
                  let delta_line = delta_lines.(!line_cnt) in
                  let gamma_line = gamma_lines.(!line_cnt) in
                  line_cnt := !line_cnt + 1 ;

                  G2Line.Circuit.assert_is_tangent b_line !t ;

                  let g = ref (G2Line.Circuit.psi b_line a_cache) in
                  g :=
                    Fp12.Circuit.sparse_mul !g
                      (G2Line.Circuit.psi delta_line c_cache) ;
                  g :=
                    Fp12.Circuit.sparse_mul !g
                      (G2Line.Circuit.psi gamma_line pi_cache) ;

                  t :=
                    G2Affine.Circuit.double_from_line !t
                      (G2Line.Circuit.lambda b_line) ;

                  let () =
                    if ate_loop_count.(i) = 1 || ate_loop_count.(i) = -1 then (
                      let b_line = b_lines.(!line_cnt) in
                      let delta_line = delta_lines.(!line_cnt) in
                      let gamma_line = gamma_lines.(!line_cnt) in
                      line_cnt := !line_cnt + 1 ;

                      if ate_loop_count.(i) = 1 then (
                        G2Line.Circuit.assert_is_line b_line !t
                          (Accumulator.Circuit.Proof.b !acc) ;
                        t :=
                          G2Affine.Circuit.add_from_line !t
                            (G2Line.Circuit.lambda b_line)
                            (Accumulator.Circuit.Proof.b !acc) )
                      else (
                        G2Line.Circuit.assert_is_line b_line !t negB ;
                        t :=
                          G2Affine.Circuit.add_from_line !t
                            (G2Line.Circuit.lambda b_line)
                            negB ) ;

                      g :=
                        Fp12.Circuit.sparse_mul !g
                          (G2Line.Circuit.psi b_line a_cache) ;
                      g :=
                        Fp12.Circuit.sparse_mul !g
                          (G2Line.Circuit.psi delta_line c_cache) ;
                      g :=
                        Fp12.Circuit.sparse_mul !g
                          (G2Line.Circuit.psi gamma_line pi_cache) )
                    else ()
                  in

                  lines_hashes.(!idx) <-
                    Random_oracle.Checked.hash
                      (Random_oracle.Checked.pack_input
                         (Fp12.Circuit.to_input !g) )
                done ;

                let public_output =
                  Random_oracle.Checked.hash
                    (Random_oracle.Checked.pack_input
                       (Accumulator.Circuit.to_input !acc) )
                in
                { previous_proof_statements = []
                ; public_output
                ; auxiliary_output = ()
                } )
          ; feature_flags = Pickles_types.Plonk_types.Features.none_bool
          }
        ] )
      ()
end
