open Pickles.Impls.Step

module type Inputs = sig
  module Fp12 : sig
    type t

    module Circuit : sig
      type t

      val sparse_mul : t -> t -> t

      val one : unit -> t

      val square : t -> t

      val mul : t -> t -> t

      val assert_equal : t -> t -> unit

      val to_input : t -> Field.t Random_oracle_input.Chunked.t
    end

    val typ : (Circuit.t, t) Typ.t
  end

  module G2Affine : sig
    module Circuit : sig
      type t

      val create : 'a -> 'a -> t

      val x : t -> 'a

      val y : t -> 'a

      val neg : t -> t

      val add_from_line : t -> 'a -> t -> t

      val double_from_line : t -> 'a -> t

      val frobenius : t -> t

      val negative_frobenius : t -> t
    end
  end

  module Accumulator : sig
    type t

    module Circuit : sig
      type t

      val g_digest : t -> Field.t

      val set_g_digest : t -> Field.t -> t

      val t : t -> G2Affine.Circuit.t

      val set_t : t -> G2Affine.Circuit.t -> t

      val f : t -> Fp12.Circuit.t

      val set_f : t -> Fp12.Circuit.t -> t

      module Proof : sig
        val negA : t -> 'a

        val c : t -> 'a

        val c_inv : t -> 'a

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

      val open_ :
        Field.t array -> Fp12.Circuit.t array -> Field.t array -> Field.t
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

    val frobenius_lines : G2Line.Circuit.t array -> 'a array
  end
end

module Make_zkp0_to_6_ate_loop (Range : sig
  val begin_ : int

  val end_ : int
end)
(Inputs : Inputs) =
struct
  open Range
  open Inputs

  let delta_lines = LineParser.parse begin_ end_ VK.delta_lines

  let gamma_lines = LineParser.parse begin_ end_ VK.gamma_lines

  let ate_loop (acc, lines_hashes, all_b_lines) (a_cache, c_cache, pi_cache) =
    let t =
      if begin_ = 1 then
        let b = Accumulator.Circuit.Proof.b !acc in
        G2Affine.Circuit.create (G2Affine.Circuit.x b) (G2Affine.Circuit.y b)
      else Accumulator.Circuit.t !acc
    in
    let t = ref t in
    let negB = G2Affine.Circuit.neg (Accumulator.Circuit.Proof.b !acc) in

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
      g := Fp12.Circuit.sparse_mul !g (G2Line.Circuit.psi delta_line c_cache) ;
      g := Fp12.Circuit.sparse_mul !g (G2Line.Circuit.psi gamma_line pi_cache) ;

      t := G2Affine.Circuit.double_from_line !t (G2Line.Circuit.lambda b_line) ;

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

          g := Fp12.Circuit.sparse_mul !g (G2Line.Circuit.psi b_line a_cache) ;
          g :=
            Fp12.Circuit.sparse_mul !g (G2Line.Circuit.psi delta_line c_cache) ;
          g :=
            Fp12.Circuit.sparse_mul !g (G2Line.Circuit.psi gamma_line pi_cache)
          )
        else ()
      in

      lines_hashes.(!idx) <-
        Random_oracle.Checked.hash
          (Random_oracle.Checked.pack_input (Fp12.Circuit.to_input !g))
    done ;
    acc := Accumulator.Circuit.set_t !acc !t
end

module Make_zkp0_to_5 (Range : sig
  val zkp_id : int

  val begin_ : int

  val end_ : int
end)
(Inputs : Inputs) =
struct
  open Range
  open Inputs
  module Ate_loop = Make_zkp0_to_6_ate_loop (Range) (Inputs)

  let auxiliary_input_typ =
    Typ.tuple3 Accumulator.typ
      (Typ.array ~length:(Array.length ate_loop_count) Field.typ)
      (Typ.array ~length:91 G2Line.typ)

  let tags, cache, proof, provers =
    Pickles.compile
      ~public_input:(Input_and_output (Field.typ, Field.typ))
      ~auxiliary_typ:Typ.unit
      ~max_proofs_verified:(module Pickles_types.Nat.N0)
      ~name:(Format.sprintf "zkp%i" zkp_id)
      ~choices:(fun ~self:_ ->
        [ { identifier = "main"
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

                Ate_loop.ate_loop
                  (acc, lines_hashes, all_b_lines)
                  (a_cache, c_cache, pi_cache) ;

                let new_g_digest = ArrayListHasher.Circuit.hash lines_hashes in
                acc := Accumulator.Circuit.set_g_digest !acc new_g_digest ;

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

module Make_zkp0 (Inputs : Inputs) =
  Make_zkp0_to_5
    (struct
      open Inputs

      let zkp_id = 0

      let begin_ = 1

      let end_ = Array.length ate_loop_count - 55
    end)
    (Inputs)

module Make_zkp1 (Inputs : Inputs) =
  Make_zkp0_to_5
    (struct
      open Inputs

      let zkp_id = 1

      let begin_ = Array.length ate_loop_count - 55

      let end_ = Array.length ate_loop_count - 45
    end)
    (Inputs)

module Make_zkp2 (Inputs : Inputs) =
  Make_zkp0_to_5
    (struct
      open Inputs

      let zkp_id = 2

      let begin_ = Array.length ate_loop_count - 45

      let end_ = Array.length ate_loop_count - 35
    end)
    (Inputs)

module Make_zkp3 (Inputs : Inputs) =
  Make_zkp0_to_5
    (struct
      open Inputs

      let zkp_id = 3

      let begin_ = Array.length ate_loop_count - 35

      let end_ = Array.length ate_loop_count - 25
    end)
    (Inputs)

module Make_zkp4 (Inputs : Inputs) =
  Make_zkp0_to_5
    (struct
      open Inputs

      let zkp_id = 4

      let begin_ = Array.length ate_loop_count - 25

      let end_ = Array.length ate_loop_count - 15
    end)
    (Inputs)

module Make_zkp5 (Inputs : Inputs) =
  Make_zkp0_to_5
    (struct
      open Inputs

      let zkp_id = 5

      let begin_ = Array.length ate_loop_count - 15

      let end_ = Array.length ate_loop_count - 6
    end)
    (Inputs)

module Make_zkp6 (Inputs : Inputs) = struct
  open Inputs

  module Range = struct
    let zkp_id = 6

    let begin_ = Array.length ate_loop_count - 6

    let end_ = Array.length ate_loop_count
  end

  open Range
  module Ate_loop = Make_zkp0_to_6_ate_loop (Range) (Inputs)

  let auxiliary_input_typ =
    Typ.tuple3 Accumulator.typ
      (Typ.array ~length:(Array.length ate_loop_count) Field.typ)
      (Typ.array ~length:91 G2Line.typ)

  let tags, cache, proof, provers =
    Pickles.compile
      ~public_input:(Input_and_output (Field.typ, Field.typ))
      ~auxiliary_typ:Typ.unit
      ~max_proofs_verified:(module Pickles_types.Nat.N0)
      ~name:(Format.sprintf "zkp%i" zkp_id)
      ~choices:(fun ~self:_ ->
        [ { identifier = "main"
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

                Ate_loop.ate_loop
                  (acc, lines_hashes, all_b_lines)
                  (a_cache, c_cache, pi_cache) ;

                let t = ref (Accumulator.Circuit.t !acc) in

                (* frobenius part: *)
                let frob_line_cnt = ref 0 in

                let frob_b_lines = LineParser.frobenius_lines all_b_lines in
                let frob_delta_lines =
                  LineParser.frobenius_lines VK.delta_lines
                in
                let frob_gamma_lines =
                  LineParser.frobenius_lines VK.gamma_lines
                in

                let b_line = frob_b_lines.(!frob_line_cnt) in
                let delta_line = frob_delta_lines.(!frob_line_cnt) in
                let gamma_line = frob_gamma_lines.(!frob_line_cnt) in
                frob_line_cnt := !frob_line_cnt + 1 ;

                let g = ref (G2Line.Circuit.psi b_line a_cache) in
                g :=
                  Fp12.Circuit.sparse_mul !g
                    (G2Line.Circuit.psi delta_line c_cache) ;
                g :=
                  Fp12.Circuit.sparse_mul !g
                    (G2Line.Circuit.psi gamma_line pi_cache) ;

                let piB =
                  G2Affine.Circuit.frobenius (Accumulator.Circuit.Proof.b !acc)
                in
                G2Line.Circuit.assert_is_line b_line !t piB ;
                t :=
                  G2Affine.Circuit.add_from_line !t
                    (G2Line.Circuit.lambda b_line)
                    piB ;

                let b_line = frob_b_lines.(!frob_line_cnt) in
                let delta_line = frob_delta_lines.(!frob_line_cnt) in
                let gamma_line = frob_gamma_lines.(!frob_line_cnt) in

                let pi_2_B = G2Affine.Circuit.negative_frobenius piB in
                G2Line.Circuit.assert_is_line b_line !t pi_2_B ;

                g :=
                  Fp12.Circuit.sparse_mul !g (G2Line.Circuit.psi b_line a_cache) ;
                g :=
                  Fp12.Circuit.sparse_mul !g
                    (G2Line.Circuit.psi delta_line c_cache) ;
                g :=
                  Fp12.Circuit.sparse_mul !g
                    (G2Line.Circuit.psi gamma_line pi_cache) ;

                lines_hashes.(Array.length ate_loop_count - 1) <-
                  Random_oracle.Checked.hash
                    (Random_oracle.Checked.pack_input (Fp12.Circuit.to_input !g)) ;

                (* Assert that witnessed inverse is correct *)
                Fp12.Circuit.assert_equal
                  (Fp12.Circuit.mul
                     (Accumulator.Circuit.Proof.c_inv !acc)
                     (Accumulator.Circuit.Proof.c !acc) )
                  (Fp12.Circuit.one ()) ;

                let new_g_digest = ArrayListHasher.Circuit.hash lines_hashes in
                acc := Accumulator.Circuit.set_t !acc !t ;
                acc := Accumulator.Circuit.set_g_digest !acc new_g_digest ;

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

module Make_zkp7_to_12 (Range : sig
  val zkp_id : int

  val prefix : int

  val iterations : int
end)
(Inputs : Inputs) =
struct
  open Range
  open Inputs

  let update_f acc g_chunk =
    let f = ref (Accumulator.Circuit.f !acc) in

    let idx = ref 0 in

    for i = 1 + prefix to prefix + iterations do
      f := Fp12.Circuit.mul (Fp12.Circuit.square !f) g_chunk.(!idx) ;
      if ate_loop_count.(i) = 1 then
        f := Fp12.Circuit.mul !f (Accumulator.Circuit.Proof.c_inv !acc)
      else if ate_loop_count.(i) = -1 then
        f := Fp12.Circuit.mul !f (Accumulator.Circuit.Proof.c !acc)
      else () ;
      idx := !idx + 1
    done ;

    acc := Accumulator.Circuit.set_f !acc !f

  let auxiliary_input_typ =
    Typ.tuple2 Accumulator.typ
      (Typ.tuple3
         (Typ.array ~length:prefix Field.typ)
         (Typ.array ~length:iterations Fp12.typ)
         (Typ.array
            ~length:(Array.length ate_loop_count - prefix - iterations)
            Field.typ ) )

  let tags, cache, proof, provers =
    Pickles.compile
      ~public_input:(Input_and_output (Field.typ, Field.typ))
      ~auxiliary_typ:Typ.unit
      ~max_proofs_verified:(module Pickles_types.Nat.N0)
      ~name:(Format.sprintf "zkp%i" zkp_id)
      ~choices:(fun ~self:_ ->
        [ { identifier = "main"
          ; prevs = []
          ; main =
              (fun { public_input = input } ->
                let acc, (lhs_lines_hashes, g_chunk, rhs_lines_hashes) =
                  exists auxiliary_input_typ ~compute:(fun () ->
                      failwith "TODO" )
                in
                (* Accomodate rampant mutability in o1js *)
                let acc = ref acc in

                Field.Assert.equal input
                  (Random_oracle.Checked.hash
                     (Random_oracle.Checked.pack_input
                        (Accumulator.Circuit.to_input !acc) ) ) ;

                let opening =
                  ArrayListHasher.Circuit.open_ lhs_lines_hashes g_chunk
                    rhs_lines_hashes
                in
                Field.Assert.equal (Accumulator.Circuit.g_digest !acc) opening ;

                update_f acc g_chunk ;

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

module Make_zkp7 (Inputs : Inputs) =
  Make_zkp7_to_12
    (struct
      let zkp_id = 7

      let prefix = 0

      let iterations = 9
    end)
    (Inputs)

module Make_zkp8 (Inputs : Inputs) =
  Make_zkp7_to_12
    (struct
      let zkp_id = 8

      let prefix = 9

      let iterations = 11
    end)
    (Inputs)

module Make_zkp9 (Inputs : Inputs) =
  Make_zkp7_to_12
    (struct
      let zkp_id = 9

      let prefix = 9 + 11

      let iterations = 11
    end)
    (Inputs)

module Make_zkp10 (Inputs : Inputs) =
  Make_zkp7_to_12
    (struct
      let zkp_id = 10

      let prefix = 9 + 11 + 11

      let iterations = 11
    end)
    (Inputs)

module Make_zkp11 (Inputs : Inputs) =
  Make_zkp7_to_12
    (struct
      let zkp_id = 11

      let prefix = 9 + 11 + 11 + 11

      let iterations = 11
    end)
    (Inputs)

module Make_zkp12 (Inputs : Inputs) =
  Make_zkp7_to_12
    (struct
      let zkp_id = 12

      let prefix = 9 + 11 + 11 + 11 + 11

      let iterations = 11
    end)
    (Inputs)
