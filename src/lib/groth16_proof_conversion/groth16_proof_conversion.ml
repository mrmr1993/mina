open Pickles.Impls.Step

module type Inputs = sig
  val switch_ : Boolean.var list -> ('a, _) Typ.t -> 'a list -> 'a

  val array_to_input :
       ('a -> Field.t Random_oracle_input.Chunked.t)
    -> 'a array
    -> Field.t Random_oracle_input.Chunked.t

  module rec FrA : sig
    type t

    module Circuit : sig
      type t

      val assertCanonical : t -> FrC.Circuit.t
    end

    val typ : (Circuit.t, t) Typ.t
  end

  and FrC : sig
    type t

    module Circuit : sig
      type t

      val assert_equal : t -> t -> unit

      val to_FrA : t -> FrA.Circuit.t

      val of_int : int -> t

      val to_input : t -> Field.t Random_oracle_input.Chunked.t
    end

    val typ : (Circuit.t, t) Typ.t
  end

  module Bn254 : sig
    type t

    module Circuit : sig
      type t

      val create : FrA.Circuit.t -> FrA.Circuit.t -> t

      val x : t -> FrA.Circuit.t

      val y : t -> FrA.Circuit.t

      val add : t -> t -> t

      val scale : t -> FrC.Circuit.t -> t
    end

    val typ : (Circuit.t, t) Typ.t
  end

  module Fp2 : sig
    type t

    module Circuit : sig
      type t

      val create : FrC.Circuit.t -> FrC.Circuit.t -> t

      val zero : unit -> t

      val add : t -> t -> t

      val neg : t -> t

      val mul : t -> t -> t

      val square : t -> t

      val mul_by_fp : t -> FrC.Circuit.t -> t

      val assert_equals : t -> t -> unit
    end

    val typ : (Circuit.t, t) Typ.t
  end

  module Fp6 : sig
    module Circuit : sig
      type t

      val create : Fp2.Circuit.t -> Fp2.Circuit.t -> Fp2.Circuit.t -> t
    end
  end

  module Fp12 : sig
    type t

    module Circuit : sig
      type t

      val create : Fp6.Circuit.t -> Fp6.Circuit.t -> t

      val if_ : Boolean.var -> then_:(unit -> t) -> else_:(unit -> t) -> t

      val sparse_mul : t -> t -> t

      val frobenius_pow_p : t -> t

      val frobenius_pow_p_squared : t -> t

      val frobenius_pow_p_cubed : t -> t

      val one : unit -> t

      val square : t -> t

      val mul : t -> t -> t

      val assert_equal : t -> t -> unit

      val to_input : t -> Field.t Random_oracle_input.Chunked.t
    end

    val typ : (Circuit.t, t) Typ.t
  end

  module G1Affine : sig
    type t

    module Circuit : sig
      type t

      val create : FrC.Circuit.t -> FrC.Circuit.t -> t

      val x : t -> FrC.Circuit.t

      val y : t -> FrC.Circuit.t

      val to_input : t -> Field.t Random_oracle_input.Chunked.t
    end

    val typ : (Circuit.t, t) Typ.t
  end

  module G2Affine : sig
    module Circuit : sig
      type t

      val create : Fp2.Circuit.t -> Fp2.Circuit.t -> t

      val x : t -> Fp2.Circuit.t

      val y : t -> Fp2.Circuit.t

      val neg : t -> t

      val add_from_line : t -> Fp2.Circuit.t -> t -> t

      val double_from_line : t -> Fp2.Circuit.t -> t

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

        val shift_power : t -> Field.t
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

      val create : G1Affine.Circuit.t -> t

      val xp_prime : t -> FrC.Circuit.t

      val yp_prime : t -> FrC.Circuit.t
    end
  end

  module G2Line : sig
    module Circuit : sig
      type t = { lambda : Fp2.Circuit.t; neg_mu : Fp2.Circuit.t }
    end
  end

  module VK : sig
    val delta_lines : G2Line.Circuit.t array

    val gamma_lines : G2Line.Circuit.t array

    val alpha_beta : Fp12.Circuit.t

    val w27 : Fp12.Circuit.t

    val w27_square : Fp12.Circuit.t

    val ic0 : Bn254.Circuit.t

    val ic1 : Bn254.Circuit.t

    val ic2 : Bn254.Circuit.t

    val ic3 : Bn254.Circuit.t

    val ic4 : Bn254.Circuit.t

    val ic5 : Bn254.Circuit.t
  end
end

module Make_G2Line (Inputs : Inputs) = struct
  open Inputs

  type t = { lambda : Fp2.t; neg_mu : Fp2.t }

  module Circuit = struct
    type t = G2Line.Circuit.t =
      { lambda : Fp2.Circuit.t; neg_mu : Fp2.Circuit.t }

    let psi self (cache : AffineCache.Circuit.t) =
      let g0 =
        Fp2.Circuit.create (FrC.Circuit.of_int 1) (FrC.Circuit.of_int 0)
      in
      let h0 =
        Fp2.Circuit.mul_by_fp self.lambda (AffineCache.Circuit.xp_prime cache)
      in
      let g1 = Fp2.Circuit.zero () in
      let h1 =
        Fp2.Circuit.mul_by_fp self.neg_mu (AffineCache.Circuit.yp_prime cache)
      in
      let g2 = Fp2.Circuit.zero () in
      let h2 = Fp2.Circuit.zero () in

      let c0 = Fp6.Circuit.create g0 g1 g2 in
      let c1 = Fp6.Circuit.create h0 h1 h2 in

      Fp12.Circuit.create c0 c1

    let evaluate self (p : G2Affine.Circuit.t) : Fp2.Circuit.t =
      let t = Fp2.Circuit.mul self.lambda (G2Affine.Circuit.x p) in
      let t = Fp2.Circuit.neg t in
      let t = Fp2.Circuit.add t self.neg_mu in
      Fp2.Circuit.add t (G2Affine.Circuit.y p)

    let assert_is_line self (t : G2Affine.Circuit.t) (q : G2Affine.Circuit.t) =
      let e1 = evaluate self t in
      let e2 = evaluate self q in

      Fp2.Circuit.assert_equals e1 (Fp2.Circuit.zero ()) ;
      Fp2.Circuit.assert_equals e2 (Fp2.Circuit.zero ())

    let assert_is_tangent self (p : G2Affine.Circuit.t) =
      let e = evaluate self p in
      Fp2.Circuit.assert_equals e (Fp2.Circuit.zero ()) ;

      let dbl_lambda_y =
        Fp2.Circuit.mul
          (Fp2.Circuit.add self.lambda self.lambda)
          (G2Affine.Circuit.y p)
      in
      let x_square = Fp2.Circuit.square (G2Affine.Circuit.x p) in
      Fp2.Circuit.assert_equals dbl_lambda_y
        (Fp2.Circuit.mul_by_fp x_square (FrC.Circuit.of_int 3))

    let lambda { lambda; _ } = lambda
  end

  (* TODO: Correct order? *)
  let typ =
    Typ.of_hlistable [ Fp2.typ; Fp2.typ ]
      ~var_to_hlist:(fun ({ lambda; neg_mu } : Circuit.t) -> [ lambda; neg_mu ])
      ~var_of_hlist:(fun [ lambda; neg_mu ] -> { lambda; neg_mu })
      ~value_to_hlist:(fun ({ lambda; neg_mu } : t) -> [ lambda; neg_mu ])
      ~value_of_hlist:(fun [ lambda; neg_mu ] -> { lambda; neg_mu })
end

module Line_parser (Inputs : Inputs) = struct
  open Inputs

  let ateCntSlice from to_ =
    let line_cnt = ref 0 in
    for i = from to to_ - 1 do
      if ate_loop_count.(i) = 0 then line_cnt := !line_cnt + 1
      else line_cnt := !line_cnt + 2
    done ;
    !line_cnt

  let parse from to_ lines =
    let start = ateCntSlice 1 from in
    let toSlice = ateCntSlice from to_ in
    Array.sub lines start toSlice

  let frobenius_lines lines = Array.sub lines (Array.length lines - 2) 2
end

module Make_zkp0_to_6_ate_loop (Range : sig
  val begin_ : int

  val end_ : int
end)
(Inputs : Inputs) =
struct
  open Range
  open Inputs
  module G2Line = Make_G2Line (Inputs)
  module LineParser = Line_parser (Inputs)

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
  open Ate_loop

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
  open Ate_loop

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

module Make_zkp7_to_13_update_f (Range : sig
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
  module Update_f = Make_zkp7_to_13_update_f (Range) (Inputs)

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

                Update_f.update_f acc g_chunk ;

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

module Make_zkp13 (Inputs : Inputs) = struct
  module Range = struct
    let zkp_id = 13

    let prefix = 64

    let iterations = 1
  end

  open Range
  open Inputs
  module Update_f = Make_zkp7_to_13_update_f (Range) (Inputs)

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

                Update_f.update_f acc g_chunk ;

                let f = ref (Accumulator.Circuit.f !acc) in

                (f :=
                   !f
                   |> (fun x ->
                        Fp12.Circuit.mul x
                          (Fp12.Circuit.frobenius_pow_p
                             (Accumulator.Circuit.Proof.c_inv !acc) ) )
                   |> (fun x ->
                        Fp12.Circuit.mul x
                          (Fp12.Circuit.frobenius_pow_p_squared
                             (Accumulator.Circuit.Proof.c !acc) ) )
                   |> (fun x ->
                        Fp12.Circuit.mul x
                          (Fp12.Circuit.frobenius_pow_p_cubed
                             (Accumulator.Circuit.Proof.c_inv !acc) ) )
                   |> fun x -> Fp12.Circuit.mul x VK.alpha_beta ) ;

                let shift =
                  let shift_power =
                    Accumulator.Circuit.Proof.shift_power !acc
                  in
                  switch_
                    [ Field.equal shift_power
                        (Field.constant (Field.Constant.of_int 0))
                    ; Field.equal shift_power
                        (Field.constant (Field.Constant.of_int 1))
                    ; Field.equal shift_power
                        (Field.constant (Field.Constant.of_int 2))
                    ]
                    Fp12.typ
                    [ Fp12.Circuit.one (); VK.w27; VK.w27_square ]
                in

                f := Fp12.Circuit.mul !f shift ;

                Fp12.Circuit.assert_equal !f (Fp12.Circuit.one ()) ;

                acc := Accumulator.Circuit.set_f !acc !f ;

                let public_output =
                  let pi = Accumulator.Circuit.Proof.pi !acc in
                  Random_oracle.Checked.hash
                    (Random_oracle.Checked.pack_input
                       (G1Affine.Circuit.to_input pi) )
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

module Make_zkp14 (Inputs : Inputs) = struct
  module Range = struct
    let zkp_id = 14
  end

  open Range
  open Inputs

  let auxiliary_input_typ = Typ.array ~length:5 FrC.typ

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
                let pis =
                  exists auxiliary_input_typ ~compute:(fun () ->
                      failwith "TODO" )
                in

                let pis_hash =
                  Random_oracle.Checked.hash
                    (Random_oracle.Checked.pack_input
                       (array_to_input FrC.Circuit.to_input pis) )
                in

                let acc = Bn254.Circuit.(create (x VK.ic0) (y VK.ic0)) in
                let acc =
                  Bn254.Circuit.add acc (Bn254.Circuit.scale VK.ic1 pis.(0))
                in
                let acc =
                  Bn254.Circuit.add acc (Bn254.Circuit.scale VK.ic2 pis.(1))
                in
                let acc =
                  Bn254.Circuit.add acc (Bn254.Circuit.scale VK.ic3 pis.(2))
                in

                let acc_aff =
                  G1Affine.Circuit.create
                    (FrA.Circuit.assertCanonical (Bn254.Circuit.x acc))
                    (FrA.Circuit.assertCanonical (Bn254.Circuit.y acc))
                in
                let acc_hash =
                  Random_oracle.Checked.hash
                    (Random_oracle.Checked.pack_input
                       (G1Affine.Circuit.to_input acc_aff) )
                in

                let public_output =
                  Random_oracle.Checked.hash
                    (Random_oracle.Checked.pack_input
                       (array_to_input Random_oracle_input.Chunked.field
                          [| input; pis_hash; acc_hash |] ) )
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

module Make_zkp15 (Inputs : Inputs) = struct
  module Range = struct
    let zkp_id = 15
  end

  open Range
  open Inputs

  let auxiliary_input_typ =
    Typ.tuple3 G1Affine.typ G1Affine.typ (Typ.array ~length:5 FrC.typ)

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
                let pi, acc, pis =
                  exists auxiliary_input_typ ~compute:(fun () ->
                      failwith "TODO" )
                in

                let pi_hash =
                  Random_oracle.Checked.hash
                    (Random_oracle.Checked.pack_input
                       (G1Affine.Circuit.to_input pi) )
                in
                let pis_hash =
                  Random_oracle.Checked.hash
                    (Random_oracle.Checked.pack_input
                       (array_to_input FrC.Circuit.to_input pis) )
                in
                let acc_hash =
                  Random_oracle.Checked.hash
                    (Random_oracle.Checked.pack_input
                       (G1Affine.Circuit.to_input acc) )
                in
                Field.Assert.equal input
                  (Random_oracle.Checked.hash
                     (Random_oracle.Checked.pack_input
                        (array_to_input Random_oracle_input.Chunked.field
                           [| pi_hash; pis_hash; acc_hash |] ) ) ) ;

                let accBn =
                  Bn254.Circuit.create
                    (FrC.Circuit.to_FrA (G1Affine.Circuit.x acc))
                    (FrC.Circuit.to_FrA (G1Affine.Circuit.y acc))
                in
                let accBn =
                  Bn254.Circuit.add accBn (Bn254.Circuit.scale VK.ic4 pis.(3))
                in
                let accBn =
                  Bn254.Circuit.add accBn (Bn254.Circuit.scale VK.ic5 pis.(4))
                in

                FrC.Circuit.assert_equal
                  (FrA.Circuit.assertCanonical (Bn254.Circuit.x accBn))
                  (G1Affine.Circuit.x pi) ;
                FrC.Circuit.assert_equal
                  (FrA.Circuit.assertCanonical (Bn254.Circuit.y accBn))
                  (G1Affine.Circuit.y pi) ;

                { previous_proof_statements = []
                ; public_output = pis_hash
                ; auxiliary_output = ()
                } )
          ; feature_flags = Pickles_types.Plonk_types.Features.none_bool
          }
        ] )
      ()
end
