open Pickles.Impls.Step

module type Inputs = sig
  val switch_ : Boolean.var list -> ('a, _) Typ.t -> 'a list -> 'a

  val array_to_input :
       ('a -> Field.t Random_oracle_input.Chunked.t)
    -> 'a array
    -> Field.t Random_oracle_input.Chunked.t

  module FpU : sig
    type t

    val add : t -> t -> t

    val sub : t -> t -> t

    val mul : t -> t -> t

    val of_int : int -> t

    module Circuit : sig
      type t

      val sub : t -> t -> t
    end

    val typ : (Circuit.t, t) Typ.t
  end

  module FpA : sig
    type t = FpU.t

    module Circuit : sig
      type t = private FpU.Circuit.t

      val assert_equal : t -> t -> unit

      val assertAlmostReduced : FpU.Circuit.t -> FpU.Circuit.t -> t * t

      val neg : t -> t

      val add : t -> t -> FpU.Circuit.t

      val sub : t -> t -> FpU.Circuit.t

      val sum : t array -> int array -> FpU.Circuit.t

      val mul : t -> t -> FpU.Circuit.t

      val of_int : int -> t

      val to_input : t -> Field.t Random_oracle_input.Chunked.t
    end

    val typ : (Circuit.t, t) Typ.t
  end

  module FpC : sig
    type t = private FpA.t

    val inv : t -> FpA.t

    val assertCanonical : FpA.t -> t

    module Circuit : sig
      type t = private FpA.Circuit.t

      val assert_equal : t -> t -> unit

      val neg : t -> FpA.Circuit.t

      val mul : t -> t -> FpA.Circuit.t

      val inv : t -> FpA.Circuit.t

      val assertCanonical : FpA.Circuit.t -> t

      val of_int : int -> t

      val to_input : t -> Field.t Random_oracle_input.Chunked.t
    end

    val typ : (Circuit.t, t) Typ.t
  end

  module Bn254 : sig
    type t

    module Circuit : sig
      type t

      val create : FpA.Circuit.t -> FpA.Circuit.t -> t

      val x : t -> FpA.Circuit.t

      val y : t -> FpA.Circuit.t

      val add : t -> t -> t

      val scale : t -> FpC.Circuit.t -> t
    end

    val typ : (Circuit.t, t) Typ.t
  end

  module UnreducedSum : sig
    module Circuit : sig
      type t

      val create : FpU.Circuit.t -> t

      val add : t -> FpU.Circuit.t -> t
    end
  end

  module AlmostReducedSum : sig
    module Circuit : sig
      type t

      val create : FpA.Circuit.t -> t

      val add : t -> FpA.Circuit.t -> t

      val sub : t -> FpA.Circuit.t -> t
    end
  end

  val assertMul :
       [ `Sum of AlmostReducedSum.Circuit.t | `Field of FpA.Circuit.t ]
    -> [ `Sum of AlmostReducedSum.Circuit.t | `Field of FpA.Circuit.t ]
    -> [ `Sum of UnreducedSum.Circuit.t | `Field of FpU.Circuit.t ]
    -> unit

  module Fp2 : sig
    type t

    module Circuit : sig
      type t

      val create : FpA.Circuit.t -> FpA.Circuit.t -> t

      val zero : unit -> t

      val one : unit -> t

      val add : t -> t -> t

      val sub : t -> t -> t

      val neg : t -> t

      val mul : t -> t -> t

      val square : t -> t

      val mul_by_fp : t -> FpA.Circuit.t -> t

      val conjugate : t -> t

      val sum : t array -> int array -> t

      val assert_equals : t -> t -> unit

      val to_input : t -> Field.t Random_oracle_input.Chunked.t
    end

    val typ : (Circuit.t, t) Typ.t
  end

  val fp2_non_residue : Fp2.Circuit.t

  module Fp6 : sig
    module Circuit : sig
      type t = { c0 : Fp2.Circuit.t; c1 : Fp2.Circuit.t; c2 : Fp2.Circuit.t }
    end
  end

  val gamma_1s : Fp2.Circuit.t array

  val gamma_2s : Fp2.Circuit.t array

  val gamma_3s : Fp2.Circuit.t array

  module Fp12 : sig
    module Circuit : sig
      type t = { c0 : Fp6.Circuit.t; c1 : Fp6.Circuit.t }
    end
  end

  module G1Affine : sig
    type t

    module Circuit : sig
      type t

      val create : FpC.Circuit.t -> FpC.Circuit.t -> t

      val x : t -> FpC.Circuit.t

      val y : t -> FpC.Circuit.t

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
        val negA : t -> G1Affine.Circuit.t

        val b : t -> G2Affine.Circuit.t

        val c : t -> G1Affine.Circuit.t

        val pi : t -> G1Affine.Circuit.t

        val c_fp : t -> Fp12.Circuit.t

        val c_fp_inv : t -> Fp12.Circuit.t

        val shift_power : t -> Field.t
      end

      val to_input : t -> Field.t Random_oracle_input.Chunked.t
    end

    val typ : (Circuit.t, t) Typ.t
  end

  val ate_loop_count : int array

  module AffineCache : sig
    module Circuit : sig
      type t =
        { xp_neg : FpC.Circuit.t
        ; yp_prime : FpC.Circuit.t
        ; xp_prime : FpC.Circuit.t
        }
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

module Make_Fp2 (Inputs : Inputs) = struct
  open Inputs

  type t = { c0 : FpA.t; c1 : FpA.t }

  module Circuit = struct
    type t = { c0 : FpA.Circuit.t; c1 : FpA.Circuit.t }

    let create c0 c1 = { c0; c1 }

    let zero () = { c0 = FpA.Circuit.of_int 0; c1 = FpA.Circuit.of_int 0 }

    let one () = { c0 = FpA.Circuit.of_int 1; c1 = FpA.Circuit.of_int 0 }

    let assert_equals self rhs =
      FpA.Circuit.assert_equal self.c0 rhs.c0 ;
      FpA.Circuit.assert_equal self.c1 rhs.c1

    let fromUnreduced c0 c1 =
      let c0A, c0B = FpA.Circuit.assertAlmostReduced c0 c1 in
      { c0 = c0A; c1 = c0B }

    let neg self =
      { c0 = FpA.Circuit.neg self.c0; c1 = FpA.Circuit.neg self.c1 }

    let conjugate self = { c0 = self.c0; c1 = FpA.Circuit.neg self.c1 }

    let add self rhs =
      let c0 = FpA.Circuit.add self.c0 rhs.c0 in
      let c1 = FpA.Circuit.add self.c1 rhs.c1 in

      fromUnreduced c0 c1

    let sub self rhs =
      let c0 = FpA.Circuit.sub self.c0 rhs.c0 in
      let c1 = FpA.Circuit.sub self.c1 rhs.c1 in

      fromUnreduced c0 c1

    let sum inputs operators =
      let c0 =
        FpA.Circuit.sum (Array.map (fun { c0; _ } -> c0) inputs) operators
      in
      let c1 =
        FpA.Circuit.sum (Array.map (fun { c1; _ } -> c1) inputs) operators
      in

      fromUnreduced c0 c1

    let mul_by_fp self rhs =
      let c0 = FpA.Circuit.mul self.c0 rhs in
      let c1 = FpA.Circuit.mul self.c1 rhs in

      fromUnreduced c0 c1

    let mul self rhs =
      let a0b0 = FpA.Circuit.mul self.c0 rhs.c0 in
      let a1b1 = FpA.Circuit.mul self.c1 rhs.c1 in
      let c0 = FpU.Circuit.sub a0b0 a1b1 in

      let c1 =
        exists FpU.typ ~compute:(fun () ->
            let a0 = As_prover.read FpA.typ self.c0 in
            let a1 = As_prover.read FpA.typ self.c1 in
            let b0 = As_prover.read FpA.typ rhs.c0 in
            let b1 = As_prover.read FpA.typ rhs.c1 in
            FpU.add (FpU.mul a0 b1) (FpU.mul a1 b0) )
      in

      let sum_a0_a1 =
        AlmostReducedSum.Circuit.add
          (AlmostReducedSum.Circuit.create self.c0)
          self.c1
      in
      let sum_b0_b1 =
        AlmostReducedSum.Circuit.add
          (AlmostReducedSum.Circuit.create rhs.c0)
          rhs.c1
      in
      let sum_c1_a0b0_a1b1 =
        UnreducedSum.Circuit.add
          (UnreducedSum.Circuit.add
             (UnreducedSum.Circuit.create c1)
             (a0b0 :> FpU.Circuit.t) )
          (a1b1 :> FpU.Circuit.t)
      in
      assertMul (`Sum sum_a0_a1) (`Sum sum_b0_b1) (`Sum sum_c1_a0b0_a1b1) ;

      fromUnreduced c0 c1

    let square self =
      let c0, c1 =
        exists (Typ.tuple2 FpU.typ FpU.typ) ~compute:(fun () ->
            let a0 = As_prover.read FpA.typ self.c0 in
            let a1 = As_prover.read FpA.typ self.c1 in
            ( FpU.sub (FpU.mul a0 a0) (FpU.mul a1 a1)
            , FpU.mul (FpU.mul (FpU.of_int 2) a0) a1 ) )
      in

      let sum_a0_a1 =
        AlmostReducedSum.Circuit.add
          (AlmostReducedSum.Circuit.create self.c0)
          self.c1
      in
      let diff_a0_a1 =
        AlmostReducedSum.Circuit.sub
          (AlmostReducedSum.Circuit.create self.c0)
          self.c1
      in
      assertMul (`Sum sum_a0_a1) (`Sum diff_a0_a1) (`Field c0) ;

      let sum_a0_a0 =
        AlmostReducedSum.Circuit.add
          (AlmostReducedSum.Circuit.create self.c0)
          self.c0
      in
      assertMul (`Sum sum_a0_a0) (`Field self.c1) (`Field c1) ;

      fromUnreduced c0 c1

    let to_input { c0; c1 } =
      Random_oracle_input.Chunked.append (FpA.Circuit.to_input c0)
        (FpA.Circuit.to_input c1)
  end

  let typ =
    Typ.of_hlistable [ FpA.typ; FpA.typ ]
      ~var_to_hlist:(fun ({ c0; c1 } : Circuit.t) -> [ c0; c1 ])
      ~var_of_hlist:(fun [ c0; c1 ] -> { c0; c1 })
      ~value_to_hlist:(fun ({ c0; c1 } : t) -> [ c0; c1 ])
      ~value_of_hlist:(fun [ c0; c1 ] -> { c0; c1 })
end

module Make_Fp6 (Inputs : Inputs) = struct
  open Inputs

  type t = { c0 : Fp2.t; c1 : Fp2.t; c2 : Fp2.t }

  module Circuit = struct
    type t = Fp6.Circuit.t =
      { c0 : Fp2.Circuit.t; c1 : Fp2.Circuit.t; c2 : Fp2.Circuit.t }

    let create c0 c1 c2 = { c0; c1; c2 }

    let zero () =
      { c0 = Fp2.Circuit.zero ()
      ; c1 = Fp2.Circuit.zero ()
      ; c2 = Fp2.Circuit.zero ()
      }

    let one () =
      { c0 = Fp2.Circuit.one ()
      ; c1 = Fp2.Circuit.zero ()
      ; c2 = Fp2.Circuit.zero ()
      }

    let assert_equal self rhs =
      Fp2.Circuit.assert_equals self.c0 rhs.c0 ;
      Fp2.Circuit.assert_equals self.c1 rhs.c1 ;
      Fp2.Circuit.assert_equals self.c2 rhs.c2

    let add self rhs =
      let c0 = Fp2.Circuit.add self.c0 rhs.c0 in
      let c1 = Fp2.Circuit.add self.c1 rhs.c1 in
      let c2 = Fp2.Circuit.add self.c2 rhs.c2 in

      { c0; c1; c2 }

    let sub self rhs =
      let c0 = Fp2.Circuit.sub self.c0 rhs.c0 in
      let c1 = Fp2.Circuit.sub self.c1 rhs.c1 in
      let c2 = Fp2.Circuit.sub self.c2 rhs.c2 in

      { c0; c1; c2 }

    let mul_by_v self =
      let c0 = Fp2.Circuit.mul self.c0 fp2_non_residue in
      { c0; c1 = self.c0; c2 = self.c1 }

    let mul_by_fp self rhs =
      let c0 = Fp2.Circuit.mul_by_fp self.c0 rhs in
      let c1 = Fp2.Circuit.mul_by_fp self.c1 rhs in
      let c2 = Fp2.Circuit.mul_by_fp self.c2 rhs in

      { c0; c1; c2 }

    let mul self rhs =
      let t0 = Fp2.Circuit.mul self.c0 rhs.c0 in
      let t1 = Fp2.Circuit.mul self.c1 rhs.c1 in
      let t2 = Fp2.Circuit.mul self.c2 rhs.c2 in

      let a1_a2 = Fp2.Circuit.add self.c1 self.c2 in
      let a0_a1 = Fp2.Circuit.add self.c0 self.c1 in
      let a0_a2 = Fp2.Circuit.add self.c0 self.c2 in

      let b1_b2 = Fp2.Circuit.add rhs.c1 rhs.c2 in
      let b0_b1 = Fp2.Circuit.add rhs.c0 rhs.c1 in
      let b0_b2 = Fp2.Circuit.add rhs.c0 rhs.c2 in

      let c0 =
        let c0 =
          Fp2.Circuit.sum [| Fp2.Circuit.mul a1_a2 b1_b2; t1; t2 |] [| -1; 1 |]
        in
        let c0 = Fp2.Circuit.mul c0 fp2_non_residue in
        Fp2.Circuit.add c0 t0
      in
      let c1 =
        Fp2.Circuit.sum
          [| Fp2.Circuit.mul a0_a1 b0_b1
           ; t0
           ; t1
           ; Fp2.Circuit.mul t2 fp2_non_residue
          |]
          [| -1; -1; 1 |]
      in
      let c2 =
        Fp2.Circuit.sum
          [| Fp2.Circuit.mul a0_a2 b0_b2; t0; t2; t1 |]
          [| -1; -1; 1 |]
      in

      { c0; c1; c2 }

    let mul_by_fp2 self rhs =
      let c0 = Fp2.Circuit.mul self.c0 rhs in
      let c1 = Fp2.Circuit.mul self.c1 rhs in
      let c2 = Fp2.Circuit.mul self.c2 rhs in

      { c0; c1; c2 }

    let mul_by_sparse_fp6 self rhs =
      let t0 = Fp2.Circuit.mul self.c0 rhs.c0 in
      let t1 = Fp2.Circuit.mul self.c1 rhs.c1 in

      let c0 =
        Fp2.Circuit.mul (Fp2.Circuit.mul self.c2 rhs.c1) fp2_non_residue
      in
      let c0 = Fp2.Circuit.add c0 t0 in

      let a0_a1 = Fp2.Circuit.add self.c0 self.c1 in
      let b0_b1 = Fp2.Circuit.add rhs.c0 rhs.c1 in
      let c1 = Fp2.Circuit.mul a0_a1 b0_b1 in
      let c1 = Fp2.Circuit.sub (Fp2.Circuit.sub c1 t0) t1 in

      let c2 = Fp2.Circuit.add (Fp2.Circuit.mul self.c2 rhs.c0) t1 in

      { c0; c1; c2 }

    let to_input { c0; c1; c2 } =
      Random_oracle_input.Chunked.append
        (Random_oracle_input.Chunked.append (Fp2.Circuit.to_input c0)
           (Fp2.Circuit.to_input c1) )
        (Fp2.Circuit.to_input c2)
  end

  let typ =
    Typ.of_hlistable
      [ Fp2.typ; Fp2.typ; Fp2.typ ]
      ~var_to_hlist:(fun ({ c0; c1; c2 } : Circuit.t) -> [ c0; c1; c2 ])
      ~var_of_hlist:(fun [ c0; c1; c2 ] -> { c0; c1; c2 })
      ~value_to_hlist:(fun ({ c0; c1; c2 } : t) -> [ c0; c1; c2 ])
      ~value_of_hlist:(fun [ c0; c1; c2 ] -> { c0; c1; c2 })
end

module Make_Fp12 (Inputs : Inputs) = struct
  open Inputs
  module Fp6 = Make_Fp6 (Inputs)

  type t = { c0 : Fp6.t; c1 : Fp6.t }

  module Circuit = struct
    type t = Fp12.Circuit.t = { c0 : Fp6.Circuit.t; c1 : Fp6.Circuit.t }

    let create c0 c1 = { c0; c1 }

    let one () = create (Fp6.Circuit.one ()) (Fp6.Circuit.zero ())

    let assert_equal self rhs =
      Fp6.Circuit.assert_equal self.c0 rhs.c0 ;
      Fp6.Circuit.assert_equal self.c1 rhs.c1

    let mul self rhs =
      let t0 = Fp6.Circuit.mul self.c0 rhs.c0 in
      let t1 = Fp6.Circuit.mul self.c1 rhs.c1 in

      let c0 = Fp6.Circuit.add (Fp6.Circuit.mul_by_v t1) t0 in

      let a0_a1 = Fp6.Circuit.add self.c0 self.c1 in
      let b0_b1 = Fp6.Circuit.add rhs.c0 rhs.c1 in

      let c1 =
        Fp6.Circuit.sub (Fp6.Circuit.sub (Fp6.Circuit.mul a0_a1 b0_b1) t0) t1
      in

      create c0 c1

    let sparse_mul self rhs =
      let t0 = Fp6.Circuit.mul_by_fp2 self.c0 rhs.c0.c0 in
      let t1 = Fp6.Circuit.mul_by_sparse_fp6 self.c1 rhs.c1 in

      let c0 = Fp6.Circuit.add t0 (Fp6.Circuit.mul_by_v t1) in

      let t2 : Fp6.Circuit.t =
        { c0 = Fp2.Circuit.add rhs.c0.c0 rhs.c1.c0
        ; c1 = rhs.c1.c1
        ; c2 = Fp2.Circuit.zero ()
        }
      in

      let c1 =
        Fp6.Circuit.mul_by_sparse_fp6 (Fp6.Circuit.add self.c0 self.c1) t2
      in
      let c1 = Fp6.Circuit.sub (Fp6.Circuit.sub c1 t0) t1 in
      { c0; c1 }

    let square self =
      let c0 = Fp6.Circuit.sub self.c0 self.c1 in
      let c3 = Fp6.Circuit.sub self.c0 (Fp6.Circuit.mul_by_v self.c1) in
      let c2 = Fp6.Circuit.mul self.c0 self.c1 in

      let c0 = Fp6.Circuit.add (Fp6.Circuit.mul c0 c3) c2 in
      let c1 = Fp6.Circuit.mul_by_fp c2 (FpA.Circuit.of_int 2) in

      let c2 = Fp6.Circuit.mul_by_v c2 in
      let c0 = Fp6.Circuit.add c0 c2 in

      { c0; c1 }

    let frobenius_pow_p self =
      let t1 = Fp2.Circuit.conjugate self.c0.c0 in
      let t2 = Fp2.Circuit.conjugate self.c1.c0 in
      let t3 = Fp2.Circuit.conjugate self.c0.c1 in
      let t4 = Fp2.Circuit.conjugate self.c1.c1 in
      let t5 = Fp2.Circuit.conjugate self.c0.c2 in
      let t6 = Fp2.Circuit.conjugate self.c1.c2 in

      let t2 = Fp2.Circuit.mul t2 gamma_1s.(0) in
      let t3 = Fp2.Circuit.mul t3 gamma_1s.(1) in
      let t4 = Fp2.Circuit.mul t4 gamma_1s.(2) in
      let t5 = Fp2.Circuit.mul t5 gamma_1s.(3) in
      let t6 = Fp2.Circuit.mul t6 gamma_1s.(4) in

      let c0 : Fp6.Circuit.t = { c0 = t1; c1 = t3; c2 = t5 } in
      let c1 : Fp6.Circuit.t = { c0 = t2; c1 = t4; c2 = t6 } in

      { c0; c1 }

    let frobenius_pow_p_squared self =
      let t1 = self.c0.c0 in
      let t2 = Fp2.Circuit.mul self.c1.c0 gamma_2s.(0) in
      let t3 = Fp2.Circuit.mul self.c0.c1 gamma_2s.(1) in
      let t4 = Fp2.Circuit.mul self.c1.c1 gamma_2s.(2) in
      let t5 = Fp2.Circuit.mul self.c0.c2 gamma_2s.(3) in
      let t6 = Fp2.Circuit.mul self.c1.c2 gamma_2s.(4) in

      let c0 : Fp6.Circuit.t = { c0 = t1; c1 = t3; c2 = t5 } in
      let c1 : Fp6.Circuit.t = { c0 = t2; c1 = t4; c2 = t6 } in

      { c0; c1 }

    let frobenius_pow_p_cubed self =
      let t1 = Fp2.Circuit.conjugate self.c0.c0 in
      let t2 = Fp2.Circuit.conjugate self.c1.c0 in
      let t3 = Fp2.Circuit.conjugate self.c0.c1 in
      let t4 = Fp2.Circuit.conjugate self.c1.c1 in
      let t5 = Fp2.Circuit.conjugate self.c0.c2 in
      let t6 = Fp2.Circuit.conjugate self.c1.c2 in

      let t2 = Fp2.Circuit.mul t2 gamma_3s.(0) in
      let t3 = Fp2.Circuit.mul t3 gamma_3s.(1) in
      let t4 = Fp2.Circuit.mul t4 gamma_3s.(2) in
      let t5 = Fp2.Circuit.mul t5 gamma_3s.(3) in
      let t6 = Fp2.Circuit.mul t6 gamma_3s.(4) in

      let c0 : Fp6.Circuit.t = { c0 = t1; c1 = t3; c2 = t5 } in
      let c1 : Fp6.Circuit.t = { c0 = t2; c1 = t4; c2 = t6 } in

      { c0; c1 }

    let to_input { c0; c1 } =
      Random_oracle_input.Chunked.append (Fp6.Circuit.to_input c0)
        (Fp6.Circuit.to_input c1)
  end

  let typ =
    Typ.of_hlistable [ Fp6.typ; Fp6.typ ]
      ~var_to_hlist:(fun ({ c0; c1 } : Circuit.t) -> [ c0; c1 ])
      ~var_of_hlist:(fun [ c0; c1 ] -> { c0; c1 })
      ~value_to_hlist:(fun ({ c0; c1 } : t) -> [ c0; c1 ])
      ~value_of_hlist:(fun [ c0; c1 ] -> { c0; c1 })
end

module ArrayListHasher (Inputs : Inputs) = struct
  open Inputs
  module Fp12 = Make_Fp12 (Inputs)

  let n = Array.length ate_loop_count

  module Circuit = struct
    let hash arr =
      Random_oracle.Checked.hash
        (Random_oracle.Checked.pack_input
           (array_to_input Random_oracle_input.Chunked.field arr) )

    let open_ lhs opening rhs =
      let opening_hashes =
        Array.map
          (fun x ->
            Random_oracle.Checked.hash
              (Random_oracle.Checked.pack_input (Fp12.Circuit.to_input x)) )
          opening
      in
      let arr = Array.concat [ lhs; opening_hashes; rhs ] in

      Random_oracle.Checked.hash
        (Random_oracle.Checked.pack_input
           (array_to_input Random_oracle_input.Chunked.field arr) )
  end
end

module Make_AffineCache (Inputs : Inputs) = struct
  open Inputs

  module Circuit = struct
    type t = AffineCache.Circuit.t =
      { xp_neg : FpC.Circuit.t
      ; yp_prime : FpC.Circuit.t
      ; xp_prime : FpC.Circuit.t
      }

    let create (p : G1Affine.Circuit.t) =
      let xp_neg =
        FpC.Circuit.assertCanonical (FpC.Circuit.neg (G1Affine.Circuit.x p))
      in
      (* This is immediately erased.. *)
      let _yp_prime =
        FpC.Circuit.assertCanonical (FpC.Circuit.inv (G1Affine.Circuit.y p))
      in
      (* ..and this isn't canonical. High-quality stuff. *)
      let yp_prime =
        exists FpC.typ ~compute:(fun () ->
            let y = As_prover.read FpC.typ (G1Affine.Circuit.y p) in
            FpC.inv y |> FpC.assertCanonical )
      in
      FpC.Circuit.mul yp_prime (G1Affine.Circuit.y p)
      |> FpA.Circuit.assert_equal (FpA.Circuit.of_int 1) ;
      let xp_prime =
        FpC.Circuit.assertCanonical (FpC.Circuit.mul xp_neg yp_prime)
      in
      { xp_neg; yp_prime; xp_prime }

    let xp_prime { xp_prime; _ } = xp_prime

    let yp_prime { yp_prime; _ } = yp_prime
  end
end

module Make_G2Line (Inputs : Inputs) = struct
  open Inputs
  module AffineCache = Make_AffineCache (Inputs)
  module Fp12 = Make_Fp12 (Inputs)
  module Fp6 = Fp12.Fp6

  type t = { lambda : Fp2.t; neg_mu : Fp2.t }

  module Circuit = struct
    type t = G2Line.Circuit.t =
      { lambda : Fp2.Circuit.t; neg_mu : Fp2.Circuit.t }

    let psi self (cache : AffineCache.Circuit.t) =
      let g0 =
        Fp2.Circuit.create (FpA.Circuit.of_int 1) (FpA.Circuit.of_int 0)
      in
      let h0 =
        Fp2.Circuit.mul_by_fp self.lambda
          (AffineCache.Circuit.xp_prime cache :> FpA.Circuit.t)
      in
      let g1 = Fp2.Circuit.zero () in
      let h1 =
        Fp2.Circuit.mul_by_fp self.neg_mu
          (AffineCache.Circuit.yp_prime cache :> FpA.Circuit.t)
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
        (Fp2.Circuit.mul_by_fp x_square (FpA.Circuit.of_int 3))

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
  module AffineCache = G2Line.AffineCache
  module Fp12 = G2Line.Fp12
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
  module ArrayListHasher = ArrayListHasher (Inputs)

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
  module ArrayListHasher = ArrayListHasher (Inputs)

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
                     (Accumulator.Circuit.Proof.c_fp_inv !acc)
                     (Accumulator.Circuit.Proof.c_fp !acc) )
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
  module Fp12 = Make_Fp12 (Inputs)

  let update_f acc g_chunk =
    let f = ref (Accumulator.Circuit.f !acc) in

    let idx = ref 0 in

    for i = 1 + prefix to prefix + iterations do
      f := Fp12.Circuit.mul (Fp12.Circuit.square !f) g_chunk.(!idx) ;
      if ate_loop_count.(i) = 1 then
        f := Fp12.Circuit.mul !f (Accumulator.Circuit.Proof.c_fp_inv !acc)
      else if ate_loop_count.(i) = -1 then
        f := Fp12.Circuit.mul !f (Accumulator.Circuit.Proof.c_fp !acc)
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
  module ArrayListHasher = ArrayListHasher (Inputs)
  module Fp12 = ArrayListHasher.Fp12

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
  module ArrayListHasher = ArrayListHasher (Inputs)
  module Fp12 = ArrayListHasher.Fp12

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
                             (Accumulator.Circuit.Proof.c_fp_inv !acc) ) )
                   |> (fun x ->
                        Fp12.Circuit.mul x
                          (Fp12.Circuit.frobenius_pow_p_squared
                             (Accumulator.Circuit.Proof.c_fp !acc) ) )
                   |> (fun x ->
                        Fp12.Circuit.mul x
                          (Fp12.Circuit.frobenius_pow_p_cubed
                             (Accumulator.Circuit.Proof.c_fp_inv !acc) ) )
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

  let auxiliary_input_typ = Typ.array ~length:5 FpC.typ

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
                       (array_to_input FpC.Circuit.to_input pis) )
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
                    (FpC.Circuit.assertCanonical (Bn254.Circuit.x acc))
                    (FpC.Circuit.assertCanonical (Bn254.Circuit.y acc))
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
    Typ.tuple3 G1Affine.typ G1Affine.typ (Typ.array ~length:5 FpC.typ)

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
                       (array_to_input FpC.Circuit.to_input pis) )
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
                    (G1Affine.Circuit.x acc :> FpA.Circuit.t)
                    (G1Affine.Circuit.y acc :> FpA.Circuit.t)
                in
                let accBn =
                  Bn254.Circuit.add accBn (Bn254.Circuit.scale VK.ic4 pis.(3))
                in
                let accBn =
                  Bn254.Circuit.add accBn (Bn254.Circuit.scale VK.ic5 pis.(4))
                in

                FpC.Circuit.assert_equal
                  (FpC.Circuit.assertCanonical (Bn254.Circuit.x accBn))
                  (G1Affine.Circuit.x pi) ;
                FpC.Circuit.assert_equal
                  (FpC.Circuit.assertCanonical (Bn254.Circuit.y accBn))
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
