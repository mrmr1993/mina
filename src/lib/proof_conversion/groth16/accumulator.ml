(** Groth16 proof conversion accumulator types.

    The accumulator carries state between the 16 recursive circuits
    that together verify a Groth16 proof. Each circuit takes the
    accumulator as input (via Poseidon hash), processes a chunk of
    the verification, and outputs the updated accumulator.

    Reference: nori-proof-conversion/src/groth/recursion/data.ts *)

open! Core_kernel
module Step = Pickles.Impls.Step
module FF = Snarky_foreign_field.Foreign_field

(** RecursionProof: the proof data carried through all circuits.
    Matches nori's RecursionProof struct field order exactly. *)
module RecursionProof = struct
  module Circuit = struct
    type t =
      { neg_a : G1.Circuit.t
      ; b : G2.Circuit.t
      ; c : G1.Circuit.t
      ; pi : G1.Circuit.t
      ; c_fp12 : Fp12.Circuit.t
      ; c_inv : Fp12.Circuit.t
      ; shift_power : Step.Field.t
      }
  end

  module Constant = struct
    type t =
      { neg_a : G1.Constant.t
      ; b : G2.Constant.t
      ; c : G1.Constant.t
      ; pi : G1.Constant.t
      ; c_fp12 : Fp12.Constant.t
      ; c_inv : Fp12.Constant.t
      ; shift_power : int
      }
  end

  let typ : (Circuit.t, Constant.t) Step.Typ.t =
    Step.Typ.of_hlistable
      [ G1.Circuit.typ
      ; G2.Circuit.typ
      ; G1.Circuit.typ
      ; G1.Circuit.typ
      ; Fp12.Circuit.typ
      ; Fp12.Circuit.typ
      ; Step.Field.typ
      ]
      ~var_to_hlist:(fun (c : Circuit.t) ->
        [ c.neg_a; c.b; c.c; c.pi; c.c_fp12; c.c_inv; c.shift_power ] )
      ~var_of_hlist:(fun ([ neg_a; b; c; pi; c_fp12; c_inv; shift_power ] :
                           (unit, _) Snarky_backendless.H_list.t ) ->
        { neg_a; b; c; pi; c_fp12; c_inv; shift_power } )
      ~value_to_hlist:(fun (c : Constant.t) ->
        [ c.neg_a
        ; c.b
        ; c.c
        ; c.pi
        ; c.c_fp12
        ; c.c_inv
        ; Step.Field.Constant.of_int c.shift_power
        ] )
      ~value_of_hlist:(fun ([ neg_a; b; c; pi; c_fp12; c_inv; shift_power ] :
                             (unit, _) Snarky_backendless.H_list.t ) ->
        { neg_a
        ; b
        ; c
        ; pi
        ; c_fp12
        ; c_inv
        ; shift_power =
            Kimchi_pasta.Pasta.Fp.to_string shift_power |> Int.of_string
        } )
end

(** State: mutable pairing computation state.
    Matches nori's State struct field order exactly. *)
module State = struct
  module Circuit = struct
    type t =
      { t_point : G2.Circuit.t  (** Current G2 point T *)
      ; f : Fp12.Circuit.t  (** Miller loop accumulator *)
      ; g_digest : Step.Field.t  (** Poseidon hash of line evaluation array *)
      }
  end

  module Constant = struct
    type t =
      { t_point : G2.Constant.t
      ; f : Fp12.Constant.t
      ; g_digest : Step.Field.Constant.t
      }
  end

  let typ : (Circuit.t, Constant.t) Step.Typ.t =
    Step.Typ.of_hlistable
      [ G2.Circuit.typ; Fp12.Circuit.typ; Step.Field.typ ]
      ~var_to_hlist:(fun (c : Circuit.t) -> [ c.t_point; c.f; c.g_digest ])
      ~var_of_hlist:(fun ([ t_point; f; g_digest ] :
                           (unit, _) Snarky_backendless.H_list.t ) ->
        { t_point; f; g_digest } )
      ~value_to_hlist:(fun (c : Constant.t) -> [ c.t_point; c.f; c.g_digest ])
      ~value_of_hlist:(fun ([ t_point; f; g_digest ] :
                             (unit, _) Snarky_backendless.H_list.t ) ->
        { t_point; f; g_digest } )
end

(** The full Accumulator = RecursionProof + State.
    Matches nori's Accumulator struct field order exactly. *)
module Circuit = struct
  type t = { proof : RecursionProof.Circuit.t; state : State.Circuit.t }
end

module Constant = struct
  type t = { proof : RecursionProof.Constant.t; state : State.Constant.t }
end

let typ : (Circuit.t, Constant.t) Step.Typ.t =
  Step.Typ.of_hlistable
    [ RecursionProof.typ; State.typ ]
    ~var_to_hlist:(fun (c : Circuit.t) -> [ c.proof; c.state ])
    ~var_of_hlist:(fun ([ proof; state ] : (unit, _) Snarky_backendless.H_list.t)
                       -> { proof; state } )
    ~value_to_hlist:(fun (c : Constant.t) -> [ c.proof; c.state ])
    ~value_of_hlist:(fun ([ proof; state ] :
                           (unit, _) Snarky_backendless.H_list.t ) ->
      { proof; state } )

(** Collect all field elements from the accumulator in nori's packing order.
    This must exactly match the order that o1js's Provable.toFields produces
    for the Accumulator struct. *)
let to_fields (acc : Circuit.t) : Step.Field.t list =
  let field3 (x : FF.Field3.t) =
    let l0, l1, l2 = x in
    [ l0; l1; l2 ]
  in
  let fp2 (x : Fp2.Circuit.t) = field3 x.c0 @ field3 x.c1 in
  let g1 (x : G1.Circuit.t) = field3 x.x @ field3 x.y in
  let g2 (x : G2.Circuit.t) = fp2 x.x @ fp2 x.y in
  let fp6 (x : Fp6.Circuit.t) = fp2 x.c0 @ fp2 x.c1 @ fp2 x.c2 in
  let fp12 (x : Fp12.Circuit.t) = fp6 x.c0 @ fp6 x.c1 in
  let p = acc.proof in
  let s = acc.state in
  List.concat
    [ g1 p.neg_a
    ; g2 p.b
    ; g1 p.c
    ; g1 p.pi
    ; fp12 p.c_fp12
    ; fp12 p.c_inv
    ; [ p.shift_power ]
    ; g2 s.t_point
    ; fp12 s.f
    ; [ s.g_digest ]
    ]

(** Hash the accumulator using Poseidon, matching nori's
    Poseidon.hashPacked(Accumulator, acc). *)
let hash (acc : Circuit.t) : Step.Field.t =
  Accumulator_hash.poseidon_hash (Array.of_list (to_fields acc))
