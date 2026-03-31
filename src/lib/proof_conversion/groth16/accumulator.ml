(** Groth16 proof conversion accumulator types.

    The accumulator carries state between the 16 recursive circuits
    that together verify a Groth16 proof. Each circuit takes the
    accumulator as input (via Poseidon hash), processes a chunk of
    the verification, and outputs the updated accumulator.

    Reference: nori-proof-conversion/src/groth/recursion/data.ts *)

open! Core_kernel
module Step = Pickles.Impls.Step
module FF = Snarky_foreign_field.Foreign_field

(** Re-export Constant types so callers in files where local modules
    shadow G1/G2 can resolve record field labels. *)
module G1_constant = G1.Constant

module G2_constant = G2.Constant

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

(** Convert the accumulator to a Random_oracle Chunked input,
    matching o1js's Provable.toInput() for the Accumulator struct.

    ForeignField limbs (88 bits each) are packed entries, not full fields.
    This allows packToFields to combine two 88-bit limbs into one field,
    reducing the hash input size from ~152 to ~102 fields. *)
let to_input (acc : Circuit.t) : Step.Field.t Random_oracle_input.Chunked.t =
  let l = 88 in
  (* Each Field3 limb becomes a packed (field, 88) entry *)
  let field3_packed (x : FF.Field3.t) =
    let l0, l1, l2 = x in
    [| (l0, l); (l1, l); (l2, l) |]
  in
  let fp2_packed (x : Fp2.Circuit.t) =
    Array.concat [ field3_packed x.c0; field3_packed x.c1 ]
  in
  let g1_packed (x : G1.Circuit.t) =
    Array.concat [ field3_packed x.x; field3_packed x.y ]
  in
  let g2_packed (x : G2.Circuit.t) =
    Array.concat [ fp2_packed x.x; fp2_packed x.y ]
  in
  let fp6_packed (x : Fp6.Circuit.t) =
    Array.concat [ fp2_packed x.c0; fp2_packed x.c1; fp2_packed x.c2 ]
  in
  let fp12_packed (x : Fp12.Circuit.t) =
    Array.concat [ fp6_packed x.c0; fp6_packed x.c1 ]
  in
  let p = acc.proof in
  let s = acc.state in
  let packeds =
    Array.concat
      [ g1_packed p.neg_a
      ; g2_packed p.b
      ; g1_packed p.c
      ; g1_packed p.pi
      ; fp12_packed p.c_fp12
      ; fp12_packed p.c_inv
      ; [| (p.shift_power, Step.Field.size_in_bits) |]
      ; g2_packed s.t_point
      ; fp12_packed s.f
      ; [| (s.g_digest, Step.Field.size_in_bits) |]
      ]
  in
  { field_elements = [||]; packeds }

(** Hash the accumulator using Poseidon with packing, matching nori's
    Poseidon.hashPacked(Accumulator, acc).
    Uses Random_oracle.Checked.pack_input + hash. *)
let _acc_hash_marker (x : int) =
  let module S = Pickles.Impls.Step in
  S.assert_
    (Raw
       { kind = Zero
       ; values = [||]
       ; coeffs = Array.map ~f:S.Field.Constant.of_int [| x; 1; 2; 3; 4; 5; 6 |]
       } )

let hash (acc : Circuit.t) : Step.Field.t =
  _acc_hash_marker 6000 ;
  let input = to_input acc in
  let packed_fields = Random_oracle.Checked.pack_input input in
  _acc_hash_marker 6001 ;
  let result = Random_oracle.Checked.hash packed_fields in
  _acc_hash_marker 6002 ; result
