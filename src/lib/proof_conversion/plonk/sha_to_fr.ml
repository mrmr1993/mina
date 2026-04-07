(** Convert SHA-256 digest to BN254 scalar field element.

    Matches nori's shaToFr from plonk/fiat-shamir/sha_to_fr.ts.

    The 256-bit SHA digest is interpreted as a big-endian integer.
    Since BN254 Fr has ~254 bits, the top 2 bits are handled via
    conditional addition of 2^254 mod r and 2^255 mod r.

    Reference: nori-proof-conversion/src/plonk/fiat-shamir/sha_to_fr.ts *)

open! Core_kernel
module Step = Pickles.Impls.Step
module FF = Snarky_foreign_field.Foreign_field

(** 2^254 mod r (BN254 scalar field order). *)
let two_254_mod_r =
  Bignum_bigint.of_string
    "7059779437489773633646340506914701874769131765994106666166191815402473914367"

(** 2^255 mod r. *)
let two_255_mod_r =
  Bignum_bigint.of_string
    "14119558874979547267292681013829403749538263531988213332332383630804947828734"

(** Convert a SHA-256 digest (32 bytes) to a BN254 scalar (FrC).

    Matches nori's shaToFr line-for-line:
    1. Iterate bytes 31..0, calling toBits() (= choose_preimage 254) on each
    2. Collect 254 low bits, save bits 254 and 255
    3. Construct FrU.fromBits(shaBitRepr)
    4. Conditionally add 2^254 mod r and 2^255 mod r
    5. assertCanonical *)
let sha_to_fr (digest_bytes : Step.Field.t array) : FF.FpA.t =
  assert (Array.length digest_bytes = 32) ;
  (* let fields = hashDigest.toFields(); *)
  let fields = digest_bytes in

  let sha_bit_repr = Queue.create () in
  let bit_255 = ref Step.Boolean.false_ in
  let bit_256 = ref Step.Boolean.false_ in

  for i = 31 downto 0 do
    let length = Step.Field.size_in_bits - 1 in
    let bits_rev = List.init length ~f:(fun k ->
        let k' = length - 1 - k in
        Step.exists Step.Boolean.typ ~compute:(fun () ->
            let v = Step.As_prover.read_var fields.(i) in
            let bi = FF.field_const_to_bignum v in
            Bignum_bigint.(bit_and (shift_right bi k') one = one) ) ) in
    let bits = List.rev bits_rev in
    let lc = List.foldi bits ~init:Step.Field.zero ~f:(fun j acc bit ->
        let coeff = FF.bignum_to_field_const
          Bignum_bigint.(pow (of_int 2) (of_int j)) in
        Step.Field.add acc (Step.Field.scale (bit :> Step.Field.t) coeff) ) in
    let sealed = FF.seal lc in
    Step.Field.Assert.equal sealed fields.(i) ;
    let bits = Array.of_list bits in
    for j = 0 to 7 do
      (* we skip last 2 bits *)
      if i = 0 && j = 6 then
        bit_255 := bits.(j)
      else if i = 0 && j = 7 then
        bit_256 := bits.(j)
      else
        Queue.enqueue sha_bit_repr bits.(j)
    done
  done ;

  let sha_bit_repr = Queue.to_array sha_bit_repr in

  (* const sh254 = FrC.from(2^254 % r) *)
  (* const sh255 = FrC.from(2^255 % r) *)

  (* let x = FrU.fromBits(shaBitRepr) *)
  (* Pack 254 bits into 3 limbs of the Fr field:
     limb0 = bits[0..87], limb1 = bits[88..175], limb2 = bits[176..253] *)
  let pack_limb ~pos ~len =
    let terms =
      Array.to_list
        (Array.init len ~f:(fun j ->
             let bit = sha_bit_repr.(pos + j) in
             let coeff =
               FF.bignum_to_field_const Bignum_bigint.(pow (of_int 2) (of_int j))
             in
             Step.Field.scale (bit :> Step.Field.t) coeff ) )
    in
    List.fold terms ~init:Step.Field.zero ~f:Step.Field.add
  in
  let limb0 = pack_limb ~pos:0 ~len:88 in
  let limb1 = pack_limb ~pos:88 ~len:88 in
  let limb2 = pack_limb ~pos:176 ~len:78 in
  let x = FF.FpU.of_field3_unsafe (limb0, limb1, limb2) in

  (* const a = Provable.if(bit255.equals(true), FrC.provable, sh254, FrC.from(0n)) *)
  let cond_field3 (b : Step.Boolean.var) (c : Bignum_bigint.t) : FF.Field3.t =
    let l0, l1, l2 = FF.Field3.Constant.split c in
    let bf = (b :> Step.Field.t) in
    ( Step.Field.scale bf (FF.bignum_to_field_const l0)
    , Step.Field.scale bf (FF.bignum_to_field_const l1)
    , Step.Field.scale bf (FF.bignum_to_field_const l2) )
  in
  let a = cond_field3 !bit_255 two_254_mod_r in
  let b = cond_field3 !bit_256 two_255_mod_r in

  (* const res: FrC = x.add(a).add(b).assertCanonical() *)
  let x_f3 = FF.FpU.to_field3 x in
  let sum =
    FF.Sum.add
      (FF.Sum.add (FF.Sum.of_field3 x_f3) a)
      b
  in
  let result = FF.Sum.finish_simple sum ~f:Bn254_params.r in
  let result_checked =
    match FF.FpA.assert_almost_reduced
            [ FF.FpU.of_field3_unsafe result ] ~f:Bn254_params.r () with
    | [ a ] -> a
    | _ -> assert false
  in
  let canonical =
    FF.FpC.assert_canonical result_checked ~f:Bn254_params.r
  in
  FF.FpC.to_fpa canonical
