(** SHA-256 hash function using constrained circuit operations.

    Matches the o1js SHA-256 gadget (sha2.ts) gate-for-gate:
    - sigma: fused decompose + reassemble + XOR (not individual ROTR)
    - Ch: AND + unchecked NOT + AND + field add + seal
    - Maj: field add + seal + double XOR + field sub + div(2) + seal
    - reduceMod: divMod32(x, 48) for modular reduction
    - messageSchedule: DeltaOne + DeltaZero + field adds + reduceMod
    - compression: 64 rounds of the above

    Reference: o1js/src/lib/provable/gadgets/sha2.ts *)

open! Core_kernel
module Step = Pickles.Impls.Step
module FF = Snarky_foreign_field.Foreign_field

(** SHA-256 initial hash values §5.3.3. *)
let h_init =
  [| 0x6a09e667; 0xbb67ae85; 0x3c6ef372; 0xa54ff53a
   ; 0x510e527f; 0x9b05688c; 0x1f83d9ab; 0x5be0cd19
  |]

(** SHA-256 round constants §4.2.2. *)
let k_constants =
  [| 0x428a2f98; 0x71374491; 0xb5c0fbcf; 0xe9b5dba5
   ; 0x3956c25b; 0x59f111f1; 0x923f82a4; 0xab1c5ed5
   ; 0xd807aa98; 0x12835b01; 0x243185be; 0x550c7dc3
   ; 0x72be5d74; 0x80deb1fe; 0x9bdc06a7; 0xc19bf174
   ; 0xe49b69c1; 0xefbe4786; 0x0fc19dc6; 0x240ca1cc
   ; 0x2de92c6f; 0x4a7484aa; 0x5cb0a9dc; 0x76f988da
   ; 0x983e5152; 0xa831c66d; 0xb00327c8; 0xbf597fc7
   ; 0xc6e00bf3; 0xd5a79147; 0x06ca6351; 0x14292967
   ; 0x27b70a85; 0x2e1b2138; 0x4d2c6dfc; 0x53380d13
   ; 0x650a7354; 0x766a0abb; 0x81c2c92e; 0x92722c85
   ; 0xa2bfe8a1; 0xa81a664b; 0xc24b8b70; 0xc76c51a3
   ; 0xd192e819; 0xd6990624; 0xf40e3585; 0x106aa070
   ; 0x19a4c116; 0x1e376c08; 0x2748774c; 0x34b0bcb5
   ; 0x391c0cb3; 0x4ed8aa4a; 0x5b9cca4f; 0x682e6ff3
   ; 0x748f82ee; 0x78a5636f; 0x84c87814; 0x8cc70208
   ; 0x90befffa; 0xa4506ceb; 0xbef9a3f7; 0xc67178f2
  |]

(** Sigma rotation constants for SHA-256.
    SIGMA_ZERO = [2, 13, 22], SIGMA_ONE = [6, 11, 25]
    DELTA_ZERO = [3, 7, 18],  DELTA_ONE = [10, 17, 19] *)
let sigma_zero_bits = (2, 13, 22)
let sigma_one_bits = (6, 11, 25)
let delta_zero_bits = (3, 7, 18)
let delta_one_bits = (10, 17, 19)

(** Reduce a field element modulo 2^32.
    Matches o1js reduceMod: divMod32(x, 48).remainder.
    The nBits=48 accounts for up to 5 additions of 32-bit values. *)
let reduce_mod (x : Step.Field.t) : Uint32.t =
  let _q, r = Uint32.div_mod_32 x ~n_bits:48 in
  r

(** Seal a field expression — materialize compound Cvars into a
    fresh variable. Matches o1js Field.seal(). *)
let seal (x : Step.Field.t) : Step.Field.t =
  FF.seal x

(** Fused sigma function: decompose, reassemble 3 rotations, XOR.
    Matches o1js sigma() for UInt32 (sha2.ts lines 514-586).

    [bits] = (r0, r1, r2) are the rotation amounts.
    [first_shifted] = true for DeltaZero/DeltaOne (first op is SHR, not ROTR). *)
let sigma (u : Uint32.t) ~(bits : int * int * int)
    ~(first_shifted : bool) : Uint32.t =
  let r0, r1, r2 = bits in
  let x = Uint32.to_field u in
  let d0 = r0 in
  let d1 = r1 - r0 in
  let d2 = r2 - r1 in
  let d3 = 32 - r2 in
  (* Decompose x into 4 chunks of size d0, d1, d2, d3.
     Witness all 4 upfront in a single Array.init for sequential indices. *)
  let chunks =
    Array.init 4 ~f:(fun idx ->
      Step.exists Step.Field.typ ~compute:(fun () ->
          let xv = Step.As_prover.read_var x in
          let x_big =
            Bignum_bigint.of_string (Step.Field.Constant.to_string xv)
          in
          let bit_slice offset len =
            let open Bignum_bigint in
            bit_and (shift_right x_big offset)
              (pow (of_int 2) (of_int len) - one)
          in
          let v =
            match idx with
            | 0 -> bit_slice 0 d0
            | 1 -> bit_slice r0 d1
            | 2 -> bit_slice r1 d2
            | 3 -> bit_slice r2 d3
            | _ -> assert false
          in
          Step.Field.Constant.of_string (Bignum_bigint.to_string v) ) )
  in
  let x0 = chunks.(0) in
  let x1 = chunks.(1) in
  let x2 = chunks.(2) in
  let x3 = chunks.(3) in
  (* Range check each chunk to 16 bits *)
  Uint32.range_check_16 x0 ;
  Uint32.range_check_16 x1 ;
  Uint32.range_check_16 x2 ;
  Uint32.range_check_16 x3 ;
  (* Prove decomposition:
     x = x0 + x1*2^d0 + x2*2^(d0+d1) + x3*2^(d0+d1+d2) *)
  let s n = Step.Field.of_int (1 lsl n) in
  let x23 = seal (Step.Field.add x2 (Step.Field.mul x3 (s d2))) in
  let x123 = seal (Step.Field.add x1 (Step.Field.mul x23 (s d1))) in
  Step.Field.Assert.equal
    (Step.Field.add x0 (Step.Field.mul x123 (s d0)))
    x ;
  (* Reassemble rotated values *)
  let x_rot_r0 =
    if not first_shifted then
      (* rotr(x, r0) = x123 + x0*2^(d1+d2+d3) *)
      seal (Step.Field.add x123 (Step.Field.mul x0 (s (d1 + d2 + d3))))
    else begin
      (* shr(x, r0) = x123 *)
      Uint32.range_check_16
        (seal (Step.Field.mul x0 (s (16 - d0)))) ;
      x123
    end
  in
  (* rotr(x, r1) = x23 + x01*2^(d2+d3) *)
  let x01 = seal (Step.Field.add x0 (Step.Field.mul x1 (s d0))) in
  let x_rot_r1 = seal (Step.Field.add x23 (Step.Field.mul x01 (s (d2 + d3)))) in
  (* rotr(x, r2) = x3 + x012*2^d3 *)
  let x012 = seal (Step.Field.add x01 (Step.Field.mul x2 (s (d0 + d1)))) in
  let x_rot_r2 = seal (Step.Field.add x3 (Step.Field.mul x012 (s d3))) in
  (* XOR the three rotated values: xor(xor(rot0, rot1), rot2) *)
  Uint32.xor (Uint32.xor x_rot_r0 x_rot_r1) x_rot_r2

(** SigmaZero(x) = sigma(x, [2, 13, 22], false) *)
let sigma_zero (x : Uint32.t) : Uint32.t =
  sigma x ~bits:sigma_zero_bits ~first_shifted:false

(** SigmaOne(x) = sigma(x, [6, 11, 25], false) *)
let sigma_one (x : Uint32.t) : Uint32.t =
  sigma x ~bits:sigma_one_bits ~first_shifted:false

(** DeltaZero(x) = sigma(x, [3, 7, 18], true) — first op is SHR *)
let delta_zero (x : Uint32.t) : Uint32.t =
  sigma x ~bits:delta_zero_bits ~first_shifted:true

(** DeltaOne(x) = sigma(x, [10, 17, 19], true) — first op is SHR *)
let delta_one (x : Uint32.t) : Uint32.t =
  sigma x ~bits:delta_one_bits ~first_shifted:true

(** Ch(x, y, z) = (x AND y) + (NOT_unchecked(x) AND z).
    Matches o1js Ch for UInt32 (sha2.ts line 439-443). *)
let ch (x : Uint32.t) (y : Uint32.t) (z : Uint32.t) : Uint32.t =
  let x_and_y = Uint32.to_field (Uint32.bit_and x y) in
  let not_x_and_z = Uint32.to_field (Uint32.bit_and (Uint32.bit_not x) z) in
  Uint32.of_field (seal Step.Field.(x_and_y + not_x_and_z))

(** Maj(x, y, z) = (x + y + z - (x XOR y XOR z)) / 2.
    Matches o1js Maj for UInt32 (sha2.ts line 456-459). *)
let maj (x : Uint32.t) (y : Uint32.t) (z : Uint32.t) : Uint32.t =
  let xf = Uint32.to_field x in
  let yf = Uint32.to_field y in
  let zf = Uint32.to_field z in
  let sum = seal (Step.Field.add (Step.Field.add xf yf) zf) in
  let xor_val = Uint32.to_field (Uint32.xor (Uint32.xor x y) z) in
  (* (sum - xor) / 2 = (sum - xor) * (1/2 mod p) *)
  let diff = Step.Field.sub sum xor_val in
  let result = seal (Step.Field.div diff (Step.Field.of_int 2)) in
  Uint32.of_field result

(** Create message schedule from 16-word block → 64 words.
    Matches o1js messageSchedule (sha2.ts lines 311-335). *)
let message_schedule (block : Uint32.t array) : Uint32.t array =
  assert (Array.length block = 16) ;
  let w = Array.create ~len:64 (Uint32.of_int 0) in
  Array.blit ~src:block ~src_pos:0 ~dst:w ~dst_pos:0 ~len:16 ;
  for t = 16 to 63 do
    (* Unreduced: DeltaOne(W[t-2]) + W[t-7] + DeltaZero(W[t-15]) + W[t-16] *)
    let d1 = Uint32.to_field (delta_one w.(t - 2)) in
    let w7 = Uint32.to_field w.(t - 7) in
    let d0 = Uint32.to_field (delta_zero w.(t - 15)) in
    let w16 = Uint32.to_field w.(t - 16) in
    let unreduced =
      Step.Field.add (Step.Field.add d1 w7) (Step.Field.add d0 w16)
    in
    w.(t) <- reduce_mod unreduced
  done ;
  w

(** SHA-256 compression function on one 16-word block.
    Matches o1js compression (sha2.ts lines 346-394). *)
let compress (h : Uint32.t array) (w : Uint32.t array) : Uint32.t array =
  let a = ref h.(0) in
  let b = ref h.(1) in
  let c = ref h.(2) in
  let d = ref h.(3) in
  let e = ref h.(4) in
  let f = ref h.(5) in
  let g = ref h.(6) in
  let hh = ref h.(7) in
  for t = 0 to 63 do
    (* unreducedT1 = h + SigmaOne(e) + Ch(e,f,g) + K[t] + W[t] *)
    let unreduced_t1 = seal Step.Field.(
      Uint32.to_field !hh
      + Uint32.to_field (sigma_one !e)
      + Uint32.to_field (ch !e !f !g)
      + of_int k_constants.(t)
      + Uint32.to_field w.(t)) in
    (* unreducedT2 = SigmaZero(a) + Maj(a,b,c) *)
    let unreduced_t2 = Step.Field.(
      Uint32.to_field (sigma_zero !a) + Uint32.to_field (maj !a !b !c)) in
    hh := !g ;
    g := !f ;
    f := !e ;
    e := reduce_mod Step.Field.(Uint32.to_field !d + unreduced_t1) ;
    d := !c ;
    c := !b ;
    b := !a ;
    a := reduce_mod Step.Field.(unreduced_t2 + unreduced_t1)
  done ;
  (* Intermediate hash: H[i] = H[i] + variable[i] mod 2^32 *)
  [| Uint32.add h.(0) !a
   ; Uint32.add h.(1) !b
   ; Uint32.add h.(2) !c
   ; Uint32.add h.(3) !d
   ; Uint32.add h.(4) !e
   ; Uint32.add h.(5) !f
   ; Uint32.add h.(6) !g
   ; Uint32.add h.(7) !hh
  |]

(** Initial SHA-256 state as circuit UInt32 constants. *)
let initial_state () : Uint32.t array =
  Array.map h_init ~f:Uint32.of_int

(** Hash pre-padded message blocks. Each block is 16 UInt32 words.
    The caller is responsible for SHA-256 padding. *)
let hash_blocks (blocks : Uint32.t array array) : Uint32.t array =
  let h = ref (initial_state ()) in
  Array.iter blocks ~f:(fun block ->
      let w = message_schedule block in
      h := compress !h w ) ;
  !h
