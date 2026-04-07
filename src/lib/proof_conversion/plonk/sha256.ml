(** SHA2

    This module provides a SHA2 provable gadget, including SHA256.

    https://csrc.nist.gov/pubs/fips/180-4/upd1/final

    Reference: o1js/src/lib/provable/gadgets/sha256.ts *)

open! Core_kernel
module Step = Pickles.Impls.Step
module FF = Snarky_foreign_field.Foreign_field

(* constants §4.2.2 *)
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

(* initial hash values §5.3.3 *)
let h_init =
  [| 0x6a09e667; 0xbb67ae85; 0x3c6ef372; 0xa54ff53a
   ; 0x510e527f; 0x9b05688c; 0x1f83d9ab; 0x5be0cd19
  |]

let seal (x : Step.Field.t) : Step.Field.t = FF.seal x

(* ch(x, y, z) = (x & y) ^ (~x & z)
               = (x & y) + (~x & z) (since x & ~x = 0) *)
let ch (x : Uint32.t) (y : Uint32.t) (z : Uint32.t) : Uint32.t =
  let x_and_y = Uint32.to_field (Uint32.bit_and x y) in
  let x_not_and_z = Uint32.to_field (Uint32.bit_and (Uint32.bit_not x) z) in
  let ch = seal Step.Field.(x_and_y + x_not_and_z) in
  Uint32.of_field ch

(* maj(x, y, z) = (x & y) ^ (x & z) ^ (y & z)
               = (x + y + z - (x ^ y ^ z)) / 2 *)
let maj (x : Uint32.t) (y : Uint32.t) (z : Uint32.t) : Uint32.t =
  let sum = seal Step.Field.(Uint32.to_field x + Uint32.to_field y
                             + Uint32.to_field z) in
  let xor_val = Uint32.to_field (Uint32.xor (Uint32.xor x y) z) in
  let maj = seal (Step.Field.div (Step.Field.sub sum xor_val) (Step.Field.of_int 2)) in
  Uint32.of_field maj

let rotr (n : int) (x : Uint32.t) : Uint32.t = Uint32.rotr x ~n
let shr (n : int) (x : Uint32.t) : Uint32.t = Uint32.shr x ~n

(* Simple sigma: individual ROTR/SHR + XOR, used for constant inputs *)
let sigma_simple (u : Uint32.t) ~(bits : int * int * int)
    ~(first_shifted : bool) : Uint32.t =
  let r0, r1, r2 = bits in
  let rot0 = if first_shifted then shr r0 u else rotr r0 u in
  let rot1 = rotr r1 u in
  let rot2 = rotr r2 u in
  Uint32.xor (Uint32.xor rot0 rot1) rot2

(* Fused sigma: decompose, reassemble 3 rotations, XOR.
   Matches o1js sigma() (sha256.ts:161-224). *)
let sigma (u : Uint32.t) ~(bits : int * int * int)
    ~(first_shifted : bool) : Uint32.t =
  if Uint32.is_constant u then sigma_simple u ~bits ~first_shifted
  else
  let r0, r1, r2 = bits in  (* TODO assert bits are sorted *)
  let x = Uint32.to_field u in
  let d0 = r0 in
  let d1 = r1 - r0 in
  let d2 = r2 - r1 in
  let d3 = 32 - r2 in
  (* decompose x into 4 chunks of size d0, d1, d2, d3 *)
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
  (* range check each chunk
     we only need to range check to 16 bits relying on the requirement that
     the rotated values are range-checked to 32 bits later; see comments below *)
  Uint32.range_check_16 x0 ;
  Uint32.range_check_16 x1 ;
  Uint32.range_check_16 x2 ;
  Uint32.range_check_16 x3 ;
  (* prove x decomposition *)
  let shift n = Step.Field.of_int (1 lsl n) in
  (* x === x0 + x1*2^d0 + x2*2^(d0+d1) + x3*2^(d0+d1+d2) *)
  let x23 = seal (Step.Field.add x2 (Step.Field.mul x3 (shift d2))) in
  let x123 = seal (Step.Field.add x1 (Step.Field.mul x23 (shift d1))) in
  Step.Field.Assert.equal
    (Step.Field.add x0 (Step.Field.mul x123 (shift d0))) x ;
  (* ^ proves that 2^(32-d3)*x3 < x < 2^32 => x3 < 2^d3 *)
  (* reassemble chunks into rotated values *)
  let x_rot_r0 =
    if not first_shifted then begin
      (* rotr(x, r0) = x1 + x2*2^d1 + x3*2^(d1+d2) + x0*2^(d1+d2+d3) *)
      seal (Step.Field.add x123 (Step.Field.mul x0 (shift (d1 + d2 + d3))))
      (* ^ proves that 2^(32-d0)*x0 < xRotR0 => x0 < 2^d0 if we check xRotR0 < 2^32 later *)
    end else begin
      (* shr(x, r0) = x1 + x2*2^d1 + x3*2^(d1+d2) *)
      (* finish x0 < 2^d0 proof: *)
      Uint32.range_check_16 (seal (Step.Field.mul x0 (shift (16 - d0)))) ;
      x123
    end
  in
  (* rotr(x, r1) = x2 + x3*2^d2 + x0*2^(d2+d3) + x1*2^(d2+d3+d0) *)
  let x01 = seal (Step.Field.add x0 (Step.Field.mul x1 (shift d0))) in
  let x_rot_r1 = seal (Step.Field.add x23 (Step.Field.mul x01 (shift (d2 + d3)))) in
  (* ^ proves that 2^(32-d1)*x1 < xRotR1 => x1 < 2^d1 if we check xRotR1 < 2^32 later *)
  (* rotr(x, r2) = x3 + x0*2^d3 + x1*2^(d3+d0) + x2*2^(d3+d0+d1) *)
  let x012 = seal (Step.Field.add x01 (Step.Field.mul x2 (shift (d0 + d1)))) in
  let x_rot_r2 = seal (Step.Field.add x3 (Step.Field.mul x012 (shift d3))) in
  (* ^ proves that 2^(32-d2)*x2 < xRotR2 => x2 < 2^d2 if we check xRotR2 < 2^32 later *)
  (* since xor() is implicitly range-checking both of its inputs, this provides the missing
     proof that xRotR0, xRotR1, xRotR2 < 2^32, which implies x0 < 2^d0, x1 < 2^d1, x2 < 2^d2 *)
  Uint32.xor
    (Uint32.xor (Uint32.of_field x_rot_r0) (Uint32.of_field x_rot_r1))
    (Uint32.of_field x_rot_r2)

let sigma_zero (x : Uint32.t) : Uint32.t =
  sigma x ~bits:(2, 13, 22) ~first_shifted:false

let sigma_one (x : Uint32.t) : Uint32.t =
  sigma x ~bits:(6, 11, 25) ~first_shifted:false

(* lowercase sigma = delta to avoid confusing function names *)

let delta_zero (x : Uint32.t) : Uint32.t =
  sigma x ~bits:(3, 7, 18) ~first_shifted:true

let delta_one (x : Uint32.t) : Uint32.t =
  sigma x ~bits:(10, 17, 19) ~first_shifted:true

(** Performs the SHA-256 compression function on the given hash values
    and message schedule.

    @param h The initial or intermediate hash values (8-element array of UInt32).
    @param w The message schedule (64-element array of UInt32).

    @returns The updated intermediate hash values after compression. *)
let compress (h : Uint32.t array) (w : Uint32.t array) : Uint32.t array =
  (* initialize working variables *)
  let a = ref h.(0) in
  let b = ref h.(1) in
  let c = ref h.(2) in
  let d = ref h.(3) in
  let e = ref h.(4) in
  let f = ref h.(5) in
  let g = ref h.(6) in
  let hh = ref h.(7) in
  (* main loop *)
  for t = 0 to 63 do
    (* T1 is unreduced and not proven to be 32bit, we will do this later to save constraints *)
    let s1 = sigma_one !e in
    let ch_val = ch !e !f !g in
    let unreduced_t1 = seal Step.Field.(
      Uint32.to_field !hh
      + Uint32.to_field s1
      + Uint32.to_field ch_val
      + of_int k_constants.(t)
      + Uint32.to_field w.(t)) in
    (* T2 is also unreduced *)
    let s0 = sigma_zero !a in
    let maj_val = maj !a !b !c in
    let unreduced_t2 = Step.Field.(
      Uint32.to_field s0
      + Uint32.to_field maj_val) in
    hh := !g ;
    g := !f ;
    f := !e ;
    (* mod 32bit the unreduced field element *)
    e := snd (Uint32.div_mod_32 Step.Field.(Uint32.to_field !d + unreduced_t1) ~n_bits:48) ;
    d := !c ;
    c := !b ;
    b := !a ;
    (* mod 32bit *)
    a := snd (Uint32.div_mod_32 Step.Field.(unreduced_t2 + unreduced_t1) ~n_bits:48)
  done ;
  (* new intermediate hash value — use let bindings to ensure
     left-to-right evaluation order matching o1js *)
  let r0 = Uint32.add h.(0) !a in
  let r1 = Uint32.add h.(1) !b in
  let r2 = Uint32.add h.(2) !c in
  let r3 = Uint32.add h.(3) !d in
  let r4 = Uint32.add h.(4) !e in
  let r5 = Uint32.add h.(5) !f in
  let r6 = Uint32.add h.(6) !g in
  let r7 = Uint32.add h.(7) !hh in
  [| r0; r1; r2; r3; r4; r5; r6; r7 |]

(** Prepares the message schedule for the SHA-256 compression function
    from the given message block.

    @param m The 512-bit message block (16-element array of UInt32).
    @returns The message schedule (64-element array of UInt32). *)
let message_schedule (m : Uint32.t array) : Uint32.t array =
  assert (Array.length m = 16) ;
  (* for each message block of 16 x 32bit do: *)
  let w = Array.create ~len:64 (Uint32.of_int 0) in
  (* prepare message block *)
  for t = 0 to 15 do w.(t) <- m.(t) done ;
  for t = 16 to 63 do
    (* the field element is unreduced and not proven to be 32bit, we will do this later to save constraints *)
    let d1 = delta_one w.(t - 2) in
    let w7 = w.(t - 7) in
    let d0 = delta_zero w.(t - 15) in
    let w16 = w.(t - 16) in
    let unreduced = Step.Field.(
      Uint32.to_field d1
      + Uint32.to_field w7
      + Uint32.to_field d0
      + Uint32.to_field w16) in
    (* mod 32bit the unreduced field element *)
    w.(t) <- snd (Uint32.div_mod_32 unreduced ~n_bits:48)
  done ;
  w

(** Initial SHA-256 state as circuit UInt32 constants. *)
let initial_state () : Uint32.t array =
  Array.map h_init ~f:Uint32.of_int

(** Hash pre-padded message blocks. Each block is 16 UInt32 words.
    The caller is responsible for SHA-256 padding.
    Returns 8 UInt32 words (the hash state). *)
let hash_blocks (blocks : Uint32.t array array) : Uint32.t array =
  let h = ref (initial_state ()) in
  let n = Array.length blocks in
  for i = 0 to n - 1 do
    let w = message_schedule blocks.(i) in
    h := compress !h w
  done ;
  !h
