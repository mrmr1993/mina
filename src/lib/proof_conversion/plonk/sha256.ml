(** SHA-256 hash function implemented as circuit constraints.

    Used by the PLONK Fiat-Shamir transcript for challenge derivation.
    Each SHA-256 compression round uses Ch, Maj, Sigma operations
    on UInt32 values.

    Reference: nori-proof-conversion/src/plonk/fiat-shamir/ *)

open! Core_kernel

(** SHA-256 initial hash values (first 32 bits of fractional parts
    of square roots of first 8 primes). *)
let h_init =
  [| 0x6a09e667
   ; 0xbb67ae85
   ; 0x3c6ef372
   ; 0xa54ff53a
   ; 0x510e527f
   ; 0x9b05688c
   ; 0x1f83d9ab
   ; 0x5be0cd19
  |]

(** SHA-256 round constants (first 32 bits of fractional parts
    of cube roots of first 64 primes). *)
let k =
  [| 0x428a2f98
   ; 0x71374491
   ; 0xb5c0fbcf
   ; 0xe9b5dba5
   ; 0x3956c25b
   ; 0x59f111f1
   ; 0x923f82a4
   ; 0xab1c5ed5
   ; 0xd807aa98
   ; 0x12835b01
   ; 0x243185be
   ; 0x550c7dc3
   ; 0x72be5d74
   ; 0x80deb1fe
   ; 0x9bdc06a7
   ; 0xc19bf174
   ; 0xe49b69c1
   ; 0xefbe4786
   ; 0x0fc19dc6
   ; 0x240ca1cc
   ; 0x2de92c6f
   ; 0x4a7484aa
   ; 0x5cb0a9dc
   ; 0x76f988da
   ; 0x983e5152
   ; 0xa831c66d
   ; 0xb00327c8
   ; 0xbf597fc7
   ; 0xc6e00bf3
   ; 0xd5a79147
   ; 0x06ca6351
   ; 0x14292967
   ; 0x27b70a85
   ; 0x2e1b2138
   ; 0x4d2c6dfc
   ; 0x53380d13
   ; 0x650a7354
   ; 0x766a0abb
   ; 0x81c2c92e
   ; 0x92722c85
   ; 0xa2bfe8a1
   ; 0xa81a664b
   ; 0xc24b8b70
   ; 0xc76c51a3
   ; 0xd192e819
   ; 0xd6990624
   ; 0xf40e3585
   ; 0x106aa070
   ; 0x19a4c116
   ; 0x1e376c08
   ; 0x2748774c
   ; 0x34b0bcb5
   ; 0x391c0cb3
   ; 0x4ed8aa4a
   ; 0x5b9cca4f
   ; 0x682e6ff3
   ; 0x748f82ee
   ; 0x78a5636f
   ; 0x84c87814
   ; 0x8cc70208
   ; 0x90befffa
   ; 0xa4506ceb
   ; 0xbef9a3f7
   ; 0xc67178f2
  |]

(** Ch(x, y, z) = (x AND y) XOR (NOT x AND z) *)
let ch (x : Uint32.t) (y : Uint32.t) (z : Uint32.t) : Uint32.t =
  let xy = Uint32.bit_and x y in
  let nx = Uint32.bit_not x in
  let nxz = Uint32.bit_and nx z in
  Uint32.xor xy nxz

(** Maj(x, y, z) = (x AND y) XOR (x AND z) XOR (y AND z) *)
let maj (x : Uint32.t) (y : Uint32.t) (z : Uint32.t) : Uint32.t =
  let xy = Uint32.bit_and x y in
  let xz = Uint32.bit_and x z in
  let yz = Uint32.bit_and y z in
  Uint32.xor (Uint32.xor xy xz) yz

(** Sigma_0(x) = ROTR^2(x) XOR ROTR^13(x) XOR ROTR^22(x) *)
let sigma_0 (x : Uint32.t) : Uint32.t =
  let r2 = Uint32.rotr x ~n:2 in
  let r13 = Uint32.rotr x ~n:13 in
  let r22 = Uint32.rotr x ~n:22 in
  Uint32.xor (Uint32.xor r2 r13) r22

(** Sigma_1(x) = ROTR^6(x) XOR ROTR^11(x) XOR ROTR^25(x) *)
let sigma_1 (x : Uint32.t) : Uint32.t =
  let r6 = Uint32.rotr x ~n:6 in
  let r11 = Uint32.rotr x ~n:11 in
  let r25 = Uint32.rotr x ~n:25 in
  Uint32.xor (Uint32.xor r6 r11) r25

(** sigma_0(x) = ROTR^7(x) XOR ROTR^18(x) XOR SHR^3(x) *)
let little_sigma_0 (x : Uint32.t) : Uint32.t =
  let r7 = Uint32.rotr x ~n:7 in
  let r18 = Uint32.rotr x ~n:18 in
  let s3 = Uint32.shr x ~n:3 in
  Uint32.xor (Uint32.xor r7 r18) s3

(** sigma_1(x) = ROTR^17(x) XOR ROTR^19(x) XOR SHR^10(x) *)
let little_sigma_1 (x : Uint32.t) : Uint32.t =
  let r17 = Uint32.rotr x ~n:17 in
  let r19 = Uint32.rotr x ~n:19 in
  let s10 = Uint32.shr x ~n:10 in
  Uint32.xor (Uint32.xor r17 r19) s10

(** Expand 16 message words to 64 words. *)
let message_schedule (block : Uint32.t array) : Uint32.t array =
  assert (Array.length block = 16) ;
  let w = Array.create ~len:64 (Uint32.of_int 0) in
  Array.blit ~src:block ~src_pos:0 ~dst:w ~dst_pos:0 ~len:16 ;
  for i = 16 to 63 do
    let s0 = little_sigma_0 w.(i - 15) in
    let s1 = little_sigma_1 w.(i - 2) in
    w.(i) <- Uint32.add (Uint32.add (Uint32.add w.(i - 16) s0) w.(i - 7)) s1
  done ;
  w

(** One SHA-256 compression function on a 16-word block. *)
let compress (h : Uint32.t array) (block : Uint32.t array) : Uint32.t array =
  let w = message_schedule block in
  let a = ref h.(0) in
  let b = ref h.(1) in
  let c = ref h.(2) in
  let d = ref h.(3) in
  let e = ref h.(4) in
  let f = ref h.(5) in
  let g = ref h.(6) in
  let hh = ref h.(7) in
  for i = 0 to 63 do
    let s1 = sigma_1 !e in
    let ch_efg = ch !e !f !g in
    let temp1 =
      Uint32.add
        (Uint32.add
           (Uint32.add (Uint32.add !hh s1) ch_efg)
           (Uint32.of_int k.(i)) )
        w.(i)
    in
    let s0 = sigma_0 !a in
    let maj_abc = maj !a !b !c in
    let temp2 = Uint32.add s0 maj_abc in
    hh := !g ;
    g := !f ;
    f := !e ;
    e := Uint32.add !d temp1 ;
    d := !c ;
    c := !b ;
    b := !a ;
    a := Uint32.add temp1 temp2
  done ;
  [| Uint32.add h.(0) !a
   ; Uint32.add h.(1) !b
   ; Uint32.add h.(2) !c
   ; Uint32.add h.(3) !d
   ; Uint32.add h.(4) !e
   ; Uint32.add h.(5) !f
   ; Uint32.add h.(6) !g
   ; Uint32.add h.(7) !hh
  |]

(** Hash a message (array of UInt32 words, already padded). *)
let hash_padded (blocks : Uint32.t array array) : Uint32.t array =
  let h = Array.map h_init ~f:Uint32.of_int in
  Array.fold blocks ~init:h ~f:(fun h block -> compress h block)
