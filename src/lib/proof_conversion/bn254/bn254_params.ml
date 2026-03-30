(** BN254 curve parameters for proof conversion.

    These are pure constants with no circuit logic — used by both
    out-of-circuit witness computation and in-circuit verification.

    Reference: nori-proof-conversion/src/towers/consts.ts *)

open Bignum_bigint

(** BN254 base field modulus (Fp).
    p = 21888242871839275222246405745257275088696311157297823662689037894645226208583 *)
let p =
  of_string
    "21888242871839275222246405745257275088696311157297823662689037894645226208583"

(** BN254 scalar field modulus (Fr).
    r = 21888242871839275222246405745257275088548364400416034343698204186575808495617 *)
let r =
  of_string
    "21888242871839275222246405745257275088548364400416034343698204186575808495617"

(** (p - 1) / 6, used for Frobenius computations. *)
let p_minus_1_div_6 =
  of_string
    "3648040478639879203707734290876212514782718526216303943781506315774204368097"

(** BN254 G1 generator: (1, 2) *)
let g1_generator_x = one

let g1_generator_y = of_int 2

(** BN254 curve parameter: y^2 = x^3 + b where b = 3 *)
let curve_b = of_int 3

(** BN254 twist parameter for G2: b' = 3 / (9 + i) *)

(** BN254 G2 generator coordinates (over Fp2).
    G2 generator x = (x0, x1), y = (y0, y1) *)
let g2_generator_x0 =
  of_string
    "10857046999023057135944570762232829481370756359578518086990519993285655852781"

let g2_generator_x1 =
  of_string
    "11559732032986387107991004021392285783925812861821192530917403151452391805634"

let g2_generator_y0 =
  of_string
    "8495653923123431417604973247489272438418190587263600148770280649306958101930"

let g2_generator_y1 =
  of_string
    "4082367875863433681332203403145435568316851327593401208105741076214120093531"

(** ATE loop count in NAF (non-adjacent form) representation.
    Big-endian: MSB first. Values are -1, 0, or 1.
    This is 6x + 2 where x is the BN254 parameter. *)
let ate_loop_count =
  [| 1; 1; 0; 1; 0; 0; -1; 0; 1; 1; 0; 0; 0; -1; 0; 0
   ; 1; 1; 0; 0; -1; 0; 0; 0; 0; 0; 1; 0; 0; -1; 0; 0
   ; 1; 1; 1; 0; 0; 0; 0; -1; 0; 1; 0; 0; -1; 0; 1; 1
   ; 0; 0; 1; 0; 0; -1; 1; 0; 0; -1; 0; 1; 0; 1; 0; 0; 0
  |]

(** Frobenius gamma constants (gamma_1s).
    gamma_1s[i] = Fp2 values used in Frobenius endomorphism computation.
    Each is a pair (c0, c1) representing c0 + c1 * u in Fp2. *)
let gamma_1s =
  [| ( of_string
         "8376118865763821496583973867626364092589906065868298776909617916018768340080"
     , of_string
         "16469823323077808223889137241176536799009286646108169935659301613961712198316" )
   ; ( of_string
         "21888242871839275220042445260109153167277707414472061641714758635765020556616"
     , zero )
   ; ( of_string
         "21888242871839275222246405745257275088696311157297823662689037894645226208582"
     , zero )
   ; ( of_string
         "8376118865763821496583973867626364092589906065868298776909617916018768340080"
     , of_string
         "5418419548761064309947104879080738992106504571858654569765736258599809058267" )
   ; ( of_string
         "2203960485148121921418603742825762020974279258880205651966"
     , zero )
  |]

(** Fp2 non-residue used for tower extension: xi = 9 + u *)
let fp2_non_residue = (of_int 9, one)
