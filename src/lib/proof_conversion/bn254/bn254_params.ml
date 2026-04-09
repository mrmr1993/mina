(** BN254 curve parameters for proof conversion.

    These are pure constants with no circuit logic -- used by both
    out-of-circuit witness computation and in-circuit verification. *)

open! Core_kernel
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
  [| 1
   ; 1
   ; 0
   ; 1
   ; 0
   ; 0
   ; -1
   ; 0
   ; 1
   ; 1
   ; 0
   ; 0
   ; 0
   ; -1
   ; 0
   ; 0
   ; 1
   ; 1
   ; 0
   ; 0
   ; -1
   ; 0
   ; 0
   ; 0
   ; 0
   ; 0
   ; 1
   ; 0
   ; 0
   ; -1
   ; 0
   ; 0
   ; 1
   ; 1
   ; 1
   ; 0
   ; 0
   ; 0
   ; 0
   ; -1
   ; 0
   ; 1
   ; 0
   ; 0
   ; -1
   ; 0
   ; 1
   ; 1
   ; 0
   ; 0
   ; 1
   ; 0
   ; 0
   ; -1
   ; 1
   ; 0
   ; 0
   ; -1
   ; 0
   ; 1
   ; 0
   ; 1
   ; 0
   ; 0
   ; 0
  |]

(* (9 + u)^(i * (p - 1) / 6) for i in 1..5 *)

(** Frobenius gamma constants (gamma_1s).
    gamma_1s[i] = Fp2 values used in Frobenius endomorphism computation.
    Each is a pair (c0, c1) representing c0 + c1 * u in Fp2. *)
let gamma_1s =
  [| ( of_string
         "8376118865763821496583973867626364092589906065868298776909617916018768340080"
     , of_string
         "16469823323077808223889137241176536799009286646108169935659301613961712198316"
     )
   ; ( of_string
         "21575463638280843010398324269430826099269044274347216827212613867836435027261"
     , of_string
         "10307601595873709700152284273816112264069230130616436755625194854815875713954"
     )
   ; ( of_string
         "2821565182194536844548159561693502659359617185244120367078079554186484126554"
     , of_string
         "3505843767911556378687030309984248845540243509899259641013678093033130930403"
     )
   ; ( of_string
         "2581911344467009335267311115468803099551665605076196740867805258568234346338"
     , of_string
         "19937756971775647987995932169929341994314640652964949448313374472400716661030"
     )
   ; ( of_string
         "685108087231508774477564247770172212460312782337200605669322048753928464687"
     , of_string
         "8447204650696766136447902020341177575205426561248465145919723016860428151883"
     )
  |]

(** Frobenius gamma_2s constants.
    gamma_2s[i] = gamma_1s[i] * conjugate(gamma_1s[i]).
    All have c1 = 0, so they are Fp elements. *)
let gamma_2s =
  [| ( of_string
         "21888242871839275220042445260109153167277707414472061641714758635765020556617"
     , zero )
   ; ( of_string
         "21888242871839275220042445260109153167277707414472061641714758635765020556616"
     , zero )
   ; ( of_string
         "21888242871839275222246405745257275088696311157297823662689037894645226208582"
     , zero )
   ; ( of_string "2203960485148121921418603742825762020974279258880205651966"
     , zero )
   ; ( of_string "2203960485148121921418603742825762020974279258880205651967"
     , zero )
  |]

(** Frobenius gamma_3s constants.
    gamma_3s[i] = gamma_1s[i] * gamma_2s[i]. *)
let gamma_3s =
  [| ( of_string
         "11697423496358154304825782922584725312912383441159505038794027105778954184319"
     , of_string
         "303847389135065887422783454877609941456349188919719272345083954437860409601"
     )
   ; ( of_string
         "3772000881919853776433695186713858239009073593817195771773381919316419345261"
     , of_string
         "2236595495967245188281701248203181795121068902605861227855261137820944008926"
     )
   ; ( of_string
         "19066677689644738377698246183563772429336693972053703295610958340458742082029"
     , of_string
         "18382399103927718843559375435273026243156067647398564021675359801612095278180"
     )
   ; ( of_string
         "5324479202449903542726783395506214481928257762400643279780343368557297135718"
     , of_string
         "16208900380737693084919495127334387981393726419856888799917914180988844123039"
     )
   ; ( of_string
         "8941241848238582420466759817324047081148088512956452953208002715982955420483"
     , of_string
         "10338197737521362862238855242243140895517409139741313354160881284257516364953"
     )
  |]

(** GLV endomorphism constant: beta = cube root of unity in Fp.
    Satisfies beta^3 = 1 (mod p) and beta != 1.
    Used to compute the GLV endomorphism phi(x, y) = (beta * x, y). *)
let glv_beta =
  of_string
    "21888242871839275220042445260109153167277707414472061641714758635765020556616"

(** GLV eigenvalue: lambda = cube root of unity in Fr.
    Satisfies lambda^3 = 1 (mod r) and lambda != 1.
    The endomorphism phi acts as scalar multiplication by lambda:
    phi(P) = [lambda] P for all P in G1. *)
let glv_lambda =
  of_string
    "21888242871839275217838484774961031246154997185409878258781734729429964517155"

(** LLL-reduced lattice basis vectors for GLV scalar decomposition.
    Given scalar k, we decompose k = k1 + lambda * k2 (mod r) where
    |k1|, |k2| < sqrt(r) ~ 2^128, halving the number of doublings.

    The decomposition uses:
      beta1 = round(k * n22 / r)
      beta2 = round(-k * n12 / r)
      b1 = beta1 * n11 + beta2 * n21
      b2 = beta1 * n12 + beta2 * n22
      k1 = k - b1,  k2 = -b2 *)
let glv_n11 = of_string "147946756881789319000765030803803410728"

let glv_n12 = of_string "9931322734385697763"

(* Note: n21 = n12, n22 = r - n11 - n21. These relationships come from
   the LLL-reduced basis of the lattice {(a, b) : a + lambda*b = 0 mod r}. *)
let glv_n21 = of_string "9931322734385697763"

let glv_n22 = of_string "147946756881789319010696353538189108491"

(** Fp2 non-residue used for tower extension: xi = 9 + u *)
let fp2_non_residue = (of_int 9, one)

(** w27: 27th root of unity in Fp12, used for KZG shift power.
    Only c0.c2 is non-zero.
    Matches nori make_w27 from plonk/helpers.ts. *)
let w27 () =
  let z = zero in
  let fp2_z = (z, z) in
  let c0_c2 =
    ( of_string
        "8204864362109909869166472767738877274689483185363591877943943203703805152849"
    , of_string
        "17912368812864921115467448876996876278487602260484145953989158612875588124088"
    )
  in
  ((fp2_z, fp2_z, c0_c2), (fp2_z, fp2_z, fp2_z))

(** w27^2: precomputed square of w27. *)
let w27_sq () =
  let z = zero in
  let fp2_z = (z, z) in
  let c0_c1 =
    ( of_string
        "1066574321224194029098510617320359175933088740832171073526214612239131844577"
    , of_string
        "7570967981015191924441724388928800689651906253447554305937154440815434452498"
    )
  in
  ((fp2_z, c0_c1, fp2_z), (fp2_z, fp2_z, fp2_z))
