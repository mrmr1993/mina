(** Groth16 witness tracker — out-of-circuit computation.

    Pre-computes all intermediate values needed by the 16 recursive
    circuits. Operates on pure bignum arithmetic (no circuit constraints). *)

open! Core_kernel
module BI = Bignum_bigint

let p = Bn254_params.p

(** Out-of-circuit Fp arithmetic. *)
module Fp = struct
  let add a b = BI.((a + b) % p)

  let sub a b = BI.((((a - b) % p) + p) % p)

  let mul a b = BI.(a * b % p)

  let inv a =
    match Snarky_foreign_field.Foreign_field.bignum_mod_inverse a ~f:p with
    | Some v ->
        v
    | None ->
        failwith "Fp.inv: inverse does not exist"

  let neg a = sub BI.zero a

  let div a b = mul a (inv b)
end

(** Out-of-circuit Fp2 arithmetic. *)
module Fp2 = struct
  type t = BI.t * BI.t [@@deriving sexp]

  let add (a0, a1) (b0, b1) : t = (Fp.add a0 b0, Fp.add a1 b1)

  let sub (a0, a1) (b0, b1) : t = (Fp.sub a0 b0, Fp.sub a1 b1)

  let mul (a0, a1) (b0, b1) : t =
    let v0 = Fp.mul a0 b0 in
    let v1 = Fp.mul a1 b1 in
    (Fp.sub v0 v1, Fp.sub (Fp.mul (Fp.add a0 a1) (Fp.add b0 b1)) (Fp.add v0 v1))

  let neg (a0, a1) : t = (Fp.neg a0, Fp.neg a1)

  let conjugate (a0, a1) : t = (a0, Fp.neg a1)

  let square (a0, a1) : t =
    let ab = Fp.mul a0 a1 in
    (Fp.mul (Fp.add a0 a1) (Fp.sub a0 a1), Fp.add ab ab)

  let inverse (a0, a1) : t =
    let norm = Fp.add (Fp.mul a0 a0) (Fp.mul a1 a1) in
    let norm_inv = Fp.inv norm in
    (Fp.mul a0 norm_inv, Fp.neg (Fp.mul a1 norm_inv))

  let zero : t = (BI.zero, BI.zero)

  let one : t = (BI.one, BI.zero)

  let mul_by_fp (a0, a1) s : t = (Fp.mul a0 s, Fp.mul a1 s)
end

(** Out-of-circuit Fp6 arithmetic. *)
module Fp6 = struct
  type t = Fp2.t * Fp2.t * Fp2.t

  let xi : Fp2.t = Bn254_params.fp2_non_residue

  let mul_by_nr x = Fp2.mul x xi

  let add (a0, a1, a2) (b0, b1, b2) : t =
    (Fp2.add a0 b0, Fp2.add a1 b1, Fp2.add a2 b2)

  let sub (a0, a1, a2) (b0, b1, b2) : t =
    (Fp2.sub a0 b0, Fp2.sub a1 b1, Fp2.sub a2 b2)

  let neg (a0, a1, a2) : t = (Fp2.neg a0, Fp2.neg a1, Fp2.neg a2)

  let mul (a0, a1, a2) (b0, b1, b2) : t =
    let a0b0 = Fp2.mul a0 b0 in
    let a1b2 = Fp2.mul a1 b2 in
    let a2b1 = Fp2.mul a2 b1 in
    let a0b1 = Fp2.mul a0 b1 in
    let a1b0 = Fp2.mul a1 b0 in
    let a2b2 = Fp2.mul a2 b2 in
    let a0b2 = Fp2.mul a0 b2 in
    let a1b1 = Fp2.mul a1 b1 in
    let a2b0 = Fp2.mul a2 b0 in
    ( Fp2.add a0b0 (mul_by_nr (Fp2.add a1b2 a2b1))
    , Fp2.add (Fp2.add a0b1 a1b0) (mul_by_nr a2b2)
    , Fp2.add (Fp2.add a0b2 a1b1) a2b0 )

  let zero : t = (Fp2.zero, Fp2.zero, Fp2.zero)

  let one : t = (Fp2.one, Fp2.zero, Fp2.zero)
end

(** Out-of-circuit Fp12 arithmetic. *)
module Fp12 = struct
  type t = Fp6.t * Fp6.t

  let mul (a0, a1) (b0, b1) : t =
    let v0 = Fp6.mul a0 b0 in
    let v1 = Fp6.mul a1 b1 in
    let v1_shifted =
      let c0, c1, c2 = v1 in
      (Fp6.mul_by_nr c2, c0, c1)
    in
    let c0 = Fp6.add v0 v1_shifted in
    let a01 = Fp6.add a0 a1 in
    let b01 = Fp6.add b0 b1 in
    let t = Fp6.mul a01 b01 in
    let c1 = Fp6.sub (Fp6.sub t v0) v1 in
    (c0, c1)

  let square a = mul a a

  let conjugate (a0, a1) : t = (a0, Fp6.neg a1)

  let inverse (a0, a1) : t =
    (* Only valid for unitary elements in the cyclotomic subgroup,
       where inverse = conjugate. *)
    conjugate (a0, a1)

  (** Frobenius: f^p. Conjugate Fp2 components, multiply by gamma_1s. *)
  let frobenius_pow_p ((c0, c1) : t) : t =
    let c00, c01, c02 = c0 in
    let c10, c11, c12 = c1 in
    let g = Bn254_params.gamma_1s in
    let t1 = Fp2.conjugate c00 in
    let t2 = Fp2.mul (Fp2.conjugate c10) g.(0) in
    let t3 = Fp2.mul (Fp2.conjugate c01) g.(1) in
    let t4 = Fp2.mul (Fp2.conjugate c11) g.(2) in
    let t5 = Fp2.mul (Fp2.conjugate c02) g.(3) in
    let t6 = Fp2.mul (Fp2.conjugate c12) g.(4) in
    ((t1, t3, t5), (t2, t4, t6))

  (** Frobenius squared: f^(p^2). No conjugation, multiply by gamma_2s. *)
  let frobenius_pow_p_squared ((c0, c1) : t) : t =
    let c00, c01, c02 = c0 in
    let c10, c11, c12 = c1 in
    let g = Bn254_params.gamma_2s in
    let t1 = c00 in
    let t2 = Fp2.mul c10 g.(0) in
    let t3 = Fp2.mul c01 g.(1) in
    let t4 = Fp2.mul c11 g.(2) in
    let t5 = Fp2.mul c02 g.(3) in
    let t6 = Fp2.mul c12 g.(4) in
    ((t1, t3, t5), (t2, t4, t6))

  (** Frobenius cubed: f^(p^3). Conjugate, multiply by gamma_3s. *)
  let frobenius_pow_p_cubed ((c0, c1) : t) : t =
    let c00, c01, c02 = c0 in
    let c10, c11, c12 = c1 in
    let g = Bn254_params.gamma_3s in
    let t1 = Fp2.conjugate c00 in
    let t2 = Fp2.mul (Fp2.conjugate c10) g.(0) in
    let t3 = Fp2.mul (Fp2.conjugate c01) g.(1) in
    let t4 = Fp2.mul (Fp2.conjugate c11) g.(2) in
    let t5 = Fp2.mul (Fp2.conjugate c02) g.(3) in
    let t6 = Fp2.mul (Fp2.conjugate c12) g.(4) in
    ((t1, t3, t5), (t2, t4, t6))

  let one : t = (Fp6.one, Fp6.zero)
end

(** G1 affine point (out-of-circuit). *)
module G1 = struct
  type t = { x : BI.t; y : BI.t }

  let negate p = { x = p.x; y = Fp.neg p.y }

  let of_proof_json (p : Proof_json.G1_constant.t) : t = { x = p.x; y = p.y }

  let add (p1 : t) (p2 : t) : t =
    let dx = Fp.sub p2.x p1.x in
    let dy = Fp.sub p2.y p1.y in
    let lambda = Fp.div dy dx in
    let lambda_sq = Fp.mul lambda lambda in
    let x3 = Fp.sub (Fp.sub lambda_sq p1.x) p2.x in
    let y3 = Fp.sub (Fp.mul lambda (Fp.sub p1.x x3)) p1.y in
    { x = x3; y = y3 }

  let double (p : t) : t =
    let x_sq = Fp.mul p.x p.x in
    let three_x_sq = Fp.add (Fp.add x_sq x_sq) x_sq in
    let two_y = Fp.add p.y p.y in
    let lambda = Fp.div three_x_sq two_y in
    let lambda_sq = Fp.mul lambda lambda in
    let two_x = Fp.add p.x p.x in
    let x3 = Fp.sub lambda_sq two_x in
    let y3 = Fp.sub (Fp.mul lambda (Fp.sub p.x x3)) p.y in
    { x = x3; y = y3 }

  (** Scalar multiplication by double-and-add. *)
  let scale (pt : t) (scalar : BI.t) : t =
    if BI.(scalar = zero) then failwith "G1.scale: zero scalar" ;
    let bits = BI.to_zarith_bigint scalar |> Z.to_bits in
    let n = String.length bits * 8 in
    let get_bit i =
      if i / 8 < String.length bits then
        (Char.to_int bits.[i / 8] lsr (i mod 8)) land 1
      else 0
    in
    (* Find highest set bit *)
    let highest = ref 0 in
    for i = 0 to n - 1 do
      if get_bit i = 1 then highest := i
    done ;
    let result = ref pt in
    for i = !highest - 1 downto 0 do
      result := double !result ;
      if get_bit i = 1 then result := add !result pt
    done ;
    !result
end

(** G2 affine point (out-of-circuit). *)
module G2 = struct
  type t = { x : Fp2.t; y : Fp2.t }

  let of_proof_json (p : Proof_json.G2_constant.t) : t = { x = p.x; y = p.y }

  let negate (p : t) : t = { x = p.x; y = Fp2.neg p.y }

  (** Frobenius endomorphism on G2: conjugate coords, multiply by gammas. *)
  let frobenius (p : t) : t =
    let g = Bn254_params.gamma_1s in
    { x = Fp2.mul (Fp2.conjugate p.x) g.(1)
    ; y = Fp2.mul (Fp2.conjugate p.y) g.(2)
    }

  (** Negative Frobenius: frobenius then negate y.
      Used for pi2B = -frobenius^2(B) = negative_frobenius(frobenius(B)). *)
  let negative_frobenius (p : t) : t =
    let g = Bn254_params.gamma_1s in
    { x = Fp2.mul (Fp2.conjugate p.x) g.(1)
    ; y = Fp2.neg (Fp2.mul (Fp2.conjugate p.y) g.(2))
    }
end

(** Line coefficient from G2 point operations. *)
module Line = struct
  type t = { lambda : Fp2.t; neg_mu : Fp2.t } [@@deriving sexp]
end

(** Compute the affine cache for a G1 point. *)
let compute_affine_cache (p : G1.t) : BI.t * BI.t =
  let y_inv = Fp.inv p.y in
  let x_over_y = Fp.mul p.x y_inv in
  (x_over_y, y_inv)

(** Per-iteration witness data for ate loop circuits. *)
type iteration_data =
  { f_before : Fp12.t
  ; double_line : Line.t
  ; add_line : Line.t option
  ; f_after : Fp12.t
  ; delta_double_line : Line.t
  ; delta_add_line : Line.t option
  ; gamma_double_line : Line.t
  ; gamma_add_line : Line.t option
  }

(** The witness tracker state. *)
type t =
  { proof : Proof_json.proof
  ; vk : Proof_json.vk
  ; c : Fp12.t
  ; c_inv : Fp12.t
  ; shift_power : int
  ; mutable t_point : G2.t  (** Current G2 point T *)
  ; mutable f : Fp12.t
  ; mutable g_digest : BI.t  (** Poseidon hash of line evaluation array *)
  ; mutable g_values : Fp12.t array
  ; mutable iterations : iteration_data array
  ; mutable line_hashes : BI.t array
  ; mutable frobenius_lines : Fp12.t array
        (** Evaluated Frobenius line corrections for zkp6:
          [0] = line from piB, [1] = line from pi2B, [2] = line from pi3B *)
  ; mutable frobenius_b_lines : Line.t array
        (** B-line coefficients for Frobenius:
          [0] = line through (T, piB), [1] = line through (T', pi2B) *)
  ; mutable frobenius_delta_lines : Line.t array
        (** Delta-line coefficients for Frobenius (from VK delta G2 point) *)
  ; mutable frobenius_gamma_lines : Line.t array
        (** Gamma-line coefficients for Frobenius (from VK gamma G2 point) *)
  }

(** Get the proof's G1 points for circuit witnessing. *)
let get_neg_a (t : t) : G1.t = G1.of_proof_json t.proof.neg_a

let get_c (t : t) : G1.t = G1.of_proof_json t.proof.c

let get_ic (t : t) (i : int) : G1.t = G1.of_proof_json t.vk.ic.(i)

(** Get the number of IC points. *)
let num_ic (t : t) : int = Array.length t.vk.ic

(** Get public inputs. *)
let get_public_input (t : t) (i : int) : BI.t = t.proof.public_inputs.(i)

let num_public_inputs (t : t) : int = Array.length t.proof.public_inputs

(** Compute ic_i scaled by pis[i-1]. Returns as G1 constant. *)
let get_scaled_ic (t : t) (ic_idx : int) (pi_idx : int) : G1.t =
  let ic = get_ic t ic_idx in
  let pi = get_public_input t pi_idx in
  G1.scale ic pi

(** Compute the partial IC accumulation for zkp14:
    ic0 + ic1*pis[0] + ic2*pis[1] + ic3*pis[2] *)
let get_partial_ic_acc (t : t) : G1.t =
  let ic0 = get_ic t 0 in
  let acc = G1.add ic0 (get_scaled_ic t 1 0) in
  let acc = G1.add acc (get_scaled_ic t 2 1) in
  G1.add acc (get_scaled_ic t 3 2)

(** Compute the full IC accumulation for zkp15:
    partial_acc + ic4*pis[3] + ic5*pis[4] *)
let get_full_ic_acc (t : t) : G1.t =
  let partial = get_partial_ic_acc t in
  let acc = G1.add partial (get_scaled_ic t 4 3) in
  G1.add acc (get_scaled_ic t 5 4)

(** Get the PI point (public input commitment) used in the pairing.
    This is the IC accumulation result = ic0 + sum(ic_i * pi_i).
    In the final circuit, the independently-computed IC accumulation
    must be asserted equal to this value. *)
let get_pi (t : t) : G1.t = get_full_ic_acc t

(** Construct the full Accumulator.Constant from the current tracker state.
    This provides all the data needed to witness the accumulator in-circuit. *)
let get_accumulator_constant (t : t) : Accumulator.Constant.t =
  let neg_a = get_neg_a t in
  let b_g2 = G2.of_proof_json t.vk.beta in
  let c_g1 = get_c t in
  let pi = get_pi t in
  (* The Accumulator module references the bn254 G1/G2 Constant types,
     but this file has local G1/G2 that shadow them. The record field
     labels are resolved via the type annotation on each sub-struct.
     G1.Constant.t = {x:BI.t; y:BI.t} and our G1.t = {x:BI.t; y:BI.t},
     so the values are compatible — we just need the labels. *)
  let module FF = Snarky_foreign_field.Foreign_field in
  (* Build proof sub-struct. The neg_a, c, pi fields need G1.Constant.t
     which has the same structure as our local G1.t. *)
  let neg_a_c = { Accumulator.G1_constant.x = neg_a.x; y = neg_a.y } in
  let b_c = { Accumulator.G2_constant.x = b_g2.x; y = b_g2.y } in
  let c_c = { Accumulator.G1_constant.x = c_g1.x; y = c_g1.y } in
  let pi_c = { Accumulator.G1_constant.x = pi.x; y = pi.y } in
  let t_c = { Accumulator.G2_constant.x = t.t_point.x; y = t.t_point.y } in
  let proof : Accumulator.RecursionProof.Constant.t =
    { neg_a = neg_a_c
    ; b = b_c
    ; c = c_c
    ; pi = pi_c
    ; c_fp12 = t.c
    ; c_inv = t.c_inv
    ; shift_power = t.shift_power
    }
  in
  let state : Accumulator.State.Constant.t =
    { t_point = t_c; f = t.f; g_digest = FF.bignum_to_field_const t.g_digest }
  in
  { Accumulator.Constant.proof; state }

(** Get the current Miller loop accumulator. *)
let get_f (t : t) : Fp12.t = t.f

(** Get the precomputed g values (Fp12 line evaluations). *)
let get_g_values (t : t) : Fp12.t array = t.g_values

(** Get a specific g value by index. *)
let get_g (t : t) (i : int) : Fp12.t = t.g_values.(i)

(** Get alpha_beta from the VK. *)
let get_alpha_beta (t : t) : Fp12.t = t.vk.alpha_beta

(** Get w27 from the VK. *)
let get_w27 (t : t) : Fp12.t = t.vk.w27

(** Get w27^2 (computed). *)
let get_w27_square (t : t) : Fp12.t = Fp12.mul (get_w27 t) (get_w27 t)

(** Compute the out-of-circuit Poseidon hash of an Fp12 value.
    Uses Random_oracle which wraps the same sponge params as the
    in-circuit Poseidon (Kimchi_pasta_basic.poseidon_params_fp). *)
let hash_fp12_out_of_circuit (x : Fp12.t) : Kimchi_pasta.Pasta.Fp.t =
  let module FF = Snarky_foreign_field.Foreign_field in
  let to_fp bi = FF.bignum_to_field_const bi in
  let fp2_fields ((c0, c1) : Fp2.t) = [| to_fp c0; to_fp c1 |] in
  let fp6_fields ((c0, c1, c2) : Fp6.t) =
    Array.concat [ fp2_fields c0; fp2_fields c1; fp2_fields c2 ]
  in
  let c0, c1 = x in
  let fields = Array.concat [ fp6_fields c0; fp6_fields c1 ] in
  Random_oracle.hash fields

(** Get the line hashes array (65 elements).
    Each element is the Poseidon hash of the corresponding g value.
    The last element (index 64) is the Frobenius correction g. *)
let get_line_hashes (t : t) : Kimchi_pasta.Pasta.Fp.t array =
  if Array.length t.line_hashes > 0 then
    Array.map t.line_hashes ~f:(fun bi ->
        Snarky_foreign_field.Foreign_field.bignum_to_field_const bi )
  else
    let n = Array.length Bn254_params.ate_loop_count in
    Array.init n ~f:(fun i ->
        if i < Array.length t.g_values then
          hash_fp12_out_of_circuit t.g_values.(i)
        else Kimchi_pasta.Pasta.Fp.zero )

(** Get the g_chunk (Fp12 values) and lhs/rhs hashes for a specific
    f-update circuit's ArrayListHasher.open call.
    Returns (lhs_hashes, g_chunk, rhs_hashes). *)
let get_g_digest_opening (t : t) ~(g_start : int) ~(n_iters : int) :
    Kimchi_pasta.Pasta.Fp.t array * Fp12.t array * Kimchi_pasta.Pasta.Fp.t array
    =
  let all_hashes = get_line_hashes t in
  let n = Array.length all_hashes in
  let lhs = Array.sub all_hashes ~pos:0 ~len:g_start in
  let g_chunk = Array.sub t.g_values ~pos:g_start ~len:n_iters in
  let rhs_start = g_start + n_iters in
  let rhs = Array.sub all_hashes ~pos:rhs_start ~len:(n - rhs_start) in
  (lhs, g_chunk, rhs)

(** Get all B-lines as a flat array in nori's order: for each ate iteration,
    the double line followed by the add line (if bit != 0), then the 2
    frobenius b_lines at the end.
    Matches nori's Provable.Array(G2Line, 91) private input, where
    LineParser.frobenius_lines returns the last 2 elements. *)
let get_all_b_lines (t : t) : Line.t array =
  let ate = Bn254_params.ate_loop_count in
  let lines = Queue.create () in
  for i = 1 to Array.length ate - 1 do
    let iter = t.iterations.(i - 1) in
    Queue.enqueue lines iter.double_line ;
    if ate.(i) <> 0 then Queue.enqueue lines (Option.value_exn iter.add_line)
  done ;
  (* Append frobenius b_lines (matches nori's slice(-2)) *)
  Array.iter t.frobenius_b_lines ~f:(Queue.enqueue lines) ;
  Queue.to_array lines

(** Get c_inv^p (Frobenius of c_inv). *)
let get_c_inv_frob_p (t : t) : Fp12.t = Fp12.frobenius_pow_p t.c_inv

(** Get c^(p^2) (Frobenius squared of c). *)
let get_c_frob_p2 (t : t) : Fp12.t = Fp12.frobenius_pow_p_squared t.c

(** Get c_inv^(p^3) (Frobenius cubed of c_inv). *)
let get_c_inv_frob_p3 (t : t) : Fp12.t = Fp12.frobenius_pow_p_cubed t.c_inv

(** Compute a doubling line coefficient from a G2 point.
    Returns (lambda, neg_mu) and the doubled point. *)
let compute_double_line (pt : G2.t) : Line.t * G2.t =
  let x_sq = Fp2.square pt.x in
  let three_x_sq = Fp2.add (Fp2.add x_sq x_sq) x_sq in
  let two_y = Fp2.add pt.y pt.y in
  let lambda = Fp2.mul three_x_sq (Fp2.inverse two_y) in
  let lambda_sq = Fp2.square lambda in
  let two_x = Fp2.add pt.x pt.x in
  let x3 = Fp2.sub lambda_sq two_x in
  let y3 = Fp2.sub (Fp2.mul lambda (Fp2.sub pt.x x3)) pt.y in
  let neg_mu = Fp2.sub (Fp2.mul lambda pt.x) pt.y in
  ({ Line.lambda; neg_mu }, { G2.x = x3; y = y3 })

(** Compute an addition line coefficient from two G2 points. *)
let compute_add_line (p1 : G2.t) (p2 : G2.t) : Line.t * G2.t =
  let dx = Fp2.sub p2.x p1.x in
  let dy = Fp2.sub p2.y p1.y in
  let lambda = Fp2.mul dy (Fp2.inverse dx) in
  let lambda_sq = Fp2.square lambda in
  let x3 = Fp2.sub (Fp2.sub lambda_sq p1.x) p2.x in
  let y3 = Fp2.sub (Fp2.mul lambda (Fp2.sub p1.x x3)) p1.y in
  let neg_mu = Fp2.sub (Fp2.mul lambda p1.x) p1.y in
  ({ Line.lambda; neg_mu }, { G2.x = x3; y = y3 })

(** Evaluate a line at a G1 point using the affine cache.
    Produces an Fp12 value with sparse structure. *)
let evaluate_line (line : Line.t) ~(x_over_y : BI.t) ~(y_inv : BI.t) : Fp12.t =
  let h0 = Fp2.mul_by_fp line.lambda x_over_y in
  let h1 = Fp2.mul_by_fp line.neg_mu y_inv in
  (* Sparse Fp12 matching nori's psi(): c0=(1,0,0), c1=(h0,h1,0) *)
  let c0 : Fp6.t = (Fp2.one, Fp2.zero, Fp2.zero) in
  let c1 : Fp6.t = (h0, h1, Fp2.zero) in
  (c0, c1)

(** Run the full Miller loop computation out-of-circuit.
    Computes all intermediate Fp12 values and stores them. *)
let compute_miller_loop (t : t) : unit =
  let neg_a = get_neg_a t in
  let x_over_y, y_inv = compute_affine_cache neg_a in
  let b = G2.of_proof_json t.vk.beta in
  let ate = Bn254_params.ate_loop_count in
  let n = Array.length ate in
  (* Initialize: T = B, f = 1 *)
  let current_t = ref b in
  let f = ref Fp12.one in
  let num_iters = n - 1 in
  let g_values = Array.create ~len:num_iters Fp12.one in
  (* Delta and gamma G2 points from VK, tracked in parallel with B *)
  let delta = G2.of_proof_json t.vk.delta in
  let gamma = G2.of_proof_json t.vk.gamma in
  let c_g1 = get_c t in
  let pi_g1 = get_pi t in
  let c_xoy, c_yinv = compute_affine_cache c_g1 in
  let pi_xoy, pi_yinv = compute_affine_cache pi_g1 in
  let current_delta = ref delta in
  let current_gamma = ref gamma in
  let neg_delta = { G2.x = delta.x; y = Fp2.neg delta.y } in
  let neg_gamma = { G2.x = gamma.x; y = Fp2.neg gamma.y } in
  let dummy_line = { Line.lambda = Fp2.zero; neg_mu = Fp2.zero } in
  let dummy_iter =
    { f_before = Fp12.one
    ; double_line = dummy_line
    ; add_line = None
    ; f_after = Fp12.one
    ; delta_double_line = dummy_line
    ; delta_add_line = None
    ; gamma_double_line = dummy_line
    ; gamma_add_line = None
    }
  in
  let iterations = Array.create ~len:num_iters dummy_iter in
  for i = 1 to num_iters do
    let f_before = !f in
    (* B lines *)
    let double_line, new_t = compute_double_line !current_t in
    current_t := new_t ;
    (* Delta and gamma lines (parallel trajectory) *)
    let delta_dl, new_delta = compute_double_line !current_delta in
    current_delta := new_delta ;
    let gamma_dl, new_gamma = compute_double_line !current_gamma in
    current_gamma := new_gamma ;
    f := Fp12.square !f ;
    let line_eval = evaluate_line double_line ~x_over_y ~y_inv in
    f := Fp12.mul !f line_eval ;
    let bit = ate.(i) in
    let add_line_opt, delta_add_opt, gamma_add_opt =
      if bit = 1 then (
        let add_line, new_t = compute_add_line !current_t b in
        current_t := new_t ;
        let add_eval = evaluate_line add_line ~x_over_y ~y_inv in
        f := Fp12.mul !f add_eval ;
        let d_add, nd = compute_add_line !current_delta delta in
        current_delta := nd ;
        let g_add, ng = compute_add_line !current_gamma gamma in
        current_gamma := ng ;
        (Some add_line, Some d_add, Some g_add) )
      else if bit = -1 then (
        let neg_b = { G2.x = b.x; y = Fp2.neg b.y } in
        let add_line, new_t = compute_add_line !current_t neg_b in
        current_t := new_t ;
        let add_eval = evaluate_line add_line ~x_over_y ~y_inv in
        f := Fp12.mul !f add_eval ;
        let d_add, nd = compute_add_line !current_delta neg_delta in
        current_delta := nd ;
        let g_add, ng = compute_add_line !current_gamma neg_gamma in
        current_gamma := ng ;
        (Some add_line, Some d_add, Some g_add) )
      else (None, None, None)
    in
    (* Compute g: product of all line evaluations at all 3 caches *)
    let g_b_double = evaluate_line double_line ~x_over_y ~y_inv in
    let g_d_double = evaluate_line delta_dl ~x_over_y:c_xoy ~y_inv:c_yinv in
    let g_g_double = evaluate_line gamma_dl ~x_over_y:pi_xoy ~y_inv:pi_yinv in
    let g_val = Fp12.mul (Fp12.mul g_b_double g_d_double) g_g_double in
    let g_val =
      match (add_line_opt, delta_add_opt, gamma_add_opt) with
      | Some al, Some dal, Some gal ->
          let g_b_add = evaluate_line al ~x_over_y ~y_inv in
          let g_d_add = evaluate_line dal ~x_over_y:c_xoy ~y_inv:c_yinv in
          let g_g_add = evaluate_line gal ~x_over_y:pi_xoy ~y_inv:pi_yinv in
          Fp12.mul g_val (Fp12.mul (Fp12.mul g_b_add g_d_add) g_g_add)
      | _ ->
          g_val
    in
    g_values.(i - 1) <- g_val ;
    iterations.(i - 1) <-
      { f_before
      ; double_line
      ; add_line = add_line_opt
      ; f_after = !f
      ; delta_double_line = delta_dl
      ; delta_add_line = delta_add_opt
      ; gamma_double_line = gamma_dl
      ; gamma_add_line = gamma_add_opt
      }
  done ;
  t.f <- !f ;
  t.t_point <- !current_t ;
  t.g_values <- g_values ;
  t.iterations <- iterations ;
  (* Compute Frobenius correction line evaluations for zkp6.
     Each of the 3 G2 trajectories (B, delta, gamma) gets Frobenius-mapped. *)
  let piB = G2.frobenius b in
  let pi2B = G2.negative_frobenius piB in
  let piB_line, t_after_piB = compute_add_line !current_t piB in
  let piB_eval = evaluate_line piB_line ~x_over_y ~y_inv in
  let pi2B_line, _t_after_pi2B = compute_add_line t_after_piB pi2B in
  let pi2B_eval = evaluate_line pi2B_line ~x_over_y ~y_inv in
  (* Delta Frobenius lines *)
  let pi_delta = G2.frobenius delta in
  let pi2_delta = G2.negative_frobenius pi_delta in
  let pi_delta_line, d_after = compute_add_line !current_delta pi_delta in
  let pi2_delta_line, _ = compute_add_line d_after pi2_delta in
  (* Gamma Frobenius lines *)
  let pi_gamma = G2.frobenius gamma in
  let pi2_gamma = G2.negative_frobenius pi_gamma in
  let pi_gamma_line, g_after = compute_add_line !current_gamma pi_gamma in
  let pi2_gamma_line, _ = compute_add_line g_after pi2_gamma in
  t.frobenius_lines <- [| piB_eval; pi2B_eval |] ;
  t.frobenius_b_lines <- [| piB_line; pi2B_line |] ;
  t.frobenius_delta_lines <- [| pi_delta_line; pi2_delta_line |] ;
  t.frobenius_gamma_lines <- [| pi_gamma_line; pi2_gamma_line |]

(** Get the line evaluation product (g value) at a specific ate loop iteration. *)
let get_g_at_iteration (t : t) (i : int) : Fp12.t =
  if Array.length t.g_values = 0 then Fp12.one (* Not computed yet *)
  else if i < Array.length t.g_values then t.g_values.(i)
  else t.f
(* Final value *)

(** Get per-iteration witness data. *)
let get_iteration (t : t) (i : int) : iteration_data = t.iterations.(i)

(** Create a witness tracker from parsed proof, VK, and auxiliary witness.
    Immediately computes the full Miller loop. *)
let create ~(proof : Proof_json.proof) ~(vk : Proof_json.vk)
    ~(aux : Proof_json.aux_witness) : t =
  let c = aux.c in
  let c_inv = Fp12.inverse c in
  let t =
    { proof
    ; vk
    ; c
    ; c_inv
    ; shift_power = aux.shift_power
    ; t_point = { G2.x = Fp2.zero; y = Fp2.zero }
    ; f = Fp12.one
    ; g_digest = BI.zero
    ; g_values = [||]
    ; iterations = [||]
    ; frobenius_b_lines = [||]
    ; frobenius_delta_lines = [||]
    ; frobenius_gamma_lines = [||]
    ; line_hashes = [||]
    ; frobenius_lines = [||]
    }
  in
  compute_miller_loop t ; t
