(** Groth16 witness tracker — out-of-circuit computation.

    Pre-computes all intermediate values needed by the 16 recursive
    circuits. Operates on pure bignum arithmetic (no circuit constraints). *)

module BI = Bignum_bigint

let p = Bn254_params.p

(** Out-of-circuit Fp arithmetic. *)
module Fp = struct
  let add a b = BI.((a + b) % p)

  let sub a b = BI.(((a - b) % p + p) % p)

  let mul a b = BI.(a * b % p)

  let inv a =
    match
      Snarky_foreign_field.Foreign_field.bignum_mod_inverse a ~f:p
    with
    | Some v -> v
    | None -> failwith "Fp.inv: inverse does not exist"

  let neg a = sub BI.zero a

  let div a b = mul a (inv b)
end

(** Out-of-circuit Fp2 arithmetic. *)
module Fp2 = struct
  type t = BI.t * BI.t

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

  let one : t = (Fp6.one, Fp6.zero)
end

(** G1 affine point (out-of-circuit). *)
module G1 = struct
  type t = { x : BI.t; y : BI.t }

  let negate p = { x = p.x; y = Fp.neg p.y }

  let of_proof_json (p : Proof_json.G1_constant.t) : t =
    { x = p.x; y = p.y }
end

(** G2 affine point (out-of-circuit). *)
module G2 = struct
  type t = { x : Fp2.t; y : Fp2.t }

  let of_proof_json (p : Proof_json.G2_constant.t) : t =
    { x = p.x; y = p.y }
end

(** Line coefficient from G2 point operations. *)
module Line = struct
  type t = { lambda : Fp2.t; neg_mu : Fp2.t }
end

(** Compute the affine cache for a G1 point. *)
let compute_affine_cache (p : G1.t) :
    BI.t * BI.t =
  let y_inv = Fp.inv p.y in
  let x_over_y = Fp.mul p.x y_inv in
  (x_over_y, y_inv)

(** Per-iteration witness data for ate loop circuits. *)
type iteration_data =
  { f_before : Fp12.t
  ; double_line : Line.t
  ; add_line : Line.t option
  ; f_after : Fp12.t
  }

(** The witness tracker state. *)
type t =
  { proof : Proof_json.proof
  ; vk : Proof_json.vk
  ; mutable f : Fp12.t
  ; mutable g_values : Fp12.t array
  ; mutable iterations : iteration_data array
  ; mutable line_hashes : BI.t array
  }

(** Get the proof's G1 points for circuit witnessing. *)
let get_neg_a (t : t) : G1.t =
  G1.of_proof_json t.proof.neg_a

let get_c (t : t) : G1.t =
  G1.of_proof_json t.proof.c

let get_ic (t : t) (i : int) : G1.t =
  G1.of_proof_json t.vk.ic.(i)

(** Get the number of IC points. *)
let num_ic (t : t) : int = Array.length t.vk.ic

(** Get public inputs. *)
let get_public_input (t : t) (i : int) : BI.t =
  t.proof.public_inputs.(i)

let num_public_inputs (t : t) : int =
  Array.length t.proof.public_inputs

(** Get the current Miller loop accumulator. *)
let get_f (t : t) : Fp12.t = t.f

(** Update the Miller loop accumulator. *)
let update_f (t : t) (f : Fp12.t) : unit = t.f <- f

(** Get the precomputed g values (Fp12 line evaluations). *)
let get_g_values (t : t) : Fp12.t array = t.g_values

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
let evaluate_line (line : Line.t) ~(x_over_y : BI.t)
    ~(y_inv : BI.t) : Fp12.t =
  let c01 = Fp2.mul_by_fp line.lambda x_over_y in
  let c11 = Fp2.mul_by_fp line.neg_mu y_inv in
  (* The sparse Fp12 element: (1, c01, 0, c11, 0, 0) *)
  let c0 : Fp6.t = (Fp2.one, c01, Fp2.zero) in
  let c1 : Fp6.t = (c11, Fp2.zero, Fp2.zero) in
  (c0, c1)

(** Run the full Miller loop computation out-of-circuit.
    Computes all intermediate Fp12 values and stores them. *)
let compute_miller_loop (t : t) : unit =
  let neg_a = get_neg_a t in
  let x_over_y, y_inv = compute_affine_cache neg_a in
  let b = G2.of_proof_json t.vk.beta in  (* Using beta as B placeholder *)
  let ate = Bn254_params.ate_loop_count in
  let n = Stdlib.Array.length ate in
  (* Initialize: T = B, f = 1 *)
  let current_t = ref b in
  let f = ref Fp12.one in
  let num_iters = Stdlib.( - ) n 1 in
  let g_values = Stdlib.Array.make num_iters Fp12.one in
  let dummy_iter =
    { f_before = Fp12.one
    ; double_line = { Line.lambda = Fp2.zero; neg_mu = Fp2.zero }
    ; add_line = None
    ; f_after = Fp12.one
    }
  in
  let iterations = Stdlib.Array.make num_iters dummy_iter in
  for i = 1 to num_iters do
    let f_before = !f in
    let double_line, new_t = compute_double_line !current_t in
    current_t := new_t ;
    f := Fp12.square !f ;
    let line_eval = evaluate_line double_line ~x_over_y ~y_inv in
    f := Fp12.mul !f line_eval ;
    let bit = ate.(i) in
    let add_line_opt =
      if bit = 1 then (
        let add_line, new_t = compute_add_line !current_t b in
        current_t := new_t ;
        let add_eval = evaluate_line add_line ~x_over_y ~y_inv in
        f := Fp12.mul !f add_eval ;
        Some add_line )
      else if bit = Stdlib.( ~- ) 1 then (
        let neg_b = { G2.x = b.x; y = Fp2.neg b.y } in
        let add_line, new_t = compute_add_line !current_t neg_b in
        current_t := new_t ;
        let add_eval = evaluate_line add_line ~x_over_y ~y_inv in
        f := Fp12.mul !f add_eval ;
        Some add_line )
      else None
    in
    g_values.(Stdlib.( - ) i 1) <- !f ;
    iterations.(Stdlib.( - ) i 1) <-
      { f_before; double_line; add_line = add_line_opt; f_after = !f }
  done ;
  t.f <- !f ;
  t.g_values <- g_values ;
  t.iterations <- iterations

(** Get the Fp12 accumulator value at a specific ate loop iteration. *)
let get_f_at_iteration (t : t) (i : int) : Fp12.t =
  if Array.length t.g_values = 0 then
    Fp12.one  (* Not computed yet *)
  else if i < Array.length t.g_values then
    t.g_values.(i)
  else
    t.f  (* Final value *)

(** Get per-iteration witness data. *)
let get_iteration (t : t) (i : int) : iteration_data =
  t.iterations.(i)

(** Create a witness tracker from parsed proof and VK.
    Immediately computes the full Miller loop. *)
let create ~(proof : Proof_json.proof) ~(vk : Proof_json.vk) : t =
  let t =
    { proof; vk; f = Fp12.one; g_values = [||]
    ; iterations = [||]; line_hashes = [||] }
  in
  compute_miller_loop t ;
  t
