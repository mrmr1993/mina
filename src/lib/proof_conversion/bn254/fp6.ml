(** Fp6 = Fp2[v] / (v^3 - xi) arithmetic over BN254.

    Elements are triples (c0, c1, c2) representing c0 + c1*v + c2*v^2
    where v^3 = xi and xi = 9 + u (the Fp2 non-residue). *)

module Circuit = struct
  type t = { c0 : Fp2.Circuit.t; c1 : Fp2.Circuit.t; c2 : Fp2.Circuit.t }
end

let mul_by_non_residue (x : Fp2.Circuit.t) : Fp2.Circuit.t =
  let xi = Fp2.of_constant Bn254_params.fp2_non_residue in
  Fp2.mul x xi

let add (a : Circuit.t) (b : Circuit.t) : Circuit.t =
  { c0 = Fp2.add a.c0 b.c0
  ; c1 = Fp2.add a.c1 b.c1
  ; c2 = Fp2.add a.c2 b.c2
  }

let sub (a : Circuit.t) (b : Circuit.t) : Circuit.t =
  { c0 = Fp2.sub a.c0 b.c0
  ; c1 = Fp2.sub a.c1 b.c1
  ; c2 = Fp2.sub a.c2 b.c2
  }

let neg (a : Circuit.t) : Circuit.t =
  { c0 = Fp2.neg a.c0; c1 = Fp2.neg a.c1; c2 = Fp2.neg a.c2 }

let mul (a : Circuit.t) (b : Circuit.t) : Circuit.t =
  let a0b0 = Fp2.mul a.c0 b.c0 in
  let a0b1 = Fp2.mul a.c0 b.c1 in
  let a0b2 = Fp2.mul a.c0 b.c2 in
  let a1b0 = Fp2.mul a.c1 b.c0 in
  let a1b1 = Fp2.mul a.c1 b.c1 in
  let a1b2 = Fp2.mul a.c1 b.c2 in
  let a2b0 = Fp2.mul a.c2 b.c0 in
  let a2b1 = Fp2.mul a.c2 b.c1 in
  let a2b2 = Fp2.mul a.c2 b.c2 in
  let c0 = Fp2.add a0b0 (mul_by_non_residue (Fp2.add a1b2 a2b1)) in
  let c1 = Fp2.add (Fp2.add a0b1 a1b0) (mul_by_non_residue a2b2) in
  let c2 = Fp2.add (Fp2.add a0b2 a1b1) a2b0 in
  { c0; c1; c2 }

let mul_by_01 (a : Circuit.t) (b0 : Fp2.Circuit.t) (b1 : Fp2.Circuit.t) :
    Circuit.t =
  let a0b0 = Fp2.mul a.c0 b0 in
  let a1b1 = Fp2.mul a.c1 b1 in
  let c0 = Fp2.add a0b0 (mul_by_non_residue (Fp2.mul a.c2 b1)) in
  let c1 =
    Fp2.sub
      (Fp2.mul (Fp2.add a.c0 a.c1) (Fp2.add b0 b1))
      (Fp2.add a0b0 a1b1)
  in
  let c2 = Fp2.add (Fp2.mul a.c2 b0) a1b1 in
  { c0; c1; c2 }
