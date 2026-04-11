//! OCaml FFI bindings for pairing-utils.
//!
//! Exposes `compute_aux_witness` and `make_alpha_beta` to OCaml via
//! the `ocaml` crate's `#[ocaml::func]` attribute.
//!
//! Field elements are marshalled as decimal strings to avoid complex
//! type conversions — matching the pattern used in kimchi_bindings.

use ark_bn254::{Bn254, Fq, Fq2, Fq6, Fq12, G1Affine, G2Affine};
use ark_ec::pairing::Pairing;
use std::str::FromStr;

use crate::kzg::compute_aux_witness as rust_compute_aux_witness;
use crate::serialize::serialize_fq12;

/// Parse 12 decimal strings into an Fq12 element.
/// Order: g00, g01, g10, g11, g20, g21, h00, h01, h10, h11, h20, h21
fn strings_to_fq12(fields: &[String]) -> Fq12 {
    assert_eq!(fields.len(), 12, "Expected 12 field strings for Fq12");
    let fq = |i: usize| -> Fq { Fq::from_str(&fields[i]).unwrap() };
    let g0 = Fq2::new(fq(0), fq(1));
    let g1 = Fq2::new(fq(2), fq(3));
    let g2 = Fq2::new(fq(4), fq(5));
    let h0 = Fq2::new(fq(6), fq(7));
    let h1 = Fq2::new(fq(8), fq(9));
    let h2 = Fq2::new(fq(10), fq(11));
    Fq12::new(Fq6::new(g0, g1, g2), Fq6::new(h0, h1, h2))
}

/// Serialize an Fq12 element to 12 decimal strings.
fn fq12_to_strings(x: Fq12) -> Vec<String> {
    let s = serialize_fq12(x);
    vec![
        s.g00, s.g01, s.g10, s.g11, s.g20, s.g21,
        s.h00, s.h01, s.h10, s.h11, s.h20, s.h21,
    ]
}

/// Compute auxiliary witness from a Miller loop output (Fp12).
///
/// Input: OCaml list of 12 decimal strings representing the Fp12 element.
/// Returns: (shift_power, list of 12 decimal strings for c).
#[ocaml::func]
pub fn caml_pairing_utils_compute_aux_witness(
    fields: Vec<String>,
) -> (ocaml::Int, Vec<String>) {
    let mlo = strings_to_fq12(&fields);
    let (shift_power, c) = rust_compute_aux_witness(mlo);
    (shift_power as ocaml::Int, fq12_to_strings(c))
}

/// Compute alpha*beta pairing from VK points.
///
/// Input: list of 6 decimal strings [alpha_x, alpha_y, beta_x_c0, beta_x_c1, beta_y_c0, beta_y_c1].
/// Returns: list of 12 decimal strings for the Fp12 result.
#[ocaml::func]
pub fn caml_pairing_utils_make_alpha_beta(
    fields: Vec<String>,
) -> Vec<String> {
    assert_eq!(fields.len(), 6, "Expected 6 field strings for make_alpha_beta");
    let fq = |i: usize| -> Fq { Fq::from_str(&fields[i]).unwrap() };

    let alpha = G1Affine::new(fq(0), fq(1));
    let beta = G2Affine::new(Fq2::new(fq(2), fq(3)), Fq2::new(fq(4), fq(5)));

    let result = Bn254::multi_miller_loop(&[alpha], &[beta]).0;
    fq12_to_strings(result)
}
