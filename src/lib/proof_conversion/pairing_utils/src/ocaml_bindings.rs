//! OCaml FFI bindings for pairing-utils.
//!
//! Uses ocaml-sys for proper OCaml value access, but avoids #[ocaml::func]
//! which conflicts with the kimchi_stubs library's runtime initialization.

use ark_bn254::{Bn254, Fq, Fq2, Fq6, Fq12, G1Affine, G2Affine};
use ark_ec::pairing::Pairing;
use std::str::FromStr;

use crate::kzg::compute_aux_witness as rust_compute_aux_witness;
use crate::serialize::serialize_fq12;

fn parse_fq12(input: &str) -> Fq12 {
    let parts: Vec<&str> = input.split('|').collect();
    assert_eq!(
        parts.len(),
        12,
        "Expected 12 pipe-delimited fields for Fq12, got {}",
        parts.len()
    );
    let fq = |i: usize| -> Fq { Fq::from_str(parts[i]).unwrap() };
    let g0 = Fq2::new(fq(0), fq(1));
    let g1 = Fq2::new(fq(2), fq(3));
    let g2 = Fq2::new(fq(4), fq(5));
    let h0 = Fq2::new(fq(6), fq(7));
    let h1 = Fq2::new(fq(8), fq(9));
    let h2 = Fq2::new(fq(10), fq(11));
    Fq12::new(Fq6::new(g0, g1, g2), Fq6::new(h0, h1, h2))
}

fn format_fq12(x: Fq12) -> String {
    let s = serialize_fq12(x);
    format!(
        "{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}",
        s.g00, s.g01, s.g10, s.g11, s.g20, s.g21, s.h00, s.h01, s.h10, s.h11, s.h20, s.h21,
    )
}

/// Read an OCaml string value into a Rust &str.
unsafe fn read_ocaml_string(v: ocaml::sys::Value) -> &'static str {
    let ptr = ocaml::sys::string_val(v) as *const u8;
    let len = ocaml::sys::caml_string_length(v);
    let bytes = std::slice::from_raw_parts(ptr, len);
    std::str::from_utf8(bytes).unwrap()
}

/// Allocate an OCaml string from a Rust String.
unsafe fn alloc_ocaml_string(s: &str) -> ocaml::sys::Value {
    let v = ocaml::sys::caml_alloc_string(s.len());
    let dst = ocaml::sys::bp_val(v) as *mut u8;
    std::ptr::copy_nonoverlapping(s.as_ptr(), dst, s.len());
    v
}

/// Compute aux witness from Miller loop output.
/// OCaml: external compute_aux_witness_raw : string -> string
#[no_mangle]
pub unsafe extern "C" fn caml_pairing_utils_compute_aux_witness(
    v_input: ocaml::sys::Value,
) -> ocaml::sys::Value {
    let input_str = read_ocaml_string(v_input);
    let mlo = parse_fq12(input_str);
    let (shift_power, c) = rust_compute_aux_witness(mlo);
    let result = format!("{}|{}", shift_power, format_fq12(c));
    alloc_ocaml_string(&result)
}

/// Compute Groth16 aux witness from proof/VK points.
/// Computes MLO = multi_miller_loop([-A, PI, C], [B, gamma, delta]) * alpha_beta,
/// then compute_aux_witness(MLO).
///
/// Input: pipe-delimited string of 18 fields:
///   negA_x|negA_y|B_x_c0|B_x_c1|B_y_c0|B_y_c1|C_x|C_y|PI_x|PI_y|
///   gamma_x_c0|gamma_x_c1|gamma_y_c0|gamma_y_c1|
///   delta_x_c0|delta_x_c1|delta_y_c0|delta_y_c1
/// Plus alpha_beta as 12 Fp12 fields (total 30 fields).
///
/// Returns: "shift_power|c_g00|c_g01|...|c_h21" (13 fields).
#[no_mangle]
pub unsafe extern "C" fn caml_pairing_utils_groth16_aux_witness(
    v_input: ocaml::sys::Value,
) -> ocaml::sys::Value {
    let input_str = read_ocaml_string(v_input);
    let parts: Vec<&str> = input_str.split('|').collect();
    assert_eq!(parts.len(), 30, "Expected 30 pipe-delimited fields, got {}", parts.len());
    let fq = |i: usize| -> Fq { Fq::from_str(parts[i]).unwrap() };

    // Parse proof points
    let neg_a = G1Affine::new(fq(0), fq(1));
    let b = G2Affine::new(Fq2::new(fq(2), fq(3)), Fq2::new(fq(4), fq(5)));
    let c = G1Affine::new(fq(6), fq(7));
    let pi = G1Affine::new(fq(8), fq(9));
    let gamma = G2Affine::new(Fq2::new(fq(10), fq(11)), Fq2::new(fq(12), fq(13)));
    let delta = G2Affine::new(Fq2::new(fq(14), fq(15)), Fq2::new(fq(16), fq(17)));

    // Parse alpha_beta Fp12
    let alpha_beta = parse_fq12(&parts[18..30].join("|"));

    // Compute MLO: multi_miller_loop([-A, PI, C], [B, gamma, delta]) * alpha_beta
    // negA is already -A, so pass directly as first G1 element.
    let mlo_raw = Bn254::multi_miller_loop(&[neg_a, pi, c], &[b, gamma, delta]);
    let mlo = mlo_raw.0 * alpha_beta;

    let (shift_power, c_root) = rust_compute_aux_witness(mlo);
    let result = format!("{}|{}", shift_power, format_fq12(c_root));
    alloc_ocaml_string(&result)
}

/// Compute alpha*beta pairing from VK points.
/// OCaml: external make_alpha_beta_raw : string -> string
#[no_mangle]
pub unsafe extern "C" fn caml_pairing_utils_make_alpha_beta(
    v_input: ocaml::sys::Value,
) -> ocaml::sys::Value {
    let input_str = read_ocaml_string(v_input);
    let parts: Vec<&str> = input_str.split('|').collect();
    assert_eq!(parts.len(), 6);
    let fq = |i: usize| -> Fq { Fq::from_str(parts[i]).unwrap() };

    let alpha = G1Affine::new(fq(0), fq(1));
    let beta = G2Affine::new(Fq2::new(fq(2), fq(3)), Fq2::new(fq(4), fq(5)));

    let result_fq12 = Bn254::multi_miller_loop(&[alpha], &[beta]).0;
    let result = format_fq12(result_fq12);
    alloc_ocaml_string(&result)
}
