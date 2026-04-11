//! OCaml FFI bindings for pairing-utils.
//!
//! Uses ocaml-sys for proper OCaml value access, but avoids #[ocaml::func]
//! which conflicts with the kimchi_stubs library's runtime initialization.

use ark_bn254::{Bn254, Fq, Fq2, Fq6, Fq12, G1Affine, G2Affine};
use ark_ec::pairing::Pairing;
use std::str::FromStr;

use crate::constants::{E, RESIDUE};
use crate::eth_root::eth_root;
use crate::serialize::serialize_fq12;
use crate::tonelli_shanks::TS;
use crate::utils::exp;
use ark_ff::{Field, One, Zero};

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
    let (shift_power, c) = crate::kzg::compute_aux_witness(mlo);
    let result = format!("{}|{}", shift_power, format_fq12(c));
    alloc_ocaml_string(&result)
}

/// Compute aux witness using a provided w27 (instead of sampling).
fn compute_aux_witness_with_w27(x: Fq12, w27: Fq12) -> (u8, Fq12) {
    let mut eth_residue = Fq12::zero();
    let mut shift_power = 0u8;

    for i in 0..3u8 {
        let tmp_shift = w27.pow(&[i as u64, 0, 0, 0]);
        let tmp_eth = x * tmp_shift;

        if exp(tmp_eth, &RESIDUE) == Fq12::one() {
            shift_power = i;
            eth_residue = tmp_eth;
            break;
        }
    }

    let ts = TS { w: w27 };
    let root = eth_root(eth_residue, ts);
    assert_eq!(exp(root, &E), eth_residue);

    (shift_power, root)
}

/// Compute Groth16 aux witness from proof/VK points + w27.
/// Computes MLO = multi_miller_loop([-A, PI, C], [B, gamma, delta]) * alpha_beta,
/// then compute_aux_witness with the provided w27.
///
/// Input: pipe-delimited string of 42 fields:
///   negA(2) | B(4) | C(2) | PI(2) | gamma(4) | delta(4) | alpha_beta(12) | w27(12)
///
/// Returns: "shift_power|c_g00|c_g01|...|c_h21" (13 fields).
#[no_mangle]
pub unsafe extern "C" fn caml_pairing_utils_groth16_aux_witness(
    v_input: ocaml::sys::Value,
) -> ocaml::sys::Value {
    let input_str = read_ocaml_string(v_input);
    let parts: Vec<&str> = input_str.split('|').collect();
    assert_eq!(parts.len(), 42, "Expected 42 pipe-delimited fields, got {}", parts.len());
    let fq = |i: usize| -> Fq { Fq::from_str(parts[i]).unwrap() };

    // Parse proof points
    let neg_a = G1Affine::new(fq(0), fq(1));
    let b = G2Affine::new(Fq2::new(fq(2), fq(3)), Fq2::new(fq(4), fq(5)));
    let c = G1Affine::new(fq(6), fq(7));
    let pi = G1Affine::new(fq(8), fq(9));
    let gamma = G2Affine::new(Fq2::new(fq(10), fq(11)), Fq2::new(fq(12), fq(13)));
    let delta = G2Affine::new(Fq2::new(fq(14), fq(15)), Fq2::new(fq(16), fq(17)));

    // Parse alpha_beta Fp12 (fields 18-29)
    let alpha_beta = parse_fq12(&parts[18..30].join("|"));

    // Parse w27 Fp12 (fields 30-41)
    let w27 = parse_fq12(&parts[30..42].join("|"));

    // Compute MLO: multi_miller_loop([-A, PI, C], [B, gamma, delta]) * alpha_beta
    let mlo_raw = Bn254::multi_miller_loop(&[neg_a, pi, c], &[b, gamma, delta]);
    let mlo = mlo_raw.0 * alpha_beta;

    let (shift_power, c_root) = compute_aux_witness_with_w27(mlo, w27);
    let result = format!("{}|{}", shift_power, format_fq12(c_root));
    alloc_ocaml_string(&result)
}

/// Compute aux witness from MLO + w27 (both provided as Fp12).
/// Input: 24 pipe-delimited fields (MLO 12 + w27 12).
/// Returns: "shift_power|c_g00|...|c_h21" (13 fields).
#[no_mangle]
pub unsafe extern "C" fn caml_pairing_utils_aux_witness_with_w27(
    v_input: ocaml::sys::Value,
) -> ocaml::sys::Value {
    let input_str = read_ocaml_string(v_input);
    let parts: Vec<&str> = input_str.split('|').collect();
    assert_eq!(parts.len(), 24, "Expected 24 pipe-delimited fields (MLO+w27), got {}", parts.len());

    let mlo = parse_fq12(&parts[0..12].join("|"));
    let w27 = parse_fq12(&parts[12..24].join("|"));

    let (shift_power, c_root) = compute_aux_witness_with_w27(mlo, w27);
    let result = format!("{}|{}", shift_power, format_fq12(c_root));
    alloc_ocaml_string(&result)
}

/// Compute KZG pairing MLO from A and -B G1 points.
/// MLO = multi_miller_loop([A, -B], [g2, tau]) where g2/tau are the BN254
/// SRS points used by SP1's PLONK verifier.
///
/// Input: 4 pipe-delimited fields: a_x|a_y|neg_b_x|neg_b_y
/// Returns: 12 pipe-delimited fields (Fp12 MLO).
#[no_mangle]
pub unsafe extern "C" fn caml_pairing_utils_compute_kzg_mlo(
    v_input: ocaml::sys::Value,
) -> ocaml::sys::Value {
    let input_str = read_ocaml_string(v_input);
    let parts: Vec<&str> = input_str.split('|').collect();
    assert_eq!(parts.len(), 4, "Expected 4 pipe-delimited fields for KZG MLO");
    let fq = |i: usize| -> Fq { Fq::from_str(parts[i]).unwrap() };

    let a = G1Affine::new(fq(0), fq(1));
    let neg_b = G1Affine::new(fq(2), fq(3));

    // SRS G2 points (fixed for SP1 PLONK verifier)
    use ark_ff::MontFp;
    let g2 = G2Affine::new(
        Fq2::new(
            MontFp!("10857046999023057135944570762232829481370756359578518086990519993285655852781"),
            MontFp!("11559732032986387107991004021392285783925812861821192530917403151452391805634"),
        ),
        Fq2::new(
            MontFp!("8495653923123431417604973247489272438418190587263600148770280649306958101930"),
            MontFp!("4082367875863433681332203403145435568316851327593401208105741076214120093531"),
        ),
    );
    let tau = G2Affine::new(
        Fq2::new(
            MontFp!("19089565590083334368588890253123139704298730990782503769911324779715431555531"),
            MontFp!("15805639136721018565402881920352193254830339253282065586954346329754995870280"),
        ),
        Fq2::new(
            MontFp!("6779728121489434657638426458390319301070371227460768374343986326751507916979"),
            MontFp!("9779648407879205346559610309258181044130619080926897934572699915909528404984"),
        ),
    );

    // MLO = multi_miller_loop([A, -B], [g2, tau])
    let mlo = Bn254::multi_miller_loop(&[a, neg_b], &[g2, tau]).0;
    let result = format_fq12(mlo);
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
