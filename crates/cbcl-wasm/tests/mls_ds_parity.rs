//! SPEC-024 REQ-142 / TEST-018 — native ↔ wasm32 verdict-serialization parity.
//!
//! The MEANINGFUL cross-target leg: the SAME `run_verify_vector` compiled to
//! wasm32 (32-bit, dlmalloc/std, ed25519-dalek built for wasm) must emit
//! byte-identical canonical verdicts to the native baseline. Each corpus vector
//! is run through the wasm build; the whole-corpus digest is compared to the
//! single pinned baseline `corpus::NATIVE_CORPUS_DIGEST_HEX` — a match is proof
//! of per-vector byte-identity (any 1-byte drift changes the digest).
//!
//! Runs two ways from ONE source:
//!   - native:  `cargo test -p cbcl-wasm --features mls-ds-proof` (`#[test]`)
//!   - wasm32:  `wasm-pack test --node -- --features mls-ds-proof`
//!              (`#[wasm_bindgen_test]`, executed in Node)
//!
//! Only built under `--features mls-ds-proof`.
#![cfg(feature = "mls-ds-proof")]

use cbcl_core::mls_ds::corpus::{corpus_input_vectors, NATIVE_CORPUS_DIGEST_HEX};
use cbcl_core::mls_ds::digest_verdicts_hex;
use cbcl_wasm::{mls_ds_corpus_digest_hex, mls_ds_run_verify_vector_bytes};

// wasm-bindgen-test runs in Node by default (the `--node` flag on
// `wasm-pack test` selects the Node runner); no `_configure!` is needed.
#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::wasm_bindgen_test;

#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
#[cfg_attr(not(target_arch = "wasm32"), test)]
fn corpus_reproduces_pinned_native_digest() {
    let vectors = corpus_input_vectors();
    assert!(vectors.len() >= 10, "corpus too small: {}", vectors.len());

    // Run every vector through THIS target's runner (exercises the full
    // recognize → verify → serialize path per vector), then fingerprint.
    let outputs: Vec<Vec<u8>> = vectors
        .iter()
        .map(|v| mls_ds_run_verify_vector_bytes(v))
        .collect();
    for (i, out) in outputs.iter().enumerate() {
        assert!(!out.is_empty(), "vector {i} produced empty verdict");
    }

    let digest = digest_verdicts_hex(&outputs);
    assert_eq!(
        digest, NATIVE_CORPUS_DIGEST_HEX,
        "this target's corpus digest diverged from the pinned native baseline"
    );

    // The crate's convenience digest fn agrees too.
    assert_eq!(mls_ds_corpus_digest_hex(), NATIVE_CORPUS_DIGEST_HEX);
}
