//! SPEC-024 REQ-142 / TEST-018 — native ↔ NIF verdict-serialization parity.
//!
//! Runs the cbcl-core REQ-142 corpus through the cbcl-erl NIF's `*_pure` helper
//! and asserts the serialized verdict bytes are byte-identical to the in-crate
//! native path, per vector, and that the NIF-produced outputs reproduce the
//! pinned native corpus digest. The NIF is a native compile, so this proves the
//! binding + serialization boundary (the wasm32 leg proves the cross-target
//! compile). It targets the env-free `run_verify_vector_pure` — the
//! `#[rustler::nif]` wrapper cannot run under `cargo test` (`enif_*` aborts
//! outside a BEAM host; see `tests/integration.rs`).
//!
//! Only built under `--features mls-ds-proof`.
#![cfg(feature = "mls-ds-proof")]

use cbcl_core::mls_ds::corpus::{corpus_input_vectors, labelled_vectors, NATIVE_CORPUS_DIGEST_HEX};
use cbcl_core::mls_ds::{digest_verdicts_hex, run_verify_vector};
use cbcl_erl::run_verify_vector_pure;

#[test]
fn nif_pure_matches_native_bytes_per_vector() {
    let vectors = labelled_vectors();
    assert!(
        vectors.len() >= 10,
        "corpus too small: {} vectors",
        vectors.len()
    );
    for (label, input) in &vectors {
        let native = run_verify_vector(input);
        let via_nif = run_verify_vector_pure(input);
        assert_eq!(
            native, via_nif,
            "vector {label}: NIF-boundary verdict bytes differ from native \
             (native={} bytes, nif={} bytes)",
            native.len(),
            via_nif.len()
        );
    }
}

#[test]
fn nif_outputs_reproduce_the_pinned_corpus_digest() {
    // Fingerprint the bytes produced THROUGH the NIF boundary and compare to
    // the single pinned baseline shared with the native and wasm32 tests.
    let outputs: Vec<Vec<u8>> = corpus_input_vectors()
        .iter()
        .map(|v| run_verify_vector_pure(v))
        .collect();
    let digest = digest_verdicts_hex(&outputs);
    assert_eq!(
        digest, NATIVE_CORPUS_DIGEST_HEX,
        "NIF corpus digest diverged from the pinned native baseline"
    );
}
