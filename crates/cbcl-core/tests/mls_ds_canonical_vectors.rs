//! SPEC-024 mls-ds/v1 — canonical reference vectors (the BYTE AUTHORITY).
//!
//! This integration test computes `cbcl_core::canonical::canonical_encode`
//! (RFC 9804 §6.2, CON-002 `canonical_CBCL`) for a representative set of typed
//! S-expression values covering exactly what the SPEC-024 proof modules hash and
//! sign — bare symbols/keywords/quoted-strings (incl. a `sha256:<hex>`), `Num`
//! (0, small, negative, i64::MAX, i64::MIN), `Bool`, and the real nested tuples
//! (`mls-ds-record-signature-v1`, the 9-field `mls-add-authorization-v1`
//! ADD-AUTH, and a `successor-offer-core-v1`).
//!
//! It emits each as `<label> <lowercase-hex>` to the COMMITTED data file
//! `crates/cbcl-core/tests/mls_ds_canonical_vectors.txt`. That file is the
//! byte-authority the cbcl-bus JS canonicaliser (`mls-ds-canonical.mjs`) is
//! cross-checked against, closing the "self-contained TLV `canon()` is not
//! byte-for-byte `canonical_CBCL`" caveat carried by every proof module.
//!
//! `canonical_encode`, `SExpr`, and `Atom` are all in the DEFAULT cbcl-core
//! build, so this vector generator needs no feature flags (it sits alongside
//! the `mls-ds-proof` gate, not behind it).
//!
//! Run: `cargo test -p cbcl-core --test mls_ds_canonical_vectors`

use cbcl_core::canonical::canonical_encode;
use cbcl_core::sexpr::{Atom, SExpr};
use std::fmt::Write as _;

// -- terse SExpr builders (mirror the mls_ds.rs sym/qstr/num helpers) --------
fn s(x: &str) -> SExpr {
    SExpr::Atom(Atom::Symbol(x.to_string()))
}
fn k(x: &str) -> SExpr {
    SExpr::Atom(Atom::Keyword(x.to_string()))
}
fn q(x: &str) -> SExpr {
    SExpr::Atom(Atom::Str(x.to_string()))
}
fn n(x: i64) -> SExpr {
    SExpr::Atom(Atom::Num(x))
}
fn b(x: bool) -> SExpr {
    SExpr::Atom(Atom::Bool(x))
}
fn l(items: Vec<SExpr>) -> SExpr {
    SExpr::List(items)
}

fn to_hex(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        write!(out, "{byte:02x}").unwrap();
    }
    out
}

// Fixed 64-hex digests reused so the JS side can reconstruct byte-identical
// `sha256:<hex>` quoted-strings. Content is arbitrary; only the exact bytes
// matter for the cross-check.
const H_EMPTY: &str = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855";
const H_REC: &str = "1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f";
const H_BASE: &str = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
const H_CT: &str = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
const H_WEL: &str = "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc";
const H_GEN: &str = "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd";
const H_BRIDGE: &str = "eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee";

/// The ordered, labelled vector set. Each entry's canonical bytes are the
/// authority; the label is the shared key with the JS cross-check.
fn vectors() -> Vec<(&'static str, SExpr)> {
    vec![
        // ---- bare atoms: symbol ----
        ("sym-simple", s("tell")),
        ("sym-domain-tag", s("mls-ds-record-signature-v1")),
        // ---- bare atoms: keyword ----
        ("kw-simple", k("action")),
        ("kw-hyphen", k("genesis-anchor")),
        // ---- bare atoms: quoted string ----
        ("str-simple", q("room-alpha")),
        ("str-sha256", q(&format!("sha256:{H_EMPTY}"))),
        ("str-empty", q("")),
        // multi-byte UTF-8: the length prefix MUST count BYTES, not chars —
        // "café-日本" is 7 scalar values but 12 UTF-8 bytes (+1 tag = 13).
        ("str-unicode", q("café-日本")),
        // ---- bare atoms: num ----
        ("num-zero", n(0)),
        ("num-small", n(42)),
        ("num-neg", n(-7)),
        ("num-i64-max", n(i64::MAX)),
        ("num-i64-min", n(i64::MIN)),
        // ---- bare atoms: bool ----
        ("bool-true", b(true)),
        ("bool-false", b(false)),
        // ---- list framing ----
        ("list-empty", l(vec![])),
        // cross-check anchor against canonical.rs unit test: "(5:Stell3:Qhi)".
        ("list-tell-hi", l(vec![s("tell"), q("hi")])),
        // cross-check anchor: "(2:Bt2:Bf)".
        ("list-bool-pair", l(vec![b(true), b(false)])),
        // ---- real nested tuples (what the proofs actually hash/sign) ----
        // ("mls-ds-record-signature-v1", ("log-v1", room, seq, record-hash))
        (
            "nested-record-sig",
            l(vec![
                s("mls-ds-record-signature-v1"),
                l(vec![
                    s("log-v1"),
                    q("room-alpha"),
                    n(7),
                    q(&format!("sha256:{H_REC}")),
                ]),
            ]),
        ),
        // The 9-field ADD-AUTH exactly as DomainTuple::AddAuth builds it:
        // (sym tag, Str room, Sym author-key, Num base-seq, Str base-hash,
        //  Str ciphertext-digest, (Sym targets…), Str welcome-digest,
        //  Str genesis-anchor-hash)
        (
            "add-auth-9tuple",
            l(vec![
                s("mls-add-authorization-v1"),
                q("room-alpha"),
                s("@creator-author-key"),
                n(41),
                q(&format!("sha256:{H_BASE}")),
                q(&format!("sha256:{H_CT}")),
                l(vec![s("@alice"), s("@bob")]),
                q(&format!("sha256:{H_WEL}")),
                q(&format!("sha256:{H_GEN}")),
            ]),
        ),
        // ("successor-offer-core-v1", (target…), nonce, issued-at, not-after)
        (
            "successor-offer-core",
            l(vec![
                s("successor-offer-core-v1"),
                l(vec![
                    s("successor-target-v1"),
                    q("room-alpha"),
                    q(&format!("sha256:{H_BRIDGE}")),
                ]),
                q("nonce-abc123"),
                n(1_721_000_000),
                n(1_721_600_000),
            ]),
        ),
    ]
}

#[test]
fn emit_and_verify_canonical_vectors() {
    let vecs = vectors();

    // -- inline sanity anchors: pin two vectors against the exact ASCII form
    //    documented in canonical.rs's own unit tests, so a drift in the
    //    generator (not just the JS side) fails loudly here too. --
    let tell_hi = canonical_encode(&l(vec![s("tell"), q("hi")]));
    assert_eq!(tell_hi, b"(5:Stell3:Qhi)", "list-tell-hi drifted");
    let bools = canonical_encode(&l(vec![b(true), b(false)]));
    assert_eq!(bools, b"(2:Bt2:Bf)", "list-bool-pair drifted");
    // i64::MIN octets = "N-9223372036854775808" (21 bytes) => "21:N…".
    let imin = canonical_encode(&n(i64::MIN));
    assert_eq!(imin, b"21:N-9223372036854775808", "num-i64-min drifted");
    // multi-byte length prefix counts bytes: "Qcafé-日本" = 1+12 = 13 octets.
    let uni = canonical_encode(&q("café-日本"));
    assert_eq!(&uni[..3], b"13:", "str-unicode length prefix is byte-based");

    // -- emit the committed data file --
    let mut body = String::new();
    body.push_str("# SPEC-024 mls-ds/v1 canonical reference vectors (BYTE AUTHORITY)\n");
    body.push_str("# Generated by crates/cbcl-core/tests/mls_ds_canonical_vectors.rs\n");
    body.push_str("# Format: <label> <hex(canonical_encode(value))>\n");
    body.push_str("# Encoder: cbcl_core::canonical::canonical_encode (RFC 9804 §6.2 / CON-002)\n");
    for (label, expr) in &vecs {
        let hex = to_hex(&canonical_encode(expr));
        writeln!(body, "{label} {hex}").unwrap();
    }

    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/mls_ds_canonical_vectors.txt"
    );
    std::fs::write(path, &body).expect("write reference-vector data file");

    // Echo to stdout under `--nocapture` for inspection.
    print!("{body}");

    // Every vector must be non-empty and round-trip deterministically.
    for (label, expr) in &vecs {
        let a = canonical_encode(expr);
        let b = canonical_encode(expr);
        assert!(!a.is_empty(), "{label} produced empty bytes");
        assert_eq!(a, b, "{label} not deterministic");
    }
    assert_eq!(vecs.len(), 21, "expected 21 reference vectors");
}
