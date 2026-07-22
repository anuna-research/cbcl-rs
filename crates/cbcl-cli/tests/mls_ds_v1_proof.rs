//! SPEC-024 approval gate 1 — proof that the normative `mls-ds/v1` CBCL
//! dialect installs and reproduces its pinned canonical `Dialect::hash` under
//! the repaired cbcl-rs runtime (branch `fix/mls-ds-quoted-hash-depth`).
//!
//! This test uses ONLY real library functions: `cbcl_parser::{parse,
//! parse_dialect}` for source -> `Dialect`, `DialectRegistry::install` for the
//! R1..R6 install path, and `cbcl_core::canonical::dialect_hash` for the
//! canonical content hash. Nothing is re-implemented.
//!
//! The dialect source is `include_str!`'d from a byte-identical copy of the
//! normative file whose raw SHA-256 is
//! `f668451b75215e2bf5b100219cb73aeaf674f975a5238f1da7751778c0b18bf2`.

use cbcl_core::canonical::dialect_hash;
use cbcl_core::dialect::DialectRegistry;
use cbcl_core::r1::verify_r1_dialect;
use cbcl_core::r2::verify_r2;
use cbcl_core::r3::verify_r3;
use cbcl_core::r4::{check_r4, R4Result, Signer};
use cbcl_core::r5::verify_r5_with_ancestors;
use cbcl_core::r6::r6_violations;
use cbcl_core::role::{parse_dialect_pin, parse_wrapper_cast};
use cbcl_core::sexpr::SExpr;
use cbcl_parser::{parse, parse_dialect};

/// Byte-identical copy of the normative dialect (raw SHA `f668451b…`).
const DIALECT_SRC: &str = include_str!("mls-ds-v1.cbcl");

/// The canonical `Dialect::hash` the spec pins (over the signable AST, not the
/// raw file bytes).
const EXPECTED_CANONICAL_HASH: &str =
    "sha256:922ba8bf9eb62a07b81989a9bfe6754a626b2edaf4d3f52e3fc4b41321261858";

/// A trivial signer. `check_r4` returns `Unsigned` before ever touching the
/// signer when the dialect carries no `:signature`, so its behaviour is
/// irrelevant here — it only satisfies the `&dyn Signer` argument.
struct NoSigner;
impl Signer for NoSigner {
    fn sign(&self, _data: &[u8]) -> Vec<u8> {
        Vec::new()
    }
    fn verify(&self, _data: &[u8], _sig: &[u8]) -> bool {
        false
    }
}

#[test]
fn mls_ds_v1_installs_and_reproduces_pinned_hash() {
    // ---- parse: source -> SExpr -> Dialect (real library parser) ----
    let expr = parse(DIALECT_SRC).expect("dialect source parses to an SExpr");
    let d = parse_dialect(&expr).expect("SExpr parses to a Dialect");

    // ---- Task 4: performative count + resource bounds ----
    assert_eq!(d.name, "mls-ds/v1");
    assert_eq!(d.performatives.len(), 40, "expected 40 performatives");
    assert_eq!(d.resources.max_depth, 9, "max-depth");
    assert_eq!(d.resources.max_expansion_size, 8192, "max-expansion-size");
    assert_eq!(d.resources.verification_time_ms, 10, "verification-time");
    println!(
        "performatives={} bounds=(max-depth {}, max-expansion-size {}, verification-time {})",
        d.performatives.len(),
        d.resources.max_depth,
        d.resources.max_expansion_size,
        d.resources.verification_time_ms,
    );

    // ---- individual R-verdicts on the install path ----
    // `DialectRegistry::install` runs R1 -> R2 -> protocol-budget -> R3 -> R5
    // -> R6 -> ensure_hash. R4 is a separate `check_r4` (Unsigned here).
    let r1 = verify_r1_dialect(&d);
    let r2 = verify_r2(&d);
    let r3 = verify_r3(&d);
    let reg0 = DialectRegistry::new();
    let ancestors = reg0.resolve_ancestors(&d);
    let r5 = verify_r5_with_ancestors(&d, &ancestors);
    let r6v = r6_violations(&d);
    let r4 = check_r4(&d, &NoSigner);
    println!(
        "R1={r1} R2={r2} R3={r3} R5={r5} R6_violations={} R4={r4:?}",
        r6v.len()
    );
    assert!(r1, "R1 (no recursion) must pass");
    assert!(r2, "R2 (resource bounds) must pass");
    assert!(r3, "R3 (core preservation) must pass");
    assert!(r5, "R5 (protocol/shape coherence) must pass");
    assert!(r6v.is_empty(), "R6 (role layer) must pass, got {r6v:?}");
    assert_eq!(r4, R4Result::Unsigned, "unsigned dialect => R4 Unsigned");

    // ---- Task 2/3: canonical Dialect::hash via the library path ----
    let computed = dialect_hash(&d);
    println!("computed canonical Dialect::hash = {computed}");
    assert_eq!(
        computed, EXPECTED_CANONICAL_HASH,
        "canonical Dialect::hash must reproduce the spec pin"
    );

    // ---- full install through the real registry path ----
    let mut reg = DialectRegistry::new();
    reg.install(d.clone())
        .expect("mls-ds/v1 must install cleanly (R1..R6)");
    let installed = reg
        .find_by_name("mls-ds/v1")
        .expect("installed dialect present");
    // The source declares no `:hash`, so `ensure_hash` computes+stores the
    // canonical hash at install; it must equal the pin.
    assert_eq!(
        installed.hash.as_deref(),
        Some(EXPECTED_CANONICAL_HASH),
        "install must stamp the canonical hash"
    );

    // ---- Task 5 (Defect B): a `with-roles` wrapper cast carrying the quoted
    //      `:dialect` pin parses, and its extracted pin equals the bare-form
    //      pin and the computed hash. ----
    let bare_pin: SExpr = computed.parse().expect("bare pin token"); // Atom::Symbol
    let quoted_pin: SExpr = format!("\"{computed}\"")
        .parse()
        .expect("quoted pin token"); // Atom::Str

    // direct pin-parser equivalence
    assert_eq!(parse_dialect_pin(&bare_pin).unwrap(), computed);
    assert_eq!(parse_dialect_pin(&quoted_pin).unwrap(), computed);

    // full wrapper-cast equivalence, bound to the dialect's own roles
    let binds: SExpr = "((client @c) (ds @d))".parse().unwrap();
    let kw: SExpr = ":dialect".parse().unwrap();
    let cast_bare =
        parse_wrapper_cast(&[binds.clone(), kw.clone(), bare_pin], &d.roles).unwrap();
    let cast_quoted = parse_wrapper_cast(&[binds, kw, quoted_pin], &d.roles).unwrap();
    assert_eq!(cast_bare.dialect_pin.as_deref(), Some(computed.as_str()));
    assert_eq!(cast_quoted.dialect_pin.as_deref(), Some(computed.as_str()));
    assert_eq!(
        cast_bare, cast_quoted,
        "quoted `:dialect` pin must yield the same Cast as the bare spelling"
    );
    println!(
        "quoted-pin demo OK: bare == quoted == {}",
        cast_quoted.dialect_pin.as_deref().unwrap()
    );
}
