# R4 Adversarial Cryptographic Review

**Date**: 2026-03-18
**Scope**: USDD Tier 1 adversarial review of R4 integrity constraint implementation
**Files reviewed**: `crates/cbcl-core/src/r4.rs`, `crates/cbcl-core/src/dialect.rs`, `crates/cbcl-core/src/serializer.rs`
**Spec references**: IETF draft-cbcl.md §R4 (lines 435–742), `specs/SPEC-001.md` REQ-090–091
**Reference impl**: `src/cbcl/signature.scm`

---

## Summary

The R4 implementation provides a trait-based abstraction for Ed25519 signature verification
over dialect definitions. The design cleanly separates the pure verification logic (core) from
concrete cryptographic implementations (shell), which is architecturally sound.

However, this review identifies **3 critical**, **4 high**, and **3 moderate** findings that
must be addressed before the cryptographic code can be considered safe for production use.

---

## Critical Findings

### CRIT-01: Canonical form does not match IETF spec (RFC 9804)

**Location**: `r4.rs:72–80` (`dialect_sign_body`)

The IETF spec (line 725) states:

> Dialect signatures MUST be computed over the canonical form of the dialect S-expression
> as defined in RFC 9804.

The current implementation uses naive string concatenation:

```rust
fn dialect_sign_body(d: &Dialect) -> Vec<u8> {
    let mut body = String::new();
    body.push_str(&d.name);
    for p in &d.performatives {
        body.push_str(&p.name);
        body.push_str(&serialize(&p.template));
    }
    body.into_bytes()
}
```

This is **not** RFC 9804 canonical S-expression encoding. The Guile reference implementation
uses `canonicalize-for-signing` which produces proper canonical S-expressions with
length-prefixed verbatim strings and no whitespace between list elements.

**Impact**: Signatures produced by the Rust implementation will not verify against the Guile
reference implementation (or any other RFC 9804-compliant implementation), breaking
cross-implementation interoperability — a core design goal.

**Recommendation**: Implement RFC 9804 canonical encoding and use it for the sign body.
The entire dialect S-expression (not just name + performatives) should be serialized
to canonical form.

---

### CRIT-02: Ambiguous sign body enables signature confusion

**Location**: `r4.rs:72–80` (`dialect_sign_body`)

The concatenation has no delimiters or length prefixes between fields. This creates
ambiguity where two structurally different dialects produce identical sign bodies.

**Proof of concept**:

| Dialect | name | performative name | template |
|---------|------|-------------------|----------|
| A       | `"ab"` | `"cd"` | `(e)` |
| B       | `"abc"` | `"d"` | `(e)` |

Both produce sign body: `abcd(e)`.

An attacker who obtains a valid signature for dialect A can construct dialect B with
the same signature, and it will verify successfully.

**Impact**: Signature forgery via field boundary confusion. An attacker can create a
dialect with a different name that verifies under another dialect's signature.

**Recommendation**: Use length-prefixed encoding (RFC 9804 canonical form) or insert
unambiguous delimiters (e.g., null bytes) between fields. Fixing CRIT-01 resolves this.

---

### CRIT-03: Signature does not cover critical dialect fields

**Location**: `r4.rs:72–80` (`dialect_sign_body`)

The sign body includes only `name` and `performatives[].{name, template}`. The following
security-critical fields are **excluded**:

| Field | Signed? | Security impact if modified |
|-------|---------|---------------------------|
| `author` | **No** | Attacker can re-attribute a signed dialect to a different author |
| `extends` | **No** | Attacker can change inheritance chain, altering resolution semantics |
| `resources` | **No** | Attacker can weaken resource bounds (e.g., `max_depth: 64`, `max_expansion_size: 8192`) to enable resource exhaustion |
| `hash` | **No** | Attacker can remove or alter integrity hash |
| `protocol` | **No** | Attacker can change declared signing protocol |
| `performatives[].params` | **No** | Attacker can alter parameter declarations |

The IETF spec (line 725) says signatures are computed over "the canonical form of the
dialect S-expression" — i.e., the **entire** dialect definition, not a subset of fields.

**Impact**: An attacker who intercepts a validly signed dialect can modify `author`,
`extends`, `resources`, `params`, `hash`, and `protocol` fields without invalidating
the signature. This defeats integrity, authenticity, and non-repudiation guarantees.

**Recommendation**: Sign the complete canonical dialect S-expression. All fields must be
covered by the signature.

---

## High Findings

### HIGH-01: No author-to-key binding in verification

**Location**: `r4.rs:47–57` (`check_r4`)

The IETF spec (line 734) requires:

> 4. Confirm the signing key matches the declared author

The `check_r4` function takes a single `signer: &dyn Signer` but never checks that the
signer's key corresponds to `d.author`. The `Signer` trait has no method to retrieve or
compare the public key identity.

```rust
pub fn check_r4(d: &Dialect, signer: &dyn Signer) -> R4Result {
    let Some(ref sig) = d.signature else {
        return R4Result::Unsigned;
    };
    let body = dialect_sign_body(d);
    if signer.verify(&body, sig) {  // No author check
        R4Result::Valid
    } else {
        R4Result::Invalid
    }
}
```

**Impact**: If the caller provides the wrong signer (or a signer with a different key
than the declared author), the verification is meaningless. A dialect signed by author A
could be verified using author B's key if the caller makes a binding mistake.

**Recommendation**: Either:
- Add a `public_key_id(&self) -> &str` method to `Signer` and compare against `d.author`
  inside `check_r4`, or
- Add a `verify_for_author(&self, author: &str, data: &[u8], sig: &[u8]) -> bool` method
  that performs the binding internally, or
- Document this as a caller responsibility and add `author` to the sign body (CRIT-03).

---

### HIGH-02: No signature length validation

**Location**: `r4.rs:17–22` (Signer trait), `dialect.rs:123` (Dialect struct)

Ed25519 signatures are exactly 64 bytes. The implementation accepts `Option<Vec<u8>>` with
no length validation at any layer:

1. `Dialect.signature` is `Option<Vec<u8>>` — accepts any length
2. `Signer::verify` receives `sig: &[u8]` — no length constraint in the trait contract
3. `check_r4` passes the signature directly without validation

**Impact**: While a correct Ed25519 implementation will reject wrong-length signatures,
the trait abstraction means a buggy `Signer` implementation could accept truncated or
malformed signatures. A 0-byte signature `Some(vec![])` is treated as "signed" (not
`Unsigned`) and goes through verification rather than being rejected outright.

**Recommendation**: Add a `SIGNATURE_LEN` associated constant to `Signer` or validate
`sig.len() == 64` in `check_r4` before calling `verify`. At minimum, reject empty
signatures before calling `verify`.

---

### HIGH-03: Signer trait lacks constant-time requirement

**Location**: `r4.rs:17–22` (Signer trait)

The `Signer` trait documentation does not specify that `verify` must use constant-time
comparison internally. The test mock uses `sig == [0xAA, 0xBB]` which is a variable-time
comparison.

While the core crate cannot enforce constant-time behavior (it's `no_std` + pure), the trait
documentation should explicitly state the requirement. Implementors who follow the mock
pattern will introduce timing side channels.

**Impact**: A `Signer` implementation using variable-time signature comparison leaks
information about the expected signature through timing differences, potentially enabling
online signature forgery.

**Recommendation**: Add a doc comment to `Signer::verify`:
```rust
/// Implementations MUST use constant-time comparison for signature
/// verification to prevent timing side-channel attacks. Use a
/// cryptographic library (e.g., ed25519-dalek, ring) that provides
/// this guarantee. Do NOT use `==` on byte slices.
```

---

### HIGH-04: `verify_r4` returns false for unsigned dialects (misleading API)

**Location**: `r4.rs:59–65`

```rust
pub fn verify_r4(d: &Dialect, signer: &dyn Signer) -> bool {
    check_r4(d, signer) == R4Result::Valid
}
```

This returns `false` for unsigned dialects. Meanwhile, `install_with_signer` uses `check_r4`
and accepts unsigned dialects. A caller using `verify_r4` as a security gate would reject
all unsigned dialects, while `install_with_signer` would accept them.

The function name `verify_r4` strongly implies "does this dialect pass R4 verification?"
which, per the spec, unsigned dialects do (with a warning). The doc comment says "Returns
`true` only if the dialect has a signature and it verifies" but the function name does not
convey this stricter semantic.

**Impact**: API misuse risk. A caller who uses `verify_r4` expecting spec-compliant
behavior will incorrectly reject valid unsigned dialects.

**Recommendation**: Rename to `has_valid_signature` or `verify_r4_strict`, or change the
return semantics to match `is_acceptable()`. Deprecate the current function.

---

## Moderate Findings

### MOD-01: No protection against Ed25519 signature malleability

**Location**: `r4.rs:17–22` (Signer trait)

Ed25519 has a known S-malleability issue: for any valid signature `(R, s)`, the value
`(R, -s mod l)` is also mathematically valid. RFC 8032 §5.1.7 specifies that
implementations SHOULD reject signatures where `s >= l` (the group order).

The `Signer` trait does not specify whether implementations must check for S-malleability.
If an implementation accepts malleable signatures, an attacker can create a second valid
signature for any signed dialect without knowing the private key.

**Impact**: Signature malleability can break deduplication, caching, or audit logging
that assumes signature uniqueness. It does not break authenticity or integrity directly.

**Recommendation**: Document in the `Signer` trait that implementations MUST reject
non-canonical signatures (s >= l). Reference RFC 8032 §5.1.7.

---

### MOD-02: No key material zeroization guidance

**Location**: `r4.rs:17–22` (Signer trait)

The `Signer::sign` method implies that implementations will hold private key material.
The trait provides no guidance on secure handling of key material:

- No requirement to use zeroizing types (e.g., `zeroize::Zeroize`)
- No guidance on preventing key material from being swapped to disk
- No warning about `Debug` implementations potentially logging key bytes

**Impact**: Implementors may store Ed25519 private keys in plain `Vec<u8>` that persists
in memory after deallocation, potentially recoverable through memory inspection.

**Recommendation**: Add documentation requiring implementations to use zeroizing storage
for private keys. Consider adding a `Zeroize` supertrait bound or documenting the
expectation.

---

### MOD-03: Test mock signers do not validate cryptographic properties

**Location**: `r4.rs:91–116` (MockSigner, AuthoritySigner)

The test mocks use trivial 2-byte signatures (`[0xAA, 0xBB]`, `[0xCC, 0xDD]`) and
data-independent verification. While acceptable for unit tests, these mocks:

1. Cannot detect if `dialect_sign_body` produces correct output (the mock ignores `data`)
2. Cannot detect canonicalization bugs (CRIT-01, CRIT-02)
3. Do not test actual Ed25519 behavior (malleability, wrong-length rejection, etc.)

**Impact**: Test coverage gives false confidence. All R4 tests pass with the current
broken canonical form because mocks don't validate the signed data.

**Recommendation**: Add integration tests with a real Ed25519 implementation (e.g.,
`ed25519-dalek`) behind a `#[cfg(feature = "test-crypto")]` flag. Include cross-implementation
test vectors with known keys, messages, and expected signatures.

---

## Informational Notes

### INFO-01: Guile reference implementation has incomplete base64

The Guile reference (`src/cbcl/signature.scm:88–116`) contains stub base64 encode/decode
functions with `TODO` comments. The "decoder" reads raw bytes from a string port, which
is not base64 decoding. This means the reference implementation's signature verification
is also not fully functional for base64-encoded signatures.

### INFO-02: `install_with_signer` return type changed from doc comment

The doc comment on `install_with_signer` (dialect.rs:257) says "Returns `((), R4Result)`"
but the actual return type is `Result<R4Result, DialectInstallError>`. Minor doc inconsistency.

### INFO-03: `check_r4` short-circuits on missing signature before computing sign body

This is correct behavior — `dialect_sign_body` is not called when no signature is present,
avoiding unnecessary work. No issue here.

---

## Summary of Recommendations

| ID | Severity | Status | Fix |
|----|----------|--------|-----|
| CRIT-01 | Critical | Open | Implement RFC 9804 canonical encoding for sign body |
| CRIT-02 | Critical | Open | Use length-prefixed encoding (resolved by CRIT-01 fix) |
| CRIT-03 | Critical | Open | Sign the complete dialect definition, not a field subset |
| HIGH-01 | High | Open | Add author-to-key binding in verification |
| HIGH-02 | High | Open | Validate signature length (64 bytes for Ed25519) |
| HIGH-03 | High | Open | Document constant-time requirement on Signer::verify |
| HIGH-04 | High | Open | Rename or fix `verify_r4` semantics |
| MOD-01 | Moderate | Open | Document S-malleability rejection requirement |
| MOD-02 | Moderate | Open | Add key material zeroization guidance |
| MOD-03 | Moderate | Open | Add integration tests with real Ed25519 |

---

## USDD Compliance Note

Per USDD AI Trust Boundaries, cryptography is a **no-go area** requiring explicit approval.
The findings in this review — particularly CRIT-01 through CRIT-03 and HIGH-01 — indicate
that the R4 implementation does not yet meet the security bar for production deployment.

The trait-based design (deferring concrete crypto to the shell) is architecturally sound and
aligns with the purity boundary (ADR-004). However, the core verification logic has
correctness issues that cannot be mitigated by a correct shell implementation alone.

**Recommendation**: Do not approve R4 for production use until CRIT-01–03 and HIGH-01–02
are resolved and verified with cross-implementation test vectors.
