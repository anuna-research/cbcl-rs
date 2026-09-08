---
id: BUG-006
title: "The CON-700 envelope wire form cannot be produced by the parser that guards the trust boundary"
severity: S2
priority: P0
status: new
reported-by: agent:claude-opus-5
assigned-to: unassigned
reported-date: 2026-08-13
component: crates/cbcl-core/src/envelope.rs
---

# BUG-006: The CON-700 envelope wire form is unreachable from the wire

**Severity:** S2 (Major — a shipped feature is unreachable on its own stated
input path, and its test suite reports otherwise)
**Priority:** P0
**Status:** new
**Reported by:** agent:claude-opus-5 (Claude Code, 1M-context Opus 5)
**Assigned to:** unassigned

## Specification Reference

- **Violates:** `SPEC-015` CON-700, the redacted-envelope grammar, whose
  `hash := "sha256:" hex64` production is declared to be recognised from the
  wire (`crates/cbcl-core/src/envelope.rs:29-42`: "full recognition before any
  semantic action").
- **Related:** `SPEC-015` REQ-708 (suite-typed key identity, surface spelling
  `@[suite:]name`), which has the same defect for the same reason.
- **Caused by:** [[BUG-005]] — the two recognisers' symbol alphabets differ, and
  the envelope grammar was written against the wrong one.

## Environment

- Repository: `cbcl-rs` at commit `febc669`, branch `epp-correspondence-proof`
- Toolchain: the workspace pin in `rust-toolchain.toml`
- Detection method: deriving the normative ABNF for the IETF draft from the
  implementation; the envelope production names a token the S-expression lexer
  cannot emit

## Steps to Reproduce

```rust
#[test]
fn envelope_wire_through_strict_parser() {
    let wire = "(envelope sha256:0000000000000000000000000000000000000000000000000000000000000000 \
                 tell (@alice) (@bob) \"t-1\" \"00ff\")";
    let strict = cbcl_parser::parser::parse(wire).unwrap();
    println!("{:?}", cbcl_core::envelope::parse_envelope(&strict, 8));

    let lax = wire.parse::<cbcl_core::sexpr::SExpr>().unwrap();
    println!("{:?}", cbcl_core::envelope::parse_envelope(&lax, 8));
}
```

## Expected Behaviour

An envelope serialised by `RedactedEnvelope::to_sexpr` and transmitted as text
is recognised on receipt by the parser that guards the trust boundary — the one
`run_pipeline` uses.

## Actual Behaviour

```text
STRICT -> parse_envelope REJECT: WrongArity { found: 8 }
LAX    -> parse_envelope OK
```

`parse_envelope` reads the content hash as a **symbol** and requires it to match
`sha256:` + 64 lowercase hex (`envelope.rs:361`, `envelope.rs:263`). But `:` is
not in `parser::is_symbol_char`, so the strict lexer splits
`sha256:0000…` into the symbol `sha256` followed by the keyword `:0000…` —
two atoms where the grammar expects one. Every field after it shifts by one
position, and the arity check fires first, so the diagnostic reports
`WrongArity { found: 8 }` and never mentions the hash.

The consequence is that **no redacted envelope can be received over the wire**
under the documented grammar. Envelope-widened evidence — the SPEC-015
mechanism that makes a widened recipient's safety-level verification possible
without payload disclosure — is reachable only by constructing the `SExpr` tree
in-process, never by parsing a transmission.

The same argument applies to REQ-708's suite-typed key spelling:
`(tell @ed25519:alice "x")` parses under the strict lexer as recipient
`@ed25519` plus a stray keyword `:alice`, silently discarding the suite and
binding the message to the wrong identity. Confirmed:

```console
$ cbcl-cli parse '(tell @ed25519:alice "x")'
{"Simple":{"performative":{"Core":"Tell"},"recipient":{"One":"@ed25519"},
 "content":{"List":[]},"params":[{"Atom":{"Keyword":"alice"}},{"Atom":{"Str":"x"}}], ...
```

That is worse than a rejection: it is a silent identity substitution at the
layer that decides who signed what.

A third instance is REQ-628's wrapper dialect pin. `parse_dialect_pin`
(`role.rs:465`) also requires a bare `sha256:<hex64>` **symbol**, so the pin
splits the same way and a `with-roles` root can never carry one over the wire:

```console
$ cbcl-cli parse '(with-roles ((auctioneer @alice)) :dialect sha256:0000…0000 (signed "s" (tell @bob "x")))'
... "params":[ …bindings… ,{"Atom":{"Keyword":"dialect"}},
    {"Atom":{"Symbol":"sha256"}},{"Atom":{"Keyword":"0000…0000"}}], ...
```

`parse_wrapper_cast` matches the params slice against
`[bindings, Keyword("dialect"), value]` — three elements. The wire form yields
four, so the pin is rejected as a malformed cast. Three separate features
(envelope, suite-typed keys, dialect pin) share the one defect.

## Evidence

`crates/cbcl-core/src/envelope.rs:360`:

```rust
// hash
let content_hash = match &items[1] {
    SExpr::Atom(Atom::Symbol(s)) if is_content_hash(s) => s.clone(),
    _ => return Err(EnvelopeParseError::MalformedHash),
};
```

`crates/cbcl-core/src/envelope.rs:263`:

```rust
pub fn is_content_hash(s: &str) -> bool {
    match s.strip_prefix("sha256:") { Some(hex) => hex.len() == 64 && ..., None => false }
}
```

The test that is supposed to catch this instead conceals it.
`crates/cbcl-parser/tests/envelope_widening.rs:88-92` comments the step as
"Over the wire: CON-700 serialise ∘ parse is identity (full recognition before
any semantic action)" and then routes it through the *lax* recogniser:

```rust
let wire = envelope.to_sexpr().to_string();
let received: RedactedEnvelope =
    parse_envelope(&wire.parse::<SExpr>().unwrap(), 8).expect("wire envelope re-parses");
```

`wire.parse::<SExpr>()` is `cbcl_core`'s `FromStr`, not `cbcl_parser::parser::parse`.
The test passes, and it certifies a round trip through a recogniser that guards
nothing.

By contrast, `:caused-by` — which carries the *same* `sha256:…` hashes — is
specified against the real lexer and takes them as **strings**, which is why it
works end to end:

```console
$ cbcl-cli parse '(tell @bob "hi" :caused-by "sha256:aa")'
... "caused_by":{"Single":"sha256:aa"}
$ cbcl-cli parse '(tell @bob "hi" :caused-by (sha256:aa sha256:bb))'
validation error: malformed message: :caused-by list elements must be symbols or strings
```

So the codebase already contains the correct convention; the envelope grammar
simply does not follow it.

## Root Cause

- **Category:** interface-mismatch
- **Analysis:** the envelope grammar (CON-700) was specified as an independent
  production and implemented against a hand-built `SExpr`, with the surface
  spelling `sha256:hex64` chosen for legibility rather than checked against the
  lexer's alphabet. The test that would have caught the mismatch reached for the
  ergonomic `.parse::<SExpr>()` — the same convenience that [[BUG-005]] records
  — so the one check standing between the design and the defect was written
  against the wrong recogniser. Both the feature and its test are internally
  consistent; they are consistent with each other and with nothing on the wire.

  This is why [[BUG-005]] is P0 rather than a tidiness issue: the duplicate
  recogniser does not merely risk a differential, it has already absorbed one
  and reported it as a passing test.

## Suggested Remediation

1. Fix [[BUG-005]] first — with one recogniser, this defect becomes a visible
   test failure instead of a passing test.
2. Change the CON-700 `hash` production to a **string**, matching the
   `:caused-by` convention that already works: `hash := DQUOTE "sha256:" hex64
   DQUOTE`. Same for REQ-708 key spellings wherever a suite is present. This is
   a wire-format change; the envelope form is not yet deployed externally, so it
   is a cheap change now and an expensive one later.
   - Rejected alternative: adding `:` to `is_symbol_char`. It would make
     `:keyword` and `sym:bol` mutually ambiguous at the lexer and would
     invalidate `Parser.lean`'s alphabet along with every theorem resting on it.
3. Re-point `envelope_widening.rs:92` at `cbcl_parser::parser::parse`, so the
   test named "over the wire" runs the recogniser that is actually on the wire.
   Audit the remaining `parse::<SExpr>()` sites in `tests/` for the same claim.
4. Add a negative test asserting that `@ed25519:alice` in a recipient position
   is a **rejection**, not a silent truncation to `@ed25519`.
