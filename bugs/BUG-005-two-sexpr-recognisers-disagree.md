---
id: BUG-005
title: "Two S-expression recognisers ship in the workspace and disagree on accept/reject"
severity: S2
priority: P0
status: new
reported-by: agent:claude-opus-5
assigned-to: unassigned
reported-date: 2026-08-13
component: crates/cbcl-core/src/sexpr.rs
---

# BUG-005: Two S-expression recognisers ship in the workspace and disagree

**Severity:** S2 (Major — a parser differential in the public API of a project
whose thesis is the elimination of parser differentials)
**Priority:** P0
**Status:** new
**Reported by:** agent:claude-opus-5 (Claude Code, 1M-context Opus 5)
**Assigned to:** unassigned

## Specification Reference

- **Violates:** the central claim of `SPEC-001` and of the LangSec '26 paper
  (arXiv:2604.14512, §VII-A *Parser equivalence*): "all conformant parsers
  produce identical parse trees for every input. This eliminates the
  grammar-level parser differential vulnerabilities that arise when different
  implementations interpret the same message differently."
- **Related:** `docs/cbcl-grammar.ebnf`, which documents exactly one symbol
  alphabet; `crates/cbcl-parser/tests/differential.rs`, which cross-checks the
  Rust parser against the Lean-extracted binary but never against the second
  in-workspace recogniser.
- **Blocks:** [[BUG-006]] — the envelope defect is a direct consequence of the
  alphabet divergence recorded here.

## Environment

- Repository: `cbcl-rs` at commit `febc669`, branch `epp-correspondence-proof`
- Toolchain: the workspace pin in `rust-toolchain.toml`
- Detection method: deriving the normative ABNF for the IETF draft from the
  implementation, then differential-probing the two recognisers against each
  other

## Steps to Reproduce

Place the following at `crates/cbcl-parser/tests/differential_probe.rs` and run
`cargo test -p cbcl-parser --test differential_probe -- --nocapture`:

```rust
use cbcl_core::sexpr::SExpr;

fn probe(src: &str) {
    let a = cbcl_parser::parser::parse(src)
        .map(|e| format!("{e:?}"))
        .unwrap_or_else(|e| format!("REJECT({e})"));
    let b = src.parse::<SExpr>()
        .map(|e| format!("{e:?}"))
        .unwrap_or_else(|e| format!("REJECT({e})"));
    println!("{} {src}", if a == b { "agree  " } else { "DIVERGE" });
}

#[test]
fn probe_differential() {
    for s in [
        r#"(a sha256:00ff)"#, r#"(tell @ed25519:alice "x")"#, "(a ; c\nb)",
        r#"(a #true)"#, r#"("a\qb")"#, r#"(a [b])"#, r#"(a 1-2)"#, r#"(a b;c)"#,
    ] { probe(s); }
}
```

## Expected Behaviour

One input language, one recogniser, one parse tree. Every path that turns text
into an `SExpr` agrees.

## Actual Behaviour

All eight probes diverge. `cbcl_parser::parser::parse` (strict, fuel-bounded,
mirrored by `Parser.lean`) and `<&str>::parse::<SExpr>()` — the `FromStr` impl
at `crates/cbcl-core/src/sexpr.rs:134`, reached through the *public* `sexpr`
module — recognise different languages:

| Input | `cbcl_parser::parser::parse` | `cbcl_core` `FromStr` |
|---|---|---|
| `(a sha256:00ff)` | `[a, sha256, :00ff]` (3 atoms) | `[a, sha256:00ff]` (2 atoms) |
| `(tell @ed25519:alice "x")` | `[tell, @ed25519, :alice, "x"]` | `[tell, @ed25519:alice, "x"]` |
| `(a ; c\nb)` | comment stripped → `[a, b]` | `[a, ;, c, b]` |
| `(a #true)` | **accepts** as `[a, #t, rue]` | `[a, #t]` |
| `("a\qb")` | REJECT `invalid escape '\q'` | accepts, `"a\\qb"` |
| `(a [b])` | REJECT `unexpected '['` | accepts, symbol `[b]` |
| `(a 1-2)` | REJECT `integer overflow` | accepts, symbol `1-2` |
| `(a b;c)` | REJECT (comment eats `)`) | accepts, symbol `b;c` |

Three distinct divergence classes:

1. **Token alphabet.** `parser::is_symbol_char` admits a closed 12-character
   punctuation set; `cbcl_core`'s `parse_num_or_symbol` takes any run up to
   whitespace, `(`, `)`, or `"`. So `:`, `;`, `#`, `[`, `\` are symbol
   constituents in one and delimiters or errors in the other.
2. **Silent misacceptance.** `(a #true)` is accepted by the *strict* parser as
   two atoms, `#t` followed by the symbol `rue`. A recogniser that splits an
   unrecognised literal into a valid token plus a residue, rather than
   rejecting it, is a weird-machine primitive.
3. **Error handling discipline.** `cbcl_core`'s string parser *preserves*
   invalid escapes (`\q` → `\q`) instead of rejecting them — repair, not
   rejection, contra the LangSec principle the project states.

`cbcl_core`'s recogniser is additionally unbounded: it has no fuel parameter
and recurses on nesting depth, so deeply nested input overflows the stack where
`parser::parse` returns `FuelExhausted`.

## Evidence

`crates/cbcl-parser/src/parser.rs:328`:

```rust
fn is_symbol_char(ch: char) -> bool {
    ch.is_ascii_alphanumeric()
        || ch == '_' || ch == '-' || ch == '.' || ch == '/' || ch == '!'
        || ch == '?' || ch == '+' || ch == '*' || ch == '<' || ch == '>'
        || ch == '=' || ch == '@'
}
```

`crates/cbcl-core/src/sexpr.rs:277`:

```rust
fn parse_num_or_symbol(input: &str) -> Result<(SExpr, &str), ParseSExprError> {
    let end = input
        .find(|c: char| c.is_ascii_whitespace() || c == '(' || c == ')' || c == '"')
        .unwrap_or(input.len());
    ...
}
```

The strict parser is the one on the trust boundary: `run_pipeline` and
`run_pipeline_full` both call `parser::parse` (`pipeline.rs:183`, `pipeline.rs:214`).
So there is **no bypass inside this workspace's own pipeline**. The exposure is
at the two edges:

- **Public API.** `cbcl_core::sexpr` is `pub` (`lib.rs:68`), so `FromStr` is
  public surface. `README.md` names two downstream consumers that link this
  crate at a trust boundary — `cbcl-router` ("R1–R4 validators on every
  message") and `hark` ("local parse and R1–R5 validation at the `/send` and
  `recv` boundaries"). Either reaches the lax recogniser by writing the
  idiomatic `text.parse::<SExpr>()`.
- **Test fidelity.** Tests that model reception "over the wire" use the lax
  recogniser, so they do not exercise the recogniser that actually guards the
  boundary. `crates/cbcl-parser/tests/envelope_widening.rs:92` is the clearest
  instance and is the subject of [[BUG-006]].

## Root Cause

- **Category:** duplicate-implementation
- **Analysis:** `FromStr` reads as a convenience — the ergonomic
  `"(tell @bob \"hi\")".parse()` used throughout unit tests — and convenience
  parsers are written to be permissive because their only job is to accept the
  literals the author typed. The defect is not that it is lax; it is that it is
  *public* and *lax*, in a crate whose stated contract is that exactly one
  language is recognised. Nothing in the type system or the test suite
  distinguishes "the recogniser" from "a recogniser", so the divergence was free
  to widen: no test compares them, and `differential.rs` compares the strict
  parser against Lean, reinforcing the impression that differential coverage
  exists.

## Suggested Remediation

Preferred, in order:

1. **Delete the second recogniser.** Make `FromStr for SExpr` delegate to
   `cbcl_parser::parser::parse`. This inverts the current dependency
   (`cbcl-parser` → `cbcl-core`), so it requires either moving the parser into
   `cbcl-core` or moving `FromStr` into `cbcl-parser` as an extension trait.
   Moving `parser.rs` into `cbcl-core` is the smaller change and matches the
   purity boundary: the parser is already `no_std + alloc` and effect-free.
2. If the impl must stay where it is, make it *strictly* equivalent — same
   alphabet, same escape rejection, same fuel bound — and add a property test
   asserting agreement on arbitrary input, so the equivalence cannot silently
   rot again.

Either way, add the differential-probe test above as a regression test: it is
the check whose absence let this survive. Fix `#true` acceptance in the strict
parser as part of the same change — `#` followed by anything other than exactly
`t` or `f` at a token boundary should be a typed rejection, not a split.
