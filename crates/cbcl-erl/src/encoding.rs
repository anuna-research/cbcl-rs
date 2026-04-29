//! SExpr/Message → BEAM term encoders for the CBCL NIF binding.
//!
//! Implements SPEC-009 CON-001 — the Erlang term shape that
//! `cbcl_erl:parse_message/1` (and the lax/dialect siblings) returns.
//!
//! # CON-001 v0.1.0: four-variant message shape with a `:type` tag
//!
//! Every encoded `Message` map carries a `:type` atom discriminator so
//! BEAM-side consumers can dispatch uniformly across the four variants
//! of the Rust-side `cbcl_core::message::Message` enum:
//!
//! - `:type => simple`  — the historical CON-001 shape (7 keys + `:type`).
//! - `:type => wrapped` — `(envelope|signed|with-limits ... <inner>)`.
//! - `:type => dialect` — `(lang <name> <inner>)`.
//! - `:type => meta`    — `(meta <dialect_def>)`.
//!
//! Earlier drafts collapsed `Wrapped` / `Dialect` to their innermost
//! `Simple` and rejected `Meta` outright. That broke REQ-002 ("preserve
//! the semantics of `cbcl_parser::parse_message`") and silently dropped
//! wrapper / dialect / meta information. v0.1.0 encodes every variant
//! losslessly.
//!
//! ## Variant shapes
//!
//! Simple (8 keys total — the seven CON-001 keys plus `:type`):
//!
//! ```text
//! #{ type         := simple
//!  , performative := atom() | {custom, binary()}
//!  , recipient    := binary() | undefined
//!  , content      := sexpr_term()
//!  , params       := #{binary() => sexpr_term()}     %% see CON-001 deviation below
//!  , thread       := binary() | undefined
//!  , sender       := binary() | undefined
//!  , caused_by    := undefined | begin | [binary()]
//!  }
//! ```
//!
//! Wrapped:
//!
//! ```text
//! #{ type    := wrapped
//!  , wrapper := envelope | signed | with_limits     %% closed enum, atom-safe
//!  , params  := #{binary() => sexpr_term()}
//!  , inner   := message_map()
//!  }
//! ```
//!
//! Dialect:
//!
//! ```text
//! #{ type    := dialect
//!  , dialect := binary()                            %% NOT atom — see deviation
//!  , inner   := message_map()
//!  }
//! ```
//!
//! Meta:
//!
//! ```text
//! #{ type        := meta
//!  , dialect_def := sexpr_term()
//!  }
//! ```
//!
//! ## CON-001 v0.1.0 deviation: param keys are binaries
//!
//! CON-001 originally specifies `params` as `#{atom() => sexpr_term()}`.
//! v0.1.0 deviates: param keys are encoded as **binaries** (`binary()`),
//! NOT atoms. Rationale:
//!
//! - BEAM atoms are not garbage-collected. The atom table is a fixed-size
//!   global resource and exhausting it crashes the entire VM.
//! - Param names are user-supplied data crossing the trust boundary.
//!   Allowing untrusted input to mint new atoms is a textbook atom-table
//!   exhaustion DoS — exactly the trust-boundary risk REQ-005 / ADR-001
//!   are built to mitigate.
//!
//! BEAM-side consumers must pattern-match params with binary keys:
//!
//! ```erlang
//! %% v0.1.0 (correct):
//! #{<<"thread">> := T} = Params,
//! %% NOT:
//! #{thread := T} = Params.   %% wrong — keys are binaries
//! ```
//!
//! The same rationale applies to the `:dialect` field: the dialect name
//! flows from user input and is therefore a binary, not an atom. The
//! `:wrapper` field IS an atom because `WrapperType` is a closed enum
//! of three values (`envelope` / `signed` / `with_limits`).
//!
//! This deviation is a v0.1.0 hardening. It MAY be lifted if a future
//! SPEC-009 amendment introduces an atom-allowlist scheme that bounds
//! the set of permitted param keys at the trust boundary.
//!
//! # `caused_by` encoding (extension to CON-001)
//!
//! CON-001 says "list of content hashes" but `Message::caused_by` is
//! `Option<CausedBy>` with three variants — `Begin`, `Single(hash)`,
//! `Multiple(hashes)`. We encode them as:
//!
//! - `None` → atom `undefined`
//! - `Some(Begin)` → atom `begin`
//! - `Some(Single(h))` → list `[<<"h">>]` (a one-element list)
//! - `Some(Multiple(hs))` → list `[<<"h1">>, <<"h2">>, …]`
//!
//! This keeps the BEAM-side type stable (atom-or-list) and is
//! documented here because the choice is not literally written in the
//! spec.
//!
//! # SExpr atom encoding
//!
//! - `Atom::Symbol(s)`  → `{symbol,  <<"s">>}` (tagged 2-tuple)
//! - `Atom::Keyword(s)` → `{keyword, <<"s">>}` (tagged 2-tuple)
//! - `Atom::Str(s)`     → `<<"s">>` (bare binary — strings are the
//!   common case so they don't pay the tagging tax)
//! - `Atom::Num(n)`     → integer
//! - `Atom::Bool(b)`    → `true` / `false` atoms
//!
//! `SExpr::List(xs)` becomes a BEAM list of recursively-encoded
//! children. The `symbol` / `keyword` tags are static atoms drawn from
//! a closed two-element set — atom-safe.
//!
//! # Performative encoding
//!
//! - `Performative::Core(c)` → atom (`tell`, `ask`, `reply`, …) using
//!   `CorePerformative::as_str()` (already lowercase ASCII, closed enum).
//! - `Performative::Custom(s)` → `{custom, <<"s">>}` (tagged 2-tuple
//!   so BEAM-side pattern matches stay sharp; `custom` is a static atom).

use cbcl_core::message::{CausedBy, CorePerformative, Message, Performative, WrapperType};
use cbcl_core::sexpr::{Atom, SExpr};
use rustler::types::atom::Atom as ErlAtom;
use rustler::{Encoder, Env, NifResult, Term};

/// Encode an SExpr into a BEAM term. See module docs for the mapping.
pub(crate) fn encode_sexpr<'a>(env: Env<'a>, e: &SExpr) -> Term<'a> {
    match e {
        SExpr::Atom(a) => encode_atom(env, a),
        SExpr::List(items) => {
            let terms: Vec<Term<'a>> = items.iter().map(|x| encode_sexpr(env, x)).collect();
            terms.encode(env)
        }
    }
}

fn encode_atom<'a>(env: Env<'a>, a: &Atom) -> Term<'a> {
    match a {
        Atom::Symbol(s) => tagged_binary(env, "symbol", s),
        Atom::Keyword(s) => tagged_binary(env, "keyword", s),
        Atom::Str(s) => s.as_str().encode(env),
        Atom::Num(n) => n.encode(env),
        Atom::Bool(b) => b.encode(env),
    }
}

/// Build a `{Tag, <<"Bin">>}` 2-tuple, where `Tag` is an atom drawn from
/// a closed static set (e.g. `symbol`, `keyword`, `custom`) — never a
/// user-supplied string. See the atom-DoS rationale in the module docs.
fn tagged_binary<'a>(env: Env<'a>, tag: &str, bin: &str) -> Term<'a> {
    let tag_atom = ErlAtom::from_str(env, tag).expect("static ASCII tag fits in an atom");
    (tag_atom, bin).encode(env)
}

/// Atom helpers for the `:type` discriminator. Each is a closed-set
/// static atom; minting them at NIF call time is safe.
fn type_atom(env: Env<'_>, name: &'static str) -> ErlAtom {
    ErlAtom::from_str(env, name).expect("static ASCII type tag fits in an atom")
}

fn simple_atom(env: Env<'_>) -> ErlAtom {
    type_atom(env, "simple")
}

fn wrapped_atom(env: Env<'_>) -> ErlAtom {
    type_atom(env, "wrapped")
}

fn dialect_atom(env: Env<'_>) -> ErlAtom {
    type_atom(env, "dialect")
}

fn meta_atom(env: Env<'_>) -> ErlAtom {
    type_atom(env, "meta")
}

/// Encode a `WrapperType` as a closed-enum atom (`envelope` / `signed`
/// / `with_limits`). Note the underscore in `with_limits` — BEAM atoms
/// can't contain hyphens without quoting, so the canonical text name
/// `"with-limits"` becomes the atom `with_limits` here. Three values,
/// closed set, atom-safe.
fn encode_wrapper_type<'a>(env: Env<'a>, w: WrapperType) -> Term<'a> {
    let name = match w {
        WrapperType::Envelope => "envelope",
        WrapperType::Signed => "signed",
        WrapperType::WithLimits => "with_limits",
    };
    ErlAtom::from_str(env, name)
        .expect("wrapper-type names are ASCII")
        .to_term(env)
}

/// Build a map from a slice of `(key_str, value_term)` pairs. The keys
/// here are CON-001 schema keys (closed static set: `type`, `performative`,
/// `recipient`, …) — atomising them is safe.
fn make_map<'a>(env: Env<'a>, fields: &[(&'static str, Term<'a>)]) -> NifResult<Term<'a>> {
    let mut keys: Vec<Term<'a>> = Vec::with_capacity(fields.len());
    let mut values: Vec<Term<'a>> = Vec::with_capacity(fields.len());
    for (k, v) in fields {
        let key = ErlAtom::from_str(env, k)
            .expect("CON-001 schema key fits in an atom")
            .to_term(env);
        keys.push(key);
        values.push(*v);
    }
    Term::map_from_term_arrays(env, &keys, &values)
}

/// Encode a `Message` as a CON-001 v0.1.0 map term. Every variant of
/// `Message` is encoded losslessly (no `innermost_simple()` collapse,
/// no Meta-rejection error path). See module docs.
pub(crate) fn encode_message<'a>(env: Env<'a>, m: &Message) -> NifResult<Term<'a>> {
    match m {
        Message::Simple { .. } => encode_simple(env, m),
        Message::Wrapped {
            wrapper,
            params,
            content,
        } => {
            let type_term = wrapped_atom(env).to_term(env);
            let wrapper_term = encode_wrapper_type(env, *wrapper);
            let params_term = encode_params(env, params)?;
            let inner_term = encode_message(env, content)?;
            make_map(
                env,
                &[
                    ("type", type_term),
                    ("wrapper", wrapper_term),
                    ("params", params_term),
                    ("inner", inner_term),
                ],
            )
        }
        Message::Dialect {
            dialect_name,
            inner,
        } => {
            let type_term = dialect_atom(env).to_term(env);
            // Dialect name is user-supplied — encode as a BINARY, not an
            // atom. See module docs for the atom-DoS rationale.
            let dialect_term = dialect_name.as_str().encode(env);
            let inner_term = encode_message(env, inner)?;
            make_map(
                env,
                &[
                    ("type", type_term),
                    ("dialect", dialect_term),
                    ("inner", inner_term),
                ],
            )
        }
        Message::Meta { dialect_def } => {
            let type_term = meta_atom(env).to_term(env);
            let def_term = encode_sexpr(env, dialect_def);
            make_map(
                env,
                &[("type", type_term), ("dialect_def", def_term)],
            )
        }
    }
}

/// Encode a `Message::Simple` as the historical CON-001 7-key map plus
/// the new `:type => simple` discriminator. Panics if `m` is not Simple.
fn encode_simple<'a>(env: Env<'a>, m: &Message) -> NifResult<Term<'a>> {
    let (performative, recipient, content, params, thread, sender, caused_by) = match m {
        Message::Simple {
            performative,
            recipient,
            content,
            params,
            thread,
            sender,
            caused_by,
        } => (performative, recipient, content, params, thread, sender, caused_by),
        _ => unreachable!("encode_simple invoked on non-Simple variant"),
    };

    let type_term = simple_atom(env).to_term(env);
    let perf_term = encode_performative(env, performative);
    let recipient_term = encode_optional_binary(env, recipient.as_deref());
    let content_term = encode_sexpr(env, content);
    let params_term = encode_params(env, params)?;
    let thread_term = encode_optional_binary(env, thread.as_deref());
    let sender_term = encode_optional_binary(env, sender.as_deref());
    let caused_by_term = encode_caused_by(env, caused_by.as_ref());

    make_map(
        env,
        &[
            ("type", type_term),
            ("performative", perf_term),
            ("recipient", recipient_term),
            ("content", content_term),
            ("params", params_term),
            ("thread", thread_term),
            ("sender", sender_term),
            ("caused_by", caused_by_term),
        ],
    )
}

fn encode_performative<'a>(env: Env<'a>, p: &Performative) -> Term<'a> {
    match p {
        Performative::Core(c) => core_performative_atom(env, *c).to_term(env),
        Performative::Custom(s) => tagged_binary(env, "custom", s),
    }
}

fn core_performative_atom(env: Env<'_>, c: CorePerformative) -> ErlAtom {
    // CorePerformative::as_str returns the canonical lowercase name.
    ErlAtom::from_str(env, c.as_str()).expect("core performative names are ASCII")
}

fn encode_optional_binary<'a>(env: Env<'a>, s: Option<&str>) -> Term<'a> {
    match s {
        Some(s) => s.encode(env),
        None => undefined_atom(env).to_term(env),
    }
}

fn undefined_atom(env: Env<'_>) -> ErlAtom {
    ErlAtom::from_str(env, "undefined").expect("'undefined' is ASCII")
}

/// Walk the flat `params: Vec<SExpr>` (alternating `:keyword` /
/// value items, REQ-013) into a list of `(key, value)` pairs. The
/// parser already validates `Simple` parameter pairing, but we are
/// defensive at the encoding boundary so we never panic on malformed
/// data — non-keyword entries and dangling keywords are dropped.
pub(crate) fn pair_keyword_params(params: &[SExpr]) -> Vec<(String, &SExpr)> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < params.len() {
        match &params[i] {
            SExpr::Atom(Atom::Keyword(k)) if i + 1 < params.len() => {
                out.push((k.clone(), &params[i + 1]));
                i += 2;
            }
            _ => i += 1,
        }
    }
    out
}

fn encode_params<'a>(env: Env<'a>, params: &[SExpr]) -> NifResult<Term<'a>> {
    let pairs = pair_keyword_params(params);
    let mut keys: Vec<Term<'a>> = Vec::with_capacity(pairs.len());
    let mut values: Vec<Term<'a>> = Vec::with_capacity(pairs.len());
    for (k, v) in pairs {
        // v0.1.0 deviation from CON-001 (`#{atom() => sexpr_term()}`):
        // user-supplied keyword names are encoded as BINARIES, not atoms.
        // BEAM atoms are not garbage-collected; allowing untrusted input
        // to mint new atoms is an atom-table exhaustion DoS — exactly
        // the trust-boundary risk REQ-005 / ADR-001 is built to mitigate.
        // BEAM-side consumers pattern-match `#{<<"thread">> := T}`.
        keys.push(k.as_str().encode(env));
        values.push(encode_sexpr(env, v));
    }
    Term::map_from_term_arrays(env, &keys, &values)
}

fn encode_caused_by<'a>(env: Env<'a>, cb: Option<&CausedBy>) -> Term<'a> {
    match cb {
        None => undefined_atom(env).to_term(env),
        Some(CausedBy::Begin) => ErlAtom::from_str(env, "begin")
            .expect("'begin' is ASCII")
            .to_term(env),
        Some(CausedBy::Single(h)) => {
            let v: Vec<Term<'a>> = vec![h.as_str().encode(env)];
            v.encode(env)
        }
        Some(CausedBy::Multiple(hs)) => {
            let v: Vec<Term<'a>> = hs.iter().map(|h| h.as_str().encode(env)).collect();
            v.encode(env)
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------
//
// IMPORTANT — rustler 0.36 + plain `cargo test`:
//
// The task description suggested `rustler::env::OwnedEnv::new().run(|env| …)`
// to obtain a test `Env<'a>`. The function exists, but on rustler 0.36.2 it
// goes through `enif_alloc_env`, which is loaded dynamically and aborts with
// `unreachable_unchecked` when called from a `cargo test` binary that is not
// hosted by `erl`. The sibling `verify_dialect` module documents the same
// finding and the chosen workaround: keep all env-free logic in pure helpers,
// test those, and exercise the BEAM-encoding path from an Erlang test runner
// against the loaded NIF.
//
// We split the tests accordingly:
//
//   - The first block (always-on) tests the env-free invariants:
//     `innermost_simple` unwraps wrappers, params-list pairing logic,
//     CausedBy variant routing (without actually building Erlang terms),
//     and Performative encoding choice (atom vs `{custom, _}`).
//
//   - The second block is `#[ignore]`d. It exercises the full term-building
//     path via `OwnedEnv` and requires running under a host that provides
//     `enif_alloc_env` (i.e. a BEAM-hosted test). Run with
//     `cargo test -p cbcl-erl -- --ignored` only if you have wired the NIF
//     into an Erlang test harness — otherwise these will SIGABRT.

#[cfg(test)]
mod tests {
    use super::*;
    use cbcl_core::message::{CausedBy, CorePerformative, Message, Performative, WrapperType};
    use cbcl_core::sexpr::{Atom, SExpr};
    // OwnedEnv-based tests are gated `#[ignore]` per the module docs above
    // (they SIGABRT outside `erl`). Imported here so the file compiles.
    use rustler::env::OwnedEnv;

    fn sym(s: &str) -> SExpr {
        SExpr::Atom(Atom::Symbol(s.into()))
    }
    fn kw(s: &str) -> SExpr {
        SExpr::Atom(Atom::Keyword(s.into()))
    }
    fn str_e(s: &str) -> SExpr {
        SExpr::Atom(Atom::Str(s.into()))
    }
    fn num(n: i64) -> SExpr {
        SExpr::Atom(Atom::Num(n))
    }
    fn list(xs: Vec<SExpr>) -> SExpr {
        SExpr::List(xs)
    }

    fn simple_msg(perf: Performative) -> Message {
        Message::Simple {
            performative: perf,
            recipient: Some("@bob".into()),
            content: str_e("hello"),
            params: vec![],
            thread: None,
            sender: None,
            caused_by: None,
        }
    }

    // -- Env-free tests (always run) ---------------------------------------
    //
    // These cover the encoder's structural decisions without crossing the
    // BEAM boundary: which atom name maps to which performative, how the
    // flat `params` list pairs up, how `innermost_simple` walks envelopes,
    // and which `CausedBy` discriminant the encoder will see.

    #[test]
    fn core_performative_atom_names() {
        // CorePerformative::as_str must produce the lowercase atom name we
        // commit to in CON-001 / encode_performative.
        for (c, name) in [
            (CorePerformative::Tell, "tell"),
            (CorePerformative::Ask, "ask"),
            (CorePerformative::Reply, "reply"),
            (CorePerformative::Error, "error"),
            (CorePerformative::Ok, "ok"),
            (CorePerformative::Cancel, "cancel"),
            (CorePerformative::Hello, "hello"),
            (CorePerformative::Bye, "bye"),
        ] {
            assert_eq!(c.as_str(), name);
        }
    }

    #[test]
    fn custom_performative_routes_via_custom_tag() {
        let p = Performative::Custom("propose-step".into());
        assert!(matches!(p, Performative::Custom(_)));
        assert_eq!(p.name(), "propose-step");
    }

    #[test]
    fn pair_keyword_params_pairs_alternating_kwargs() {
        // (... :timeout 30 :priority high)
        let params = vec![kw("timeout"), num(30), kw("priority"), sym("high")];
        let pairs = pair_keyword_params(&params);
        assert_eq!(pairs.len(), 2);
        assert_eq!(pairs[0].0, "timeout");
        assert_eq!(pairs[0].1, &num(30));
        assert_eq!(pairs[1].0, "priority");
        assert_eq!(pairs[1].1, &sym("high"));
    }

    #[test]
    fn pair_keyword_params_drops_dangling_and_non_keyword() {
        // Parser shouldn't produce these, but the encoder is defensive.
        let dangling = vec![kw("alone")]; // keyword without value
        assert!(pair_keyword_params(&dangling).is_empty());

        let leading_value = vec![num(7), kw("k"), num(8)];
        let pairs = pair_keyword_params(&leading_value);
        assert_eq!(pairs.len(), 1);
        assert_eq!(pairs[0].0, "k");
        assert_eq!(pairs[0].1, &num(8));
    }

    #[test]
    fn innermost_simple_unwraps_nested_wrappers() {
        let inner = Message::Simple {
            performative: Performative::Core(CorePerformative::Tell),
            recipient: Some("@bob".into()),
            content: str_e("hi"),
            params: vec![],
            thread: None,
            sender: None,
            caused_by: None,
        };
        let wrapped = Message::Wrapped {
            wrapper: WrapperType::Envelope,
            params: vec![kw("from"), sym("@alice")],
            content: Box::new(inner.clone()),
        };
        let dialect = Message::Dialect {
            dialect_name: "logistics".into(),
            inner: Box::new(wrapped.clone()),
        };
        assert_eq!(wrapped.innermost_simple(), Some(&inner));
        assert_eq!(dialect.innermost_simple(), Some(&inner));
    }

    #[test]
    fn meta_only_message_has_no_innermost_simple() {
        // Documents the trait-level behaviour. The encoder no longer
        // rejects Meta — it produces the meta map shape losslessly —
        // but `innermost_simple()` itself still returns None for Meta.
        let m = Message::Meta {
            dialect_def: list(vec![sym("define"), sym("test-dialect")]),
        };
        assert!(m.innermost_simple().is_none());
    }

    #[test]
    fn caused_by_variants_distinguishable() {
        let none: Option<&CausedBy> = None;
        assert!(none.is_none());
        assert!(matches!(Some(CausedBy::Begin).as_ref(), Some(CausedBy::Begin)));
        if let Some(CausedBy::Single(h)) =
            Some(CausedBy::Single("sha256:abc".into())).as_ref()
        {
            assert_eq!(h, "sha256:abc");
        } else {
            panic!("expected Single");
        }
        if let Some(CausedBy::Multiple(hs)) =
            Some(CausedBy::Multiple(vec!["a".into(), "b".into()])).as_ref()
        {
            assert_eq!(hs.len(), 2);
        } else {
            panic!("expected Multiple");
        }
    }

    #[test]
    fn simple_is_its_own_innermost() {
        let m = simple_msg(Performative::Core(CorePerformative::Tell));
        assert_eq!(m.innermost_simple(), Some(&m));
    }

    #[test]
    fn encode_message_dispatches_on_variant() {
        // Confirm the four arms of `encode_message` are exhaustive by
        // building one of each variant and pattern-matching it. The
        // for-loop list ensures every variant is reachable; if a new
        // variant is added to `Message`, the match arm below must grow,
        // which forces this test to be updated alongside the encoder.
        let inner = simple_msg(Performative::Core(CorePerformative::Tell));
        let messages = [
            simple_msg(Performative::Core(CorePerformative::Tell)),
            Message::Wrapped {
                wrapper: WrapperType::Envelope,
                params: vec![kw("from"), sym("@alice")],
                content: Box::new(inner.clone()),
            },
            Message::Dialect {
                dialect_name: "logistics".into(),
                inner: Box::new(inner.clone()),
            },
            Message::Meta {
                dialect_def: list(vec![sym("define"), sym("test-dialect")]),
            },
        ];
        let mut saw_simple = false;
        let mut saw_wrapped = false;
        let mut saw_dialect = false;
        let mut saw_meta = false;
        for m in &messages {
            match m {
                Message::Simple { .. } => saw_simple = true,
                Message::Wrapped { .. } => saw_wrapped = true,
                Message::Dialect { .. } => saw_dialect = true,
                Message::Meta { .. } => saw_meta = true,
            }
        }
        assert!(saw_simple && saw_wrapped && saw_dialect && saw_meta);
    }

    // -- Env-using tests (ignored — require BEAM host) ---------------------

    #[test]
    #[ignore = "requires BEAM host (enif_alloc_env); see module docs"]
    fn performative_atom_tell() {
        OwnedEnv::new().run(|env| {
            let m = simple_msg(Performative::Core(CorePerformative::Tell));
            let t = encode_message(env, &m).expect("encode ok");
            let perf_key = ErlAtom::from_str(env, "performative").unwrap().to_term(env);
            let perf = t.map_get(perf_key).expect("performative key present");
            assert!(perf.is_atom());
            assert_eq!(perf.atom_to_string().unwrap(), "tell");
        });
    }

    #[test]
    #[ignore = "requires BEAM host (enif_alloc_env); see module docs"]
    fn performative_atoms_ask_reply() {
        OwnedEnv::new().run(|env| {
            for (p, name) in [
                (CorePerformative::Ask, "ask"),
                (CorePerformative::Reply, "reply"),
                (CorePerformative::Ok, "ok"),
                (CorePerformative::Error, "error"),
            ] {
                let m = simple_msg(Performative::Core(p));
                let t = encode_message(env, &m).expect("encode ok");
                let perf_key = ErlAtom::from_str(env, "performative").unwrap().to_term(env);
                let perf = t.map_get(perf_key).expect("present");
                assert_eq!(perf.atom_to_string().unwrap(), name);
            }
        });
    }

    #[test]
    #[ignore = "requires BEAM host (enif_alloc_env); see module docs"]
    fn performative_custom_tagged_tuple() {
        OwnedEnv::new().run(|env| {
            let m = simple_msg(Performative::Custom("propose-step".into()));
            let t = encode_message(env, &m).expect("encode ok");
            let perf_key = ErlAtom::from_str(env, "performative").unwrap().to_term(env);
            let perf = t.map_get(perf_key).expect("present");
            assert!(perf.is_tuple());
            let parts: (ErlAtom, String) = perf.decode().expect("2-tuple");
            assert_eq!(parts.0.to_term(env).atom_to_string().unwrap(), "custom");
            assert_eq!(parts.1, "propose-step");
        });
    }

    #[test]
    #[ignore = "requires BEAM host (enif_alloc_env); see module docs"]
    fn sexpr_nesting_roundtrip() {
        // Represents `(a (b "c") :k)`
        let e = list(vec![sym("a"), list(vec![sym("b"), str_e("c")]), kw("k")]);
        OwnedEnv::new().run(|env| {
            let t = encode_sexpr(env, &e);
            assert!(t.is_list());

            // Decode back as a 3-element BEAM list.
            let v: Vec<Term> = t.decode().expect("list");
            assert_eq!(v.len(), 3);

            // First element: {symbol, <<"a">>}
            let (tag, name): (ErlAtom, String) = v[0].decode().expect("tagged tuple");
            assert_eq!(tag.to_term(env).atom_to_string().unwrap(), "symbol");
            assert_eq!(name, "a");

            // Second element: list [{symbol, <<"b">>}, <<"c">>]
            let inner: Vec<Term> = v[1].decode().expect("inner list");
            assert_eq!(inner.len(), 2);
            let (tag2, name2): (ErlAtom, String) = inner[0].decode().expect("tagged tuple");
            assert_eq!(tag2.to_term(env).atom_to_string().unwrap(), "symbol");
            assert_eq!(name2, "b");
            // Bare binary for Atom::Str
            assert!(inner[1].is_binary());
            let s: String = inner[1].decode().expect("binary->String");
            assert_eq!(s, "c");

            // Third element: {keyword, <<"k">>}
            let (tag3, name3): (ErlAtom, String) = v[2].decode().expect("tagged tuple");
            assert_eq!(tag3.to_term(env).atom_to_string().unwrap(), "keyword");
            assert_eq!(name3, "k");
        });
    }

    #[test]
    #[ignore = "requires BEAM host (enif_alloc_env); see module docs"]
    fn sexpr_num_and_bool() {
        OwnedEnv::new().run(|env| {
            let t = encode_sexpr(env, &num(42));
            assert_eq!(t.decode::<i64>().unwrap(), 42);

            let t2 = encode_sexpr(env, &SExpr::Atom(Atom::Bool(true)));
            assert!(t2.is_atom());
            assert_eq!(t2.atom_to_string().unwrap(), "true");
        });
    }

    fn caused_by_term<'a>(env: Env<'a>, m: &Message) -> Term<'a> {
        let t = encode_message(env, m).expect("encode ok");
        let key = ErlAtom::from_str(env, "caused_by").unwrap().to_term(env);
        t.map_get(key).expect("caused_by present")
    }

    #[test]
    #[ignore = "requires BEAM host (enif_alloc_env); see module docs"]
    fn caused_by_none_is_undefined_atom() {
        OwnedEnv::new().run(|env| {
            let m = simple_msg(Performative::Core(CorePerformative::Tell));
            let cb = caused_by_term(env, &m);
            assert!(cb.is_atom());
            assert_eq!(cb.atom_to_string().unwrap(), "undefined");
        });
    }

    #[test]
    #[ignore = "requires BEAM host (enif_alloc_env); see module docs"]
    fn caused_by_begin_is_atom() {
        OwnedEnv::new().run(|env| {
            let mut m = simple_msg(Performative::Core(CorePerformative::Tell));
            if let Message::Simple { caused_by, .. } = &mut m {
                *caused_by = Some(CausedBy::Begin);
            }
            let cb = caused_by_term(env, &m);
            assert!(cb.is_atom());
            assert_eq!(cb.atom_to_string().unwrap(), "begin");
        });
    }

    #[test]
    #[ignore = "requires BEAM host (enif_alloc_env); see module docs"]
    fn caused_by_single_is_one_element_list() {
        OwnedEnv::new().run(|env| {
            let mut m = simple_msg(Performative::Core(CorePerformative::Reply));
            if let Message::Simple { caused_by, .. } = &mut m {
                *caused_by = Some(CausedBy::Single("sha256:abc".into()));
            }
            let cb = caused_by_term(env, &m);
            assert!(cb.is_list());
            let v: Vec<String> = cb.decode().expect("list of binaries");
            assert_eq!(v, vec!["sha256:abc".to_string()]);
        });
    }

    #[test]
    #[ignore = "requires BEAM host (enif_alloc_env); see module docs"]
    fn caused_by_multiple_is_list() {
        OwnedEnv::new().run(|env| {
            let mut m = simple_msg(Performative::Core(CorePerformative::Ok));
            if let Message::Simple { caused_by, .. } = &mut m {
                *caused_by = Some(CausedBy::Multiple(vec!["aaa".into(), "bbb".into()]));
            }
            let cb = caused_by_term(env, &m);
            assert!(cb.is_list());
            let v: Vec<String> = cb.decode().expect("list of binaries");
            assert_eq!(v, vec!["aaa".to_string(), "bbb".to_string()]);
        });
    }

    #[test]
    #[ignore = "requires BEAM host (enif_alloc_env); see module docs"]
    fn simple_message_carries_type_simple() {
        OwnedEnv::new().run(|env| {
            let m = simple_msg(Performative::Core(CorePerformative::Tell));
            let t = encode_message(env, &m).expect("encode ok");
            let type_key = ErlAtom::from_str(env, "type").unwrap().to_term(env);
            let ty = t.map_get(type_key).expect(":type key present");
            assert!(ty.is_atom());
            assert_eq!(ty.atom_to_string().unwrap(), "simple");
        });
    }

    #[test]
    #[ignore = "requires BEAM host (enif_alloc_env); see module docs"]
    fn wrapped_message_preserves_wrapper_type_and_params() {
        // (envelope :from @alice (tell @bob "hi"))
        // Asserts:
        //   - :type   => :wrapped
        //   - :wrapper => :envelope
        //   - :params  has binary key <<"from">> (NOT atom — atom-DoS fix)
        //   - :inner.:type => :simple, with the embedded (tell @bob "hi")
        OwnedEnv::new().run(|env| {
            let inner = Message::Simple {
                performative: Performative::Core(CorePerformative::Tell),
                recipient: Some("@bob".into()),
                content: str_e("hi"),
                params: vec![],
                thread: None,
                sender: None,
                caused_by: None,
            };
            let wrapped = Message::Wrapped {
                wrapper: WrapperType::Envelope,
                params: vec![kw("from"), sym("@alice")],
                content: Box::new(inner),
            };
            let t = encode_message(env, &wrapped).expect("encode ok");

            let type_key = ErlAtom::from_str(env, "type").unwrap().to_term(env);
            let ty = t.map_get(type_key).unwrap();
            assert_eq!(ty.atom_to_string().unwrap(), "wrapped");

            let wrapper_key = ErlAtom::from_str(env, "wrapper").unwrap().to_term(env);
            let wrapper = t.map_get(wrapper_key).unwrap();
            assert_eq!(wrapper.atom_to_string().unwrap(), "envelope");

            let params_key = ErlAtom::from_str(env, "params").unwrap().to_term(env);
            let params = t.map_get(params_key).expect("params present");
            assert!(params.is_map());
            // BINARY key (atom-DoS fix), NOT atom.
            let bin_key = "from".encode(env);
            let v = params.map_get(bin_key).expect("binary key <<\"from\">>");
            // value is {symbol, <<"@alice">>}
            let (tag, name): (ErlAtom, String) = v.decode().expect("tagged tuple");
            assert_eq!(tag.to_term(env).atom_to_string().unwrap(), "symbol");
            assert_eq!(name, "@alice");
            // And confirm an atom key would NOT match (atom-DoS regression).
            let atom_key = ErlAtom::from_str(env, "from").unwrap().to_term(env);
            assert!(
                params.map_get(atom_key).is_err(),
                "atom keys must not be present (atom-DoS fix)"
            );

            let inner_key = ErlAtom::from_str(env, "inner").unwrap().to_term(env);
            let inner = t.map_get(inner_key).expect("inner present");
            assert!(inner.is_map());
            let inner_type = inner.map_get(type_key).unwrap();
            assert_eq!(inner_type.atom_to_string().unwrap(), "simple");
            let perf_key = ErlAtom::from_str(env, "performative").unwrap().to_term(env);
            let perf = inner.map_get(perf_key).unwrap();
            assert_eq!(perf.atom_to_string().unwrap(), "tell");
        });
    }

    #[test]
    #[ignore = "requires BEAM host (enif_alloc_env); see module docs"]
    fn dialect_message_preserves_dialect_name() {
        // (lang logistics (tell @bob "hi"))
        // Asserts :dialect => <<"logistics">> (BINARY, NOT atom — atom-DoS fix).
        OwnedEnv::new().run(|env| {
            let inner = simple_msg(Performative::Core(CorePerformative::Tell));
            let dialect = Message::Dialect {
                dialect_name: "logistics".into(),
                inner: Box::new(inner),
            };
            let t = encode_message(env, &dialect).expect("encode ok");

            let type_key = ErlAtom::from_str(env, "type").unwrap().to_term(env);
            let ty = t.map_get(type_key).unwrap();
            assert_eq!(ty.atom_to_string().unwrap(), "dialect");

            let dialect_key = ErlAtom::from_str(env, "dialect").unwrap().to_term(env);
            let name = t.map_get(dialect_key).unwrap();
            assert!(name.is_binary(), "dialect name must be a binary, not an atom");
            let s: String = name.decode().expect("binary->String");
            assert_eq!(s, "logistics");

            let inner_key = ErlAtom::from_str(env, "inner").unwrap().to_term(env);
            let inner = t.map_get(inner_key).expect("inner present");
            assert!(inner.is_map());
            let inner_type = inner.map_get(type_key).unwrap();
            assert_eq!(inner_type.atom_to_string().unwrap(), "simple");
        });
    }

    #[test]
    #[ignore = "requires BEAM host (enif_alloc_env); see module docs"]
    fn meta_message_encodes_dialect_def() {
        // (meta (define test-dialect))
        // Asserts :type => :meta and :dialect_def is a list-shaped term
        // (the encoded SExpr).
        OwnedEnv::new().run(|env| {
            let m = Message::Meta {
                dialect_def: list(vec![sym("define"), sym("test-dialect")]),
            };
            let t = encode_message(env, &m).expect("encode ok");

            let type_key = ErlAtom::from_str(env, "type").unwrap().to_term(env);
            let ty = t.map_get(type_key).unwrap();
            assert_eq!(ty.atom_to_string().unwrap(), "meta");

            let def_key = ErlAtom::from_str(env, "dialect_def").unwrap().to_term(env);
            let def = t.map_get(def_key).expect("dialect_def present");
            assert!(def.is_list(), "dialect_def must be a list (encoded SExpr)");
            let v: Vec<Term> = def.decode().expect("list");
            assert_eq!(v.len(), 2);
            // First element: {symbol, <<"define">>}
            let (tag, name): (ErlAtom, String) =
                v[0].decode().expect("tagged tuple");
            assert_eq!(tag.to_term(env).atom_to_string().unwrap(), "symbol");
            assert_eq!(name, "define");
        });
    }

    #[test]
    #[ignore = "requires BEAM host (enif_alloc_env); see module docs"]
    fn meta_only_message_encodes_to_meta_map() {
        // Replaces the previous `meta_only_message_returns_message_error`
        // test. Meta is now encoded losslessly — the previous error path
        // ("non-simple message at innermost layer") is gone.
        OwnedEnv::new().run(|env| {
            let m = Message::Meta {
                dialect_def: list(vec![sym("define"), sym("test-dialect")]),
            };
            let t = encode_message(env, &m).expect("meta now encodes losslessly");
            assert!(t.is_map());
            let type_key = ErlAtom::from_str(env, "type").unwrap().to_term(env);
            let ty = t.map_get(type_key).unwrap();
            assert_eq!(ty.atom_to_string().unwrap(), "meta");
        });
    }

    #[test]
    #[ignore = "requires BEAM host (enif_alloc_env); see module docs"]
    fn nested_dialect_wrapped_simple_round_trips_through_encoder() {
        // (lang logistics (envelope :from @alice (tell @bob "hi")))
        // The encoder should produce three nested maps:
        //   :type=>:dialect (:dialect=><<"logistics">>, :inner=>...)
        //   :type=>:wrapped (:wrapper=>:envelope, :params=>#{<<"from">>...},
        //                    :inner=>...)
        //   :type=>:simple  (:performative=>:tell, ...)
        OwnedEnv::new().run(|env| {
            let leaf = Message::Simple {
                performative: Performative::Core(CorePerformative::Tell),
                recipient: Some("@bob".into()),
                content: str_e("hi"),
                params: vec![],
                thread: None,
                sender: None,
                caused_by: None,
            };
            let wrapped = Message::Wrapped {
                wrapper: WrapperType::Envelope,
                params: vec![kw("from"), sym("@alice")],
                content: Box::new(leaf),
            };
            let dialect = Message::Dialect {
                dialect_name: "logistics".into(),
                inner: Box::new(wrapped),
            };
            let t = encode_message(env, &dialect).expect("encode ok");

            let type_key = ErlAtom::from_str(env, "type").unwrap().to_term(env);
            let inner_key = ErlAtom::from_str(env, "inner").unwrap().to_term(env);
            assert_eq!(
                t.map_get(type_key).unwrap().atom_to_string().unwrap(),
                "dialect"
            );
            let mid = t.map_get(inner_key).expect("dialect inner present");
            assert_eq!(
                mid.map_get(type_key).unwrap().atom_to_string().unwrap(),
                "wrapped"
            );
            let leaf_t = mid.map_get(inner_key).expect("wrapped inner present");
            assert_eq!(
                leaf_t.map_get(type_key).unwrap().atom_to_string().unwrap(),
                "simple"
            );
            // Recipient survives the nesting.
            let rec_key = ErlAtom::from_str(env, "recipient").unwrap().to_term(env);
            let rec: String = leaf_t.map_get(rec_key).unwrap().decode().unwrap();
            assert_eq!(rec, "@bob");
        });
    }

    #[test]
    #[ignore = "requires BEAM host (enif_alloc_env); see module docs"]
    fn wrapper_type_atoms_signed_and_with_limits() {
        // Closed-enum atom set: envelope / signed / with_limits.
        // (Note: WrapperType::WithLimits canonical text name is "with-limits"
        // but the atom uses an underscore — atoms cannot carry hyphens
        // unquoted.)
        OwnedEnv::new().run(|env| {
            let leaf = simple_msg(Performative::Core(CorePerformative::Tell));
            for (w, name) in [
                (WrapperType::Signed, "signed"),
                (WrapperType::WithLimits, "with_limits"),
            ] {
                let m = Message::Wrapped {
                    wrapper: w,
                    params: vec![],
                    content: Box::new(leaf.clone()),
                };
                let t = encode_message(env, &m).expect("encode ok");
                let wrapper_key =
                    ErlAtom::from_str(env, "wrapper").unwrap().to_term(env);
                let wrapper = t.map_get(wrapper_key).unwrap();
                assert!(wrapper.is_atom());
                assert_eq!(wrapper.atom_to_string().unwrap(), name);
            }
        });
    }

    #[test]
    #[ignore = "requires BEAM host (enif_alloc_env); see module docs"]
    fn params_use_binary_keys_not_atoms() {
        // Regression test for the atom-DoS fix (REQ-005 / ADR-001).
        // BEAM atoms are not GC'd; user-supplied param keys MUST be
        // encoded as binaries, not atoms.
        OwnedEnv::new().run(|env| {
            let m = Message::Simple {
                performative: Performative::Core(CorePerformative::Ask),
                recipient: Some("@alice".into()),
                content: str_e("What?"),
                params: vec![kw("timeout"), num(30)],
                thread: None,
                sender: None,
                caused_by: None,
            };
            let t = encode_message(env, &m).expect("encode ok");
            let params_key = ErlAtom::from_str(env, "params").unwrap().to_term(env);
            let params = t.map_get(params_key).expect("params present");
            assert!(params.is_map());

            // BINARY key succeeds.
            let bin_key = "timeout".encode(env);
            let v = params.map_get(bin_key).expect("binary key works");
            assert_eq!(v.decode::<i64>().unwrap(), 30);

            // ATOM key FAILS — the regression check.
            let atom_key = ErlAtom::from_str(env, "timeout").unwrap().to_term(env);
            assert!(
                params.map_get(atom_key).is_err(),
                "atom-keyed lookup must fail; param keys are binaries to \
                 prevent atom-table exhaustion DoS"
            );
        });
    }
}
