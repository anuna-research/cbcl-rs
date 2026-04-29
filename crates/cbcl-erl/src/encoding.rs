//! SExpr/Message → BEAM term encoders for the CBCL NIF binding.
//!
//! Implements SPEC-009 CON-001 — the Erlang term shape that
//! `cbcl_erl:parse_message/1` (and the lax/dialect siblings) returns.
//!
//! # CON-001 message map shape (atom keys)
//!
//! ```text
//! #{ performative := atom()
//!  , recipient    := binary() | undefined
//!  , content      := sexpr_term()
//!  , params       := #{atom() => sexpr_term()}
//!  , thread       := binary() | undefined
//!  , sender       := binary() | undefined
//!  , caused_by    := undefined | begin | [binary()]
//!  }
//! ```
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
//! children.
//!
//! # Performative encoding
//!
//! - `Performative::Core(c)` → atom (`tell`, `ask`, `reply`, …) using
//!   `CorePerformative::as_str()` (already lowercase ASCII).
//! - `Performative::Custom(s)` → `{custom, <<"s">>}` (tagged 2-tuple
//!   so BEAM-side pattern matches stay sharp).
//!
//! # Non-Simple messages
//!
//! CON-001 only describes the Simple shape. `encode_message` walks
//! `Wrapped` / `Dialect` envelopes via `Message::innermost_simple()`.
//! If the innermost layer is `Meta` (no Simple at the bottom) we
//! return `Err(Error::Term(...))` carrying the tagged tuple
//! `{message_error, <<"non-simple message at innermost layer">>}`.
//! The `parse_message` NIF wrapper (a separate task) translates this
//! into the user-facing `<<"message error: ...">>` binary.

use cbcl_core::message::{CausedBy, CorePerformative, Message, Performative};
use cbcl_core::sexpr::{Atom, SExpr};
use rustler::types::atom::Atom as ErlAtom;
use rustler::{Encoder, Env, Error, NifResult, Term};

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

/// Build a `{Tag, <<"Bin">>}` 2-tuple, where `Tag` is an atom.
fn tagged_binary<'a>(env: Env<'a>, tag: &str, bin: &str) -> Term<'a> {
    let tag_atom = ErlAtom::from_str(env, tag).expect("static ASCII tag fits in an atom");
    (tag_atom, bin).encode(env)
}

/// Encode a `Message` as a CON-001 map term. Walks through Wrapped /
/// Dialect envelopes to the innermost Simple. Returns `Error::Term`
/// if no Simple layer exists (e.g. a Meta-only message).
pub(crate) fn encode_message<'a>(env: Env<'a>, m: &Message) -> NifResult<Term<'a>> {
    let inner = m.innermost_simple().ok_or_else(|| {
        let tag = ErlAtom::from_str(env, "message_error")
            .expect("static ASCII tag fits in an atom");
        // Box::new on a (Atom, &'static str) tuple — both are Encoder.
        Error::Term(Box::new((
            tag,
            "non-simple message at innermost layer".to_string(),
        )))
    })?;

    // innermost_simple returns Some only for Simple variants.
    let (performative, recipient, content, params, thread, sender, caused_by) = match inner {
        Message::Simple {
            performative,
            recipient,
            content,
            params,
            thread,
            sender,
            caused_by,
        } => (performative, recipient, content, params, thread, sender, caused_by),
        _ => unreachable!("innermost_simple returns Some only for Simple"),
    };

    let perf_term = encode_performative(env, performative);
    let recipient_term = encode_optional_binary(env, recipient.as_deref());
    let content_term = encode_sexpr(env, content);
    let params_term = encode_params(env, params)?;
    let thread_term = encode_optional_binary(env, thread.as_deref());
    let sender_term = encode_optional_binary(env, sender.as_deref());
    let caused_by_term = encode_caused_by(env, caused_by.as_ref());

    let key = |s: &str| -> Term<'a> {
        ErlAtom::from_str(env, s)
            .expect("CON-001 key fits in an atom")
            .to_term(env)
    };

    let keys = [
        key("performative"),
        key("recipient"),
        key("content"),
        key("params"),
        key("thread"),
        key("sender"),
        key("caused_by"),
    ];
    let values = [
        perf_term,
        recipient_term,
        content_term,
        params_term,
        thread_term,
        sender_term,
        caused_by_term,
    ];

    Term::map_from_term_arrays(env, &keys, &values)
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
        let key = ErlAtom::from_str(env, &k).map_err(|_| {
            Error::Term(Box::new(format!("param key not encodable as atom: {k}")))
        })?;
        keys.push(key.to_term(env));
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
        // The encoder maps `None` here onto Error::Term(message_error,…).
        // Building the term requires an Env, but the None branch is env-free.
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
    fn innermost_simple_unwraps_envelope() {
        // (envelope :from @alice (tell @bob "hi"))
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
            // Ensure the encoded term is the inner Simple — performative
            // is `tell` and recipient is <<"@bob">>.
            let perf_key = ErlAtom::from_str(env, "performative").unwrap().to_term(env);
            let perf = t.map_get(perf_key).unwrap();
            assert_eq!(perf.atom_to_string().unwrap(), "tell");
            let rec_key = ErlAtom::from_str(env, "recipient").unwrap().to_term(env);
            let rec = t.map_get(rec_key).unwrap();
            let s: String = rec.decode().unwrap();
            assert_eq!(s, "@bob");
        });
    }

    #[test]
    #[ignore = "requires BEAM host (enif_alloc_env); see module docs"]
    fn meta_only_message_returns_message_error() {
        OwnedEnv::new().run(|env| {
            let m = Message::Meta {
                dialect_def: list(vec![sym("define"), sym("test-dialect")]),
            };
            let res = encode_message(env, &m);
            let err = res.expect_err("meta has no innermost simple");
            // Error::Term should hold our tagged tuple. We can confirm
            // by encoding it back to a term and matching the shape.
            let term = match err {
                Error::Term(boxed) => boxed.encode(env),
                other => panic!("expected Error::Term, got {other:?}"),
            };
            assert!(term.is_tuple());
            let (tag, msg): (ErlAtom, String) = term.decode().expect("2-tuple");
            assert_eq!(tag.to_term(env).atom_to_string().unwrap(), "message_error");
            assert!(msg.contains("non-simple"));
        });
    }

    #[test]
    #[ignore = "requires BEAM host (enif_alloc_env); see module docs"]
    fn params_become_atom_keyed_map() {
        OwnedEnv::new().run(|env| {
            // (ask @alice "What?" :timeout 30)
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
            let timeout_key = ErlAtom::from_str(env, "timeout").unwrap().to_term(env);
            let v = params.map_get(timeout_key).expect("timeout key");
            assert_eq!(v.decode::<i64>().unwrap(), 30);
        });
    }
}
