//! SPEC-035 ADR-3503: one LWW family and immutable opener fields.
use cbcl_core::sexpr::{Atom, SExpr};
use cbcl_core::state::{fold, render_json, Act};
use cbcl_parser::{parse, parse_dialect, parse_message};

const INITIAL: &str = "(define init-test (cbcl) @a (extend open (to title) (tell to :title title)) (extend write (to title) (tell to :title title)) (shape open (require :title string)) (shape write (require :title string)) (protocol (then begin open) (then open write)) (state (title (initial open :title))))";

#[test]
fn retired_heads_are_rejected_not_aliased() {
    for rule in [
        "(last open :title)",
        "(latest-per-signer write :title)",
        "(latest-per-key write :title :title)",
        "(register-per-key write :title :title)",
    ] {
        let text = INITIAL.replace("(initial open :title)", rule);
        assert!(parse_dialect(&parse(&text).unwrap()).is_err(), "{rule}");
    }
}

#[test]
fn initial_is_opener_only_and_has_no_hash_winner() {
    let d = parse_dialect(&parse(INITIAL).unwrap()).unwrap();
    assert!(cbcl_core::r7::r7_violations(&d).is_empty());
    let wrong =
        parse_dialect(&parse(&INITIAL.replace("initial open", "initial write")).unwrap()).unwrap();
    assert!(!cbcl_core::r7::r7_violations(&wrong).is_empty());
    let act = |value: &str| {
        Act::from_message(
            parse_message(
                &parse(
                    &format!(
        "(lang init-test (open @a :title \"{value}\" :from @a :thread \"t\" :caused-by begin))"),
                )
                .unwrap(),
            )
            .unwrap(),
            "@a",
        )
        .unwrap()
    };
    let a = act("first");
    let b = act("other");
    let observe = |acts: &[Act]| {
        render_json(&fold(
            d.state.as_ref().unwrap(),
            d.causal_protocol.as_ref(),
            acts,
        ))
    };
    assert_eq!(observe(&[]), "{\"title\":null}");
    assert_eq!(observe(&[a.clone()]), "{\"title\":\"first\"}");
    assert_eq!(observe(&[a.clone(), a.clone()]), "{\"title\":\"first\"}");
    assert_eq!(observe(&[a.clone(), b.clone()]), "{\"title\":null}");
    assert_eq!(observe(&[b, a]), "{\"title\":null}");
    let missing = Act::from_message(
        parse_message(
            &parse("(lang init-test (open @a :from @a :thread \"t\" :caused-by begin))").unwrap(),
        )
        .unwrap(),
        "@a",
    )
    .unwrap();
    assert_eq!(
        observe(&[act("first"), missing]),
        "{\"title\":null}",
        "candidate count must not depend on payload presence"
    );
}

/// Explicit, one-off authoring of changed signed fixture bodies and references.
/// Run before STATE_CORPUS_WRITE; never part of normal validation.
#[test]
#[ignore = "author version-4 fixtures after editing their contract and explicit clock inputs"]
fn migrate_clock_fixture_bodies() {
    use std::collections::BTreeMap;
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../test-vectors/state");
    fn prepare(s: &mut SExpr, verbs: &[String]) {
        if let SExpr::List(items) = s {
            let writer = matches!(items.first(), Some(SExpr::Atom(Atom::Symbol(head))) if verbs.contains(head));
            if writer {
                if !items
                    .iter()
                    .any(|x| matches!(x, SExpr::Atom(Atom::Keyword(k)) if k == "clock"))
                {
                    items.push(SExpr::Atom(Atom::Keyword("clock".into())));
                    items.push(SExpr::Atom(Atom::Str(
                        "hlc-0000000000000000-00000000".into(),
                    )));
                }
                if !items
                    .iter()
                    .any(|x| matches!(x, SExpr::Atom(Atom::Keyword(k)) if k == "replaces"))
                {
                    items.push(SExpr::Atom(Atom::Keyword("replaces".into())));
                    items.push(SExpr::List(vec![]));
                }
            }
            for item in items {
                prepare(item, verbs);
            }
        }
    }
    fn references(s: &mut SExpr, map: &BTreeMap<String, String>) {
        match s {
            SExpr::List(xs) => {
                for x in xs {
                    references(x, map);
                }
            }
            SExpr::Atom(Atom::Symbol(x)) | SExpr::Atom(Atom::Str(x)) => {
                if let Some(y) = map.get(x) {
                    *x = y.clone();
                }
            }
            _ => {}
        }
    }
    for path in std::fs::read_dir(dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == "json"))
    {
        let mut vector: serde_json::Value =
            serde_json::from_str(&std::fs::read_to_string(&path).unwrap()).unwrap();
        let Some(verbs) = vector
            .as_object_mut()
            .unwrap()
            .remove("_migrate_clock_verbs")
        else {
            continue;
        };
        let verbs: Vec<String> = serde_json::from_value(verbs).unwrap();
        if !verbs.is_empty() {
            let messages = vector["messages"].as_array_mut().unwrap();
            let mut prepared = Vec::new();
            for message in messages.iter() {
                let mut sexpr = parse(message["canonical"].as_str().unwrap()).unwrap();
                let old = Act::from_message(
                    parse_message(&sexpr).unwrap(),
                    message["signer"].as_str().unwrap(),
                )
                .unwrap()
                .address;
                prepare(&mut sexpr, &verbs);
                prepared.push((old, sexpr));
            }
            let mut mapping = BTreeMap::new();
            let mut texts = Vec::new();
            let mut complete = false;
            for _ in 0..100 {
                let mut next = BTreeMap::new();
                texts.clear();
                for (index, (old, base)) in prepared.iter().enumerate() {
                    let mut sexpr = base.clone();
                    references(&mut sexpr, &mapping);
                    let message = parse_message(&sexpr).unwrap();
                    let act = Act::from_message(
                        message.clone(),
                        messages[index]["signer"].as_str().unwrap(),
                    )
                    .unwrap();
                    next.insert(old.clone(), act.address);
                    texts.push(cbcl_core::intend::canonical_text(&message));
                }
                if next == mapping {
                    complete = true;
                    break;
                }
                mapping = next;
            }
            assert!(
                complete,
                "cyclic fixture references require explicit re-authoring: {}",
                path.display()
            );
            for (message, text) in messages.iter_mut().zip(texts) {
                message["canonical"] = text.into();
            }
        }
        std::fs::write(path, serde_json::to_string_pretty(&vector).unwrap() + "\n").unwrap();
    }
}

#[test]
fn retired_json_ops_are_rejected() {
    for op in ["last", "latestPerSigner", "latestPerKey", "registerPerKey"] {
        let contract = serde_json::json!({"version":3,"kind":"contract","name":"retired",
            "verbs":{"open":{"after":["begin"],"fields":{"title":"string"}}},
            "state":{"title":[op,"open","title"]}});
        assert!(
            cbcl_parser::compile_contract_str(&contract.to_string()).is_err(),
            "{op}"
        );
    }
}
