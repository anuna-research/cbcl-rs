//! SPEC-019 state layer: end-to-end through the real parser.
//!
//! TEST-1900/1907 (clause and reserved field), TEST-1910/1927 (install and
//! self-address), TEST-1915–1917 (fold on the worked trace), TEST-1922/1923
//! (binding with a cast), TEST-1924 (domain refusal), TEST-1929 (may_send).

use cbcl_core::canonical::dialect_name;
use cbcl_core::dialect::{DialectInstallError, DialectRegistry};
use cbcl_core::intend::{intend, may_send, roles_of, Instance, Reject};
use cbcl_core::message::Message;
use cbcl_core::r7::{r7_violations, verify_state_shape, R7Violation};
use cbcl_core::role::AgentKey;
use cbcl_core::sexpr::{Atom, SExpr};
use cbcl_core::state::{fold, frontier, render_json, state_schema, Act};
use cbcl_core::store::ThreadId;
use cbcl_parser::{parse, parse_dialect, parse_message};
use std::collections::BTreeMap;

fn checklist_source() -> String {
    let src = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../dialects/checklist.cbcl"
    ))
    .unwrap();
    src.lines()
        .filter(|l| !l.trim_start().starts_with(';'))
        .collect::<Vec<_>>()
        .join("\n")
}

fn lunch_vote_source() -> String {
    let src = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../dialects/lunch-vote.cbcl"
    ))
    .unwrap();
    src.lines()
        .filter(|l| !l.trim_start().starts_with(';'))
        .collect::<Vec<_>>()
        .join("\n")
}

fn dialect(src: &str) -> cbcl_core::dialect::Dialect {
    parse_dialect(&parse(src).unwrap()).unwrap()
}

fn msg(text: &str) -> Message {
    parse_message(&parse(text).unwrap()).unwrap()
}

fn act(text: &str, signer: &str) -> Act {
    Act::from_message(msg(text), signer).unwrap()
}

fn fields(pairs: &[(&str, SExpr)]) -> BTreeMap<String, SExpr> {
    pairs
        .iter()
        .map(|(k, v)| (String::from(*k), v.clone()))
        .collect()
}

fn s(x: &str) -> SExpr {
    SExpr::Atom(Atom::Str(String::from(x)))
}
fn b(x: bool) -> SExpr {
    SExpr::Atom(Atom::Bool(x))
}

// ---------------------------------------------------------------------------
// TEST-1900 / TEST-1907: the clause parses and :replaces is inserted
// ---------------------------------------------------------------------------

#[test]
fn checklist_parses_and_replaces_is_inserted() {
    let d = dialect(&checklist_source());
    let clause = d.state.as_ref().expect("state clause");
    assert_eq!(clause.fields().count(), 2);
    for verb in ["check", "drop"] {
        let kws = cbcl_core::r7::declared_keywords(&d.shapes, verb);
        assert!(
            kws.contains("replaces"),
            "{verb} must carry :replaces: {kws:?}"
        );
    }
    assert!(!cbcl_core::r7::declared_keywords(&d.shapes, "open").contains("replaces"));
    assert!(r7_violations(&d).is_empty(), "{:?}", r7_violations(&d));
}

#[test]
fn author_declared_replaces_is_rejected() {
    let src = checklist_source().replace(
        "(require :done bool))",
        "(require :done bool) (require :replaces list))",
    );
    let err = parse_dialect(&parse(&src).unwrap()).unwrap_err();
    assert!(err.contains("reserved"), "{err}");
}

#[test]
fn unknown_rule_and_bad_domain_fail_install() {
    let src = checklist_source().replace("(last open :title)", "(newest open :title)");
    assert!(parse_dialect(&parse(&src).unwrap()).is_err());
    let src = lunch_vote_source().replace(
        "(domain vote :choice options)",
        "(domain vote :choice question)",
    );
    let d = dialect(&src);
    let v = r7_violations(&d);
    assert!(
        v.iter().any(|x| matches!(x, R7Violation::Domain(_))),
        "{v:?}"
    );
}

// ---------------------------------------------------------------------------
// TEST-1910 / TEST-1927: install and self-address
// ---------------------------------------------------------------------------

#[test]
fn install_accepts_author_name_and_checks_claimed_self_address() {
    let d = dialect(&checklist_source());
    let mut reg = DialectRegistry::new();
    reg.install(d.clone())
        .expect("author-named state dialect installs");

    let name = dialect_name(&d);
    assert!(name.starts_with("sha256-") && name.len() == 7 + 64);
    let mut renamed = d.clone();
    renamed.name = name.clone();
    let mut reg = DialectRegistry::new();
    reg.install(renamed)
        .expect("self-addressed dialect installs");

    let mut wrong = d.clone();
    wrong.name = format!("sha256-{}", "0".repeat(64));
    let mut reg = DialectRegistry::new();
    match reg.install(wrong) {
        Err(DialectInstallError::R7Violation { violations, .. }) => {
            assert!(violations
                .iter()
                .any(|v| matches!(v, R7Violation::Name { .. })));
        }
        other => panic!("expected R7 name violation, got {other:?}"),
    }

    // Changing one rule changes the self-address.
    let src = checklist_source().replace(
        "(register-per-key check :item :done drop)",
        "(values-per-key check :item :done drop)",
    );
    assert_ne!(dialect_name(&dialect(&src)), name);
}

// ---------------------------------------------------------------------------
// TEST-1915–1917: the fold on the worked trace
// ---------------------------------------------------------------------------

/// The worked trace. Under R6 the thread's root is the cast-bearing
/// `hello` (SPEC-014 REQ-611, typed as `begin` by REQ-623); the opener
/// follows it. Index 0 is the root, 1 the opener, 2–4 the acts.
fn trace(d: &cbcl_core::dialect::Dialect) -> Vec<Act> {
    let n = &d.name;
    let m0 = act(
        "(with-roles ((owner @aria) (member @bo @cy)) (signed @aria (hello :thread \"list-1\" :caused-by begin)))",
        "@aria",
    );
    let a0 = m0.address.clone();
    let m1 = act(
        &format!("(signed @aria (lang {n} (open (@aria @bo @cy) :title \"Launch tasks\" :caused-by {a0} :thread \"list-1\" :from @aria)))"),
        "@aria",
    );
    let a1 = m1.address.clone();
    let m2 = act(
        &format!("(signed @bo (lang {n} (check (@aria @bo @cy) :item \"venue\" :done #f :replaces () :caused-by {a1} :thread \"list-1\" :from @bo)))"),
        "@bo",
    );
    let a2 = m2.address.clone();
    let m3 = act(
        &format!("(signed @bo (lang {n} (check (@aria @bo @cy) :item \"venue\" :done #t :replaces ({a2}) :caused-by {a1} :thread \"list-1\" :from @bo)))"),
        "@bo",
    );
    let a3 = m3.address.clone();
    let m4 = act(
        &format!("(signed @aria (lang {n} (drop (@aria @bo @cy) :item \"venue\" :replaces ({a3}) :caused-by {a1} :thread \"list-1\" :from @aria)))"),
        "@aria",
    );
    vec![m0, m1, m2, m3, m4]
}

#[test]
fn fold_matches_the_worked_trace_in_any_order() {
    let d = dialect(&checklist_source());
    let clause = d.state.as_ref().unwrap();
    let t = trace(&d);
    let p = d.causal_protocol.as_ref();
    let after3 = render_json(&fold(clause, p, &t[..4]));
    assert_eq!(
        after3,
        "{\"title\":\"Launch tasks\",\"items\":{\"venue\":true}}"
    );
    let after4 = render_json(&fold(clause, p, &t));
    assert_eq!(after4, "{\"title\":\"Launch tasks\",\"items\":{}}");
    let shuffled = vec![
        t[4].clone(),
        t[3].clone(),
        t[0].clone(),
        t[1].clone(),
        t[2].clone(),
        t[3].clone(),
    ];
    assert_eq!(render_json(&fold(clause, p, &shuffled)), after4);
    let missing_m2 = vec![t[0].clone(), t[1].clone(), t[3].clone(), t[4].clone()];
    assert_eq!(render_json(&fold(clause, p, &missing_m2)), after4);
    assert_eq!(frontier(&t[..4]), {
        let mut f = vec![t[2].address.clone(), t[3].address.clone()];
        f.sort();
        f
    });
    for a in &t {
        verify_state_shape(&d, &a.message).unwrap_or_else(|e| panic!("{}: {e}", a.verb));
    }
}

#[test]
fn state_shape_rejects_undeclared_and_oversized_fields() {
    let d = dialect(&checklist_source());
    let n = &d.name;
    let extra = msg(&format!("(lang {n} (check @x :item \"venue\" :done #t :note \"hi\" :caused-by begin :thread \"t\" :from @bo))"));
    assert!(verify_state_shape(&d, &extra)
        .unwrap_err()
        .rule
        .contains("closed"));
    let big = "x".repeat(2049);
    let oversized = msg(&format!(
        "(lang {n} (check @x :item \"{big}\" :done #t :caused-by begin :thread \"t\" :from @bo))"
    ));
    assert!(verify_state_shape(&d, &oversized)
        .unwrap_err()
        .rule
        .contains("size"));
    let bad_ref = msg(&format!("(lang {n} (drop @x :item \"venue\" :replaces (nope) :caused-by begin :thread \"t\" :from @bo))"));
    assert!(verify_state_shape(&d, &bad_ref)
        .unwrap_err()
        .rule
        .contains("replaces"));
    // A verb the clause does not name is unconstrained by R7.
    let other = msg("(tell @x \"hello\" :anything 1)");
    assert!(verify_state_shape(&d, &other).is_ok());
}

#[test]
fn state_schema_of_the_checklist() {
    let d = dialect(&checklist_source());
    let schema = state_schema(d.state.as_ref().unwrap(), &d.shapes);
    assert_eq!(
        cbcl_core::state::render_schema(&schema),
        "{\"title\":{\"type\":\"opt-scalar\",\"of\":\"string\"},\"items\":{\"type\":\"map\",\"key\":\"string\",\"value\":{\"type\":\"opt-scalar\",\"of\":\"bool\"}}}"
    );
}

// ---------------------------------------------------------------------------
// TEST-1922 / TEST-1923: the binder with a cast
// ---------------------------------------------------------------------------

#[test]
fn intend_binds_recipients_replaces_and_predecessor_from_the_cast_and_history() {
    let d = dialect(&checklist_source());
    let t = trace(&d);
    let inst = Instance::new(&d, ThreadId("list-1".into()), &t[..4]).unwrap();
    assert_eq!(inst.instance_id(), Some(t[1].address.as_str()));
    assert_eq!(
        inst.root.map(|r| r.address.as_str()),
        Some(t[0].address.as_str())
    );
    let cast = inst.cast.as_ref().expect("cast from the root wrapper");
    assert_eq!(
        roles_of(cast, &AgentKey("@bo".into())),
        vec![String::from("member")]
    );
    assert_eq!(
        roles_of(cast, &AgentKey("@aria".into())),
        vec![String::from("owner")]
    );

    let bo = AgentKey("@bo".into());
    let m = intend(
        &inst,
        &bo,
        "check",
        fields(&[("item", s("venue")), ("done", b(false))]),
    )
    .expect("check binds");
    let text = cbcl_core::intend::canonical_text(&m);
    assert!(
        text.contains("(@aria @bo @cy)"),
        "recipients from the cast: {text}"
    );
    assert!(
        text.contains(&format!(":replaces ({})", t[3].address)),
        "replaces the current write M3: {text}"
    );
    assert!(
        text.contains(&format!(":caused-by {}", t[1].address)),
        "predecessor is the opener: {text}"
    );
    assert!(text.contains(":from @bo"));

    // Rejections.
    assert_eq!(
        intend(&inst, &bo, "drop", fields(&[("item", s("venue"))])),
        Err(Reject::Role("owner".into()))
    );
    assert_eq!(
        intend(
            &inst,
            &bo,
            "check",
            fields(&[
                ("item", s("venue")),
                ("done", b(false)),
                ("replaces", SExpr::List(vec![]))
            ])
        ),
        Err(Reject::Forge("replaces".into()))
    );
    assert_eq!(
        intend(&inst, &bo, "open", fields(&[("title", s("x"))])),
        Err(Reject::Opener)
    );
    let aria = AgentKey("@aria".into());
    assert_eq!(
        intend(&inst, &aria, "drop", fields(&[("item", s("bread"))])),
        Err(Reject::NothingToDelete)
    );
    let m4 = intend(&inst, &aria, "drop", fields(&[("item", s("venue"))])).expect("owner drops");
    assert!(
        cbcl_core::intend::canonical_text(&m4).contains(&format!(":replaces ({})", t[3].address))
    );

    // Binding is a function of the accepted set: same input, same bytes.
    let again = intend(
        &inst,
        &bo,
        "check",
        fields(&[("item", s("venue")), ("done", b(false))]),
    )
    .unwrap();
    assert_eq!(cbcl_core::intend::canonical_text(&again), text);

    // may_send reflects the role gate and excludes the opener.
    assert_eq!(may_send(&inst, &bo), vec![String::from("check")]);
    assert_eq!(may_send(&inst, &aria), vec![String::from("drop")]);
}

#[test]
fn a_write_after_a_delete_names_the_deletion() {
    let d = dialect(&checklist_source());
    let t = trace(&d);
    let inst = Instance::new(&d, ThreadId("list-1".into()), &t).unwrap();
    let cy = AgentKey("@cy".into());
    let m = intend(
        &inst,
        &cy,
        "check",
        fields(&[("item", s("venue")), ("done", b(true))]),
    )
    .unwrap();
    let text = cbcl_core::intend::canonical_text(&m);
    assert!(
        text.contains(&format!(":replaces ({})", t[4].address)),
        "{text}"
    );
}

// ---------------------------------------------------------------------------
// TEST-1924: domain refusal and fold-side filtering on the lunch vote
// ---------------------------------------------------------------------------

#[test]
fn lunch_vote_domain_filters_in_the_fold_and_refuses_in_the_binder() {
    let d = dialect(&lunch_vote_source());
    assert!(r7_violations(&d).is_empty(), "{:?}", r7_violations(&d));
    let n = &d.name;
    let p = act(&format!("(lang {n} (propose @lunch :question \"Lunch?\" :options (\"Pizza\" \"Sushi\") :caused-by begin :thread \"v1\" :from @aria))"), "@aria");
    let a = p.address.clone();
    let v1 = act(
        &format!(
            "(lang {n} (vote @lunch :choice \"Pizza\" :caused-by {a} :thread \"v1\" :from @bo))"
        ),
        "@bo",
    );
    let v2 = act(
        &format!(
            "(lang {n} (vote @lunch :choice \"Tacos\" :caused-by {a} :thread \"v1\" :from @cy))"
        ),
        "@cy",
    );
    let acts = vec![p, v1, v2];
    let st = render_json(&fold(
        d.state.as_ref().unwrap(),
        d.causal_protocol.as_ref(),
        &acts,
    ));
    assert_eq!(
        st,
        "{\"question\":\"Lunch?\",\"options\":[\"Pizza\",\"Sushi\"],\"ballots\":{\"@bo\":\"Pizza\"},\"tally\":{\"Pizza\":1}}"
    );
    let inst = Instance::new(&d, ThreadId("v1".into()), &acts).unwrap();
    let dan = AgentKey("@dan".into());
    assert_eq!(
        intend(&inst, &dan, "vote", fields(&[("choice", s("Tacos"))])),
        Err(Reject::Domain("choice".into()))
    );
    let ok = intend(&inst, &dan, "vote", fields(&[("choice", s("Sushi"))])).unwrap();
    let text = cbcl_core::intend::canonical_text(&ok);
    assert!(
        text.starts_with(&format!("(lang {n} (vote @lunch")) && text.contains(":choice \"Sushi\""),
        "{text}"
    );
    assert_eq!(may_send(&inst, &dan), vec![String::from("vote")]);
}

#[test]
fn bounds_clause_is_enforced_at_receipt() {
    let d = dialect(&lunch_vote_source());
    let n = &d.name;
    let long = "q".repeat(281);
    let m = msg(&format!("(lang {n} (propose @lunch :question \"{long}\" :options (\"a\") :caused-by begin :thread \"v1\" :from @aria))"));
    assert!(verify_state_shape(&d, &m)
        .unwrap_err()
        .detail
        .contains("max-string 280"));
}
