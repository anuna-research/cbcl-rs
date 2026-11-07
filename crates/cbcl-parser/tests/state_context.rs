//! SPEC-038 TEST-3809: context is ordinary read-only kernel data, not quorum policy.
use cbcl_core::state::{fold, render_json, Act};
use cbcl_parser::{parse, parse_dialect, parse_message, state_exports};
use serde_json::{json, Value};

fn source(policy: Option<&str>) -> String {
    let freeze = policy
        .map(|p| format!("(freeze meta close {p})"))
        .unwrap_or_default();
    format!(
        r#"(define review (cbcl) @anuna
      (:roles (chair (* reviewer))) (:causal-locality derive)
      (extend open (to) :from chair :to reviewer (tell to))
      (extend approve (to target) :from reviewer :to chair (tell to :target target))
      (extend close (to) :from chair :to reviewer (tell to))
      (shape approve (require :target string))
      (protocol (then begin open) (then open (repeat 8 approve close)))
      (state (meta (context)) {freeze}
        (identity (context dialect)) (reviewers (context thread roles reviewer))
        (front (context observation frontier))
        (domain approve :target reviewers) (arrivals (count approve))
        (threshold eligible reviewers (member "@a"))))"#
    )
}
fn act(text: &str, signer: &str) -> Act {
    Act::from_message(parse_message(&parse(text).unwrap()).unwrap(), signer).unwrap()
}
fn root_act(content: &str) -> Act {
    act(
        &format!(
            r#"(with-roles ((chair @chair) (reviewer @a @b @c))
        (signed @chair (hello {content} :thread "t" :caused-by begin)))"#
        ),
        "@chair",
    )
}
fn open(root: &Act) -> Act {
    act(
        &format!(
            r#"(signed @chair (lang review (open (@a @b @c) :from @chair :thread "t" :caused-by {})))"#,
            root.address
        ),
        "@chair",
    )
}
fn approve(who: &str, target: &str, parent: &Act) -> Act {
    act(
        &format!(
            r#"(signed {who} (lang review (approve @chair :target {target:?} :from {who} :thread "t" :caused-by {})))"#,
            parent.address
        ),
        who,
    )
}
fn close(parent: &Act) -> Act {
    act(
        &format!(
            r#"(signed @chair (lang review (close (@a @b @c) :from @chair :thread "t" :caused-by {})))"#,
            parent.address
        ),
        "@chair",
    )
}
fn read(src: &str, acts: &[Act]) -> Value {
    state_exports::parse_and_install_dialect(&parse(src).unwrap()).unwrap();
    let d = parse_dialect(&parse(src).unwrap()).unwrap();
    serde_json::from_str(&render_json(&fold(
        d.state.as_ref().unwrap(),
        d.causal_protocol.as_ref(),
        acts,
    )))
    .unwrap()
}
#[test]
fn context_exposes_installed_and_sealed_thread_metadata() {
    let src = source(None);
    let root = root_act("");
    let open = open(&root);
    let value = read(&src, &[root.clone(), open.clone()]);
    let d = parse_dialect(&parse(&src).unwrap()).unwrap();
    assert_eq!(value["identity"]["name"], "review");
    assert_eq!(
        value["identity"]["address"],
        cbcl_core::canonical::dialect_hash(&d)
    );
    assert_eq!(
        value["identity"]["body-address"],
        cbcl_core::canonical::dialect_name(&d)
    );
    assert_eq!(value["identity"]["bounds"]["max-list"], 64);
    assert_eq!(
        value["identity"]["roles"],
        json!({"chair":"singleton","reviewer":"indexed"})
    );
    assert_eq!(value["reviewers"], json!(["@a", "@b", "@c"]));
    assert_eq!(value["meta"]["thread"]["id"], "t");
    assert_eq!(value["meta"]["thread"]["root"], root.address);
    assert_eq!(value["meta"]["thread"]["opener"], open.address);
    assert_eq!(value["meta"]["thread"]["initiator"], "@chair");
    assert_eq!(value["meta"]["observation"]["accepted-count"], 2);
    assert_eq!(value["front"], json!([open.address]));
    let renamed = read(&src.replace("define review", "define alternate"), &[]);
    assert_eq!(renamed["identity"]["name"], "alternate");
    assert_eq!(
        renamed["identity"]["body-address"],
        value["identity"]["body-address"]
    );
}
#[test]
fn context_rosters_support_existing_domains_and_membership_thresholds() {
    let src = source(None);
    let root = root_act("");
    let open = open(&root);
    let inside = approve("@a", "@b", &open);
    let outside = approve("@b", "@outside", &open);
    let value = read(
        &src,
        &[root.clone(), open.clone(), inside.clone(), outside.clone()],
    );
    assert_eq!(value["arrivals"], 1);
    assert_eq!(
        value["eligible"],
        json!({"status":"reached","element":{"member":"@a"}})
    );
    let mut reverse = vec![outside, inside, open, root];
    reverse.extend(reverse.clone());
    assert_eq!(read(&src, &reverse), value);
}
#[test]
fn missing_context_is_absent_and_does_not_invent_an_empty_roster() {
    let value = read(&source(None), &[]);
    assert_eq!(value["reviewers"], Value::Null);
    assert_eq!(value["meta"]["thread"], Value::Null);
    assert_eq!(value["eligible"]["status"], "pending");
    assert_eq!(value["identity"]["name"], "review");
}
#[test]
fn incompatible_roots_fault_even_when_their_casts_are_identical() {
    let src = source(None);
    let a = root_act("");
    let b = root_act("\"other root\"");
    let value = read(&src, &[a.clone(), b.clone()]);
    assert_eq!(value["meta"]["status"], "fault");
    assert_eq!(value["reviewers"]["status"], "fault");
    assert_eq!(value["eligible"]["status"], "fault");
    assert_eq!(read(&src, &[b, a]), value);
}
#[test]
fn cast_validation_and_pins_are_not_bypassed_by_context_reads() {
    let src = source(None);
    let malformed = act(
        r#"(with-roles ((chair @chair)) (signed @chair (hello :thread "t" :caused-by begin)))"#,
        "@chair",
    );
    // BUG-006: the strict wire lexer splits bare sha256:<hex> symbols.
    // Exercise the existing typed cast boundary explicitly for pin semantics;
    // this test does not claim that the legacy pin spelling round-trips on wire.
    let pinned_root = |pin: &str| {
        let tree: cbcl_core::sexpr::SExpr = format!(
            r#"(with-roles ((chair @chair) (reviewer @a @b @c)) :dialect {pin}
            (signed @chair (hello :thread "t" :caused-by begin)))"#
        )
        .parse()
        .unwrap();
        Act::from_message(
            cbcl_core::message::Message::try_from(&tree).unwrap(),
            "@chair",
        )
        .unwrap()
    };
    let wrong = pinned_root(&format!("sha256:{}", "0".repeat(64)));
    for bad in [malformed, wrong] {
        assert_eq!(read(&src, &[bad.clone()])["reviewers"]["status"], "fault");
        assert_eq!(
            read(&src, &[root_act(""), bad.clone()]),
            read(&src, &[bad, root_act("")])
        );
    }
    let d = parse_dialect(&parse(&src).unwrap()).unwrap();
    let pinned = pinned_root(&cbcl_core::canonical::dialect_hash(&d));
    assert_eq!(
        read(&src, &[pinned])["reviewers"],
        json!(["@a", "@b", "@c"])
    );
}
#[test]
fn context_schema_marks_fixed_projections_and_current_observations() {
    let src = source(None);
    let d = parse_dialect(&parse(&src).unwrap()).unwrap();
    let schema: Value = serde_json::from_str(&cbcl_core::state::render_schema(
        &cbcl_core::state::state_schema(d.state.as_ref().unwrap(), &d.shapes),
    ))
    .unwrap();
    assert_eq!(schema["reviewers"]["observation"], "context");
    assert_eq!(schema["identity"]["observation"], "context");
    assert_eq!(schema["front"]["observation"], "snapshot");
    assert_eq!(schema["meta"]["observation"], "snapshot");
    assert_eq!(
        schema["meta"]["fields"]["thread"]["fields"]["roles"]["value"]["type"],
        "set"
    );
}
#[test]
fn cached_metadata_is_not_wire_data_and_installation_rebuilds_it() {
    let src = source(None);
    let mut d = parse_dialect(&parse(&src).unwrap()).unwrap();
    let canonical = cbcl_core::canonical::dialect_canonical_bytes(&d);
    for entry in &mut d.state.as_mut().unwrap().entries {
        if let cbcl_core::state::Entry::Field {
            rule:
                cbcl_core::state::Rule::Context {
                    definition: Some(cache),
                    ..
                },
            ..
        } = entry
        {
            cache.roles.clear();
            cache.address = "forged".into();
        }
    }
    assert_eq!(canonical, cbcl_core::canonical::dialect_canonical_bytes(&d));
    let mut registry = cbcl_core::dialect::DialectRegistry::new();
    registry.install(d).unwrap();
    let d = registry.get(registry.len() - 1).unwrap();
    let value: Value = serde_json::from_str(&render_json(&fold(
        d.state.as_ref().unwrap(),
        d.causal_protocol.as_ref(),
        &[root_act("")],
    )))
    .unwrap();
    assert_eq!(value["reviewers"], json!(["@a", "@b", "@c"]));
}
#[test]
fn context_observation_freezes_include_domain_excluded_accepted_acts() {
    for policy in ["supersede", "fault"] {
        let src = source(Some(policy));
        let root = root_act("");
        let open = open(&root);
        let before = approve("@a", "@b", &open);
        let close = close(&before);
        let late = approve("@b", "@outside", &close);
        let history = vec![root, open, before, close, late.clone()];
        let value = read(&src, &history);
        assert_eq!(value["arrivals"], 1);
        if policy == "supersede" {
            assert_eq!(value["meta"]["superseded"], json!([late.address]));
            assert_eq!(value["meta"]["value"]["observation"]["accepted-count"], 4);
        } else {
            assert_eq!(value["meta"]["status"], "fault");
        }
        let mut forked = history;
        forked.push(root_act("\"other root\""));
        assert_eq!(read(&src, &forked)["meta"]["status"], "fault");
    }
}
#[test]
fn context_is_available_without_changing_role_admission() {
    use cbcl_parser::state_exports::Admission;
    let src = source(None);
    let d = parse_dialect(&parse(&src).unwrap()).unwrap();
    let root = root_act("");
    let open = open(&root);
    let approve = approve("@a", "@b", &open);
    let mut accepted = Vec::new();
    for candidate in [root, open, approve] {
        assert!(matches!(
            state_exports::admit(
                &d,
                &cbcl_core::store::ThreadId("t".into()),
                &accepted,
                &candidate
            ),
            Admission::Accepted
        ));
        accepted.push(candidate);
    }
    assert_eq!(read(&src, &accepted)["arrivals"], 1);
}
#[test]
fn unknown_context_paths_and_policy_specific_forms_are_rejected() {
    let src = source(None);
    for bad in [
        src.replace(
            "context thread roles reviewer",
            "context thread roles absent",
        ),
        src.replace(
            "context observation frontier",
            "context observation local-clock",
        ),
        src.replace(
            "context thread roles reviewer",
            "context thread roles reviewer extra",
        ),
        src.replace("(count approve)", "(signers approve reviewer)"),
        src.replace("(member \"@a\")", "(count (majority reviewers))"),
    ] {
        let result = parse(&bad)
            .map_err(|e| e.to_string())
            .and_then(|s| state_exports::parse_and_install_dialect(&s).map(|_| ()));
        assert!(result.is_err(), "installed invalid context: {bad}");
    }
}
