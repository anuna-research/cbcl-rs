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
    let pinned_root = |pin: &str| {
        act(
            &format!(
                r#"(with-roles ((chair @chair) (reviewer @a @b @c)) :dialect {pin:?}
            (signed @chair (hello :thread "t" :caused-by begin)))"#
            ),
            "@chair",
        )
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

// REQ-3806 / TEST-3806 / TEST-3809: a later context conflict must retain
// the evidence of a fault already exposed by the same projection.
fn retains_fault_witness(before: &Value, after: &Value) {
    assert_eq!(before["status"], "fault");
    assert_eq!(after["status"], "fault");
    let retained = after["evidence"].as_array().unwrap();
    for witness in before["evidence"].as_array().unwrap() {
        assert!(
            retained.contains(witness),
            "lost {witness}: {before} -> {after}"
        );
    }
}

#[test]
fn root_conflict_retains_an_existing_context_opener_fork() {
    let src = source(None).replace(
        "(identity (context dialect))",
        "(whole-thread (context thread)) (opening (context thread opener)) (identity (context dialect))",
    );
    let root = root_act("");
    let first = open(&root);
    let second = act(
        &format!(
            r#"(signed @chair (lang review (open (@a @b) :from @chair :thread "t" :caused-by {})))"#,
            root.address
        ),
        "@chair",
    );
    let mut history = vec![root, first.clone(), second.clone()];
    let before = read(&src, &history);
    history.push(root_act("\"later root\""));
    let after = read(&src, &history);
    for field in ["meta", "whole-thread", "opening"] {
        retains_fault_witness(&before[field], &after[field]);
    }
    // Role projections never depended on the opener fork.
    let roster_evidence = after["reviewers"]["evidence"].as_array().unwrap();
    assert!(!roster_evidence.contains(&json!(first.address)));
    assert!(!roster_evidence.contains(&json!(second.address)));
    history.reverse();
    history.extend(history.clone());
    assert_eq!(read(&src, &history), after);
}

#[test]
fn root_conflict_retains_an_existing_mixed_thread_context_witness() {
    let src = source(None);
    let root = root_act("");
    let opening = open(&root);
    let foreign = act(
        &format!(
            r#"(signed @a (lang review (approve @chair :target "@b" :from @a :thread "other" :caused-by {})))"#,
            opening.address
        ),
        "@a",
    );
    let mut history = vec![root, opening, foreign];
    let before = read(&src, &history);
    history.push(root_act("\"later root\""));
    let after = read(&src, &history);
    for field in ["meta", "reviewers", "eligible", "arrivals"] {
        retains_fault_witness(&before[field], &after[field]);
    }
    history.reverse();
    history.extend(history.clone());
    assert_eq!(read(&src, &history), after);
}

#[test]
fn quoted_dialect_pins_cross_the_strict_wire_boundary() {
    let src = source(None);
    let dialect = parse_dialect(&parse(&src).unwrap()).unwrap();
    let hash = cbcl_core::canonical::dialect_hash(&dialect);
    let pinned = |pin: &str| {
        act(
            &format!(
                r#"(with-roles ((chair @chair) (reviewer @a @b @c)) :dialect {pin:?}
          (signed @chair (hello :thread "t" :caused-by begin)))"#
            ),
            "@chair",
        )
    };
    let value = read(&src, &[pinned(&hash)]);
    assert_eq!(value["reviewers"], json!(["@a", "@b", "@c"]));
    assert_eq!(value["eligible"]["status"], "reached");
    for pin in [
        format!("sha256:{}", "0".repeat(64)),
        "sha256:abc".to_owned(),
        format!("sha256:{}", "A".repeat(64)),
        format!("md5:{}", "a".repeat(64)),
    ] {
        assert_eq!(
            read(&src, &[pinned(&pin)])["reviewers"]["status"],
            "fault",
            "pin={pin}"
        );
    }
}

/// Low-level fold support fixture: the missing-parent input is deliberately not
/// an admission trace. Roster root evidence still belongs to the freeze footprint.
#[test]
fn domain_roster_root_outside_cut_is_retained_as_freeze_support() {
    let src = source(None).replace("(arrivals (count approve))",
        "(arrivals (count approve)) (freeze arrivals close fault) (threshold quorum arrivals (count 1))");
    state_exports::parse_and_install_dialect(&parse(&src).unwrap()).unwrap();
    let root = root_act("");
    let writer = act(
        r#"(signed @a (lang review (approve @chair :target "@a" :from @a :thread "t" :caused-by "missing-parent")))"#,
        "@a",
    );
    let close = act(
        &format!(
            r#"(signed @chair (lang review (close (@a @b @c) :from @chair :thread "t" :caused-by {})))"#,
            writer.address
        ),
        "@chair",
    );
    assert_eq!(
        read(&src, &[root.clone(), writer.clone()])["quorum"]["status"],
        "reached"
    );
    let after = read(&src, &[root.clone(), writer, close.clone()]);
    let mut evidence = vec![root.address, close.address];
    evidence.sort();
    assert_eq!(after["quorum"]["status"], "fault");
    assert_eq!(after["quorum"]["evidence"], json!(evidence));
}

#[test]
fn finite_fault_witness_retains_domain_roster_root_for_replay() {
    let src = source(None).replace(
        "(arrivals (count approve))",
        r#"(lattice flags (elements quiet conflict) (bottom quiet) (top conflict)
          (join (quiet quiet quiet) (quiet conflict conflict)
                (conflict quiet conflict) (conflict conflict conflict)))
        (arrivals (lift approve (into flags) (contribute (:target "@a" conflict))))"#,
    );
    state_exports::parse_and_install_dialect(&parse(&src).unwrap()).unwrap();
    let root = root_act("");
    let writer = approve("@a", "@a", &root);
    let acts = vec![root.clone(), writer];
    let before = read(&src, &acts);
    assert_eq!(before["arrivals"]["status"], "fault");
    let evidence = before["arrivals"]["evidence"].as_array().unwrap();
    assert!(
        evidence.contains(&json!(root.address)),
        "roster root supplies replay eligibility"
    );
    let witness: Vec<_> = acts
        .iter()
        .filter(|a| evidence.contains(&json!(a.address)))
        .cloned()
        .collect();
    let replay = read(&src, &witness);
    assert_eq!(replay["arrivals"]["status"], "fault");
    for id in evidence {
        assert!(replay["arrivals"]["evidence"]
            .as_array()
            .unwrap()
            .contains(id));
    }
    let mut delivered = witness.clone();
    delivered.reverse();
    delivered.extend(witness);
    assert_eq!(read(&src, &delivered)["arrivals"], replay["arrivals"]);
}

#[test]
fn sealed_cast_root_identity_commits_roster() {
    let src = source(None);
    let d = parse_dialect(&parse(&src).unwrap()).unwrap();
    let first = root_act("");
    let second = act(
        r#"(with-roles ((chair @chair) (reviewer @x @y @z)) (signed @chair (hello :thread "t" :caused-by begin)))"#,
        "@chair",
    );
    assert_ne!(
        first.address, second.address,
        "sealed root identity must commit its cast"
    );
    let thread = cbcl_core::store::ThreadId("t".into());
    let a = state_exports::admit(&d, &thread, &[], &first);
    let b = state_exports::admit(&d, &thread, &[], &second);
    assert!(
        matches!(a, state_exports::Admission::Accepted),
        "first={a:?}"
    );
    assert!(
        matches!(b, state_exports::Admission::Accepted),
        "second={b:?}"
    );
    let a = read(&src, &[first]);
    let b = read(&src, &[second]);
    assert_ne!(
        a["reviewers"], b["reviewers"],
        "distinct roots retain distinct rosters"
    );
}

#[test]
fn sealed_root_identity_uses_explicit_instance_freshness() {
    let first = root_act("100");
    let same = root_act("100");
    let fresh = root_act("101");
    assert_eq!(first.address, same.address, "identical roots deduplicate");
    assert_ne!(
        first.address, fresh.address,
        "committed fresh data distinguishes instances"
    );
}

#[test]
fn sealed_root_identity_selects_exact_wrapper_and_root_predicate() {
    use cbcl_core::message::{CausedBy, Message, WrapperType};
    use cbcl_core::state::wire_address;
    fn set_cause(message: &mut Message, cause: Option<CausedBy>) {
        match message {
            Message::Simple { caused_by, .. } => *caused_by = cause,
            Message::Wrapped { content, .. } => set_cause(content, cause),
            Message::Dialect { inner, .. } => set_cause(inner, cause),
            Message::Meta { .. } => panic!("test root must contain a simple message"),
        }
    }
    let original = root_act("100");
    let parent = root_act("parent").address;
    for cause in [
        None,
        Some(CausedBy::Begin),
        Some(CausedBy::Multiple(vec![])),
    ] {
        let mut message = original.message.clone();
        set_cause(&mut message, cause);
        let expected = wire_address(&message);
        let wrapped = Message::Dialect {
            dialect_name: "review".into(),
            inner: Box::new(Message::Wrapped {
                wrapper: WrapperType::WithLimits,
                params: vec![],
                content: Box::new(message),
            }),
        };
        let received = Act::from_message(wrapped, "@chair").unwrap();
        assert!(received.predecessors.is_empty());
        assert_eq!(
            received.address, expected,
            "transparent ancestors are excluded"
        );
    }
    for cause in [
        CausedBy::Single(parent.clone()),
        CausedBy::Multiple(vec![parent]),
    ] {
        let mut message = original.message.clone();
        set_cause(&mut message, Some(cause));
        let expected = wire_address(message.innermost_simple().unwrap());
        assert_eq!(
            Act::from_message(message, "@chair").unwrap().address,
            expected
        );
    }
    let Message::Wrapped { params, .. } = original.message else {
        panic!("sealed test root")
    };
    let nested = Message::Wrapped {
        wrapper: WrapperType::WithRoles,
        params,
        content: Box::new(root_act("nested").message),
    };
    let expected = wire_address(&nested);
    assert_eq!(
        Act::from_message(nested, "@chair").unwrap().address,
        expected,
        "the complete outermost sealed subtree is committed"
    );
}

#[test]
fn sealed_root_identity_validation_rejects_cached_simple_address() {
    let d = parse_dialect(&parse(&source(None)).unwrap()).unwrap();
    let mut root = root_act("100");
    root.address = cbcl_core::state::wire_address(root.simple());
    let verdict = state_exports::admit(&d, &cbcl_core::store::ThreadId("t".into()), &[], &root);
    assert!(
        matches!(verdict, state_exports::Admission::Rejected(_)),
        "an old simple-message address cannot validate a sealed root: {verdict:?}"
    );
}
