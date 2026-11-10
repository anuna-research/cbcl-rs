//! SPEC-035 ADR-3502: host-HLC registers and explicit retirement.
use cbcl_core::state::{fold, Act};
use cbcl_parser::{parse_dialect, parse_message};

const D: &str = r#"(define hlc-test (cbcl) @a
  (extend open (to title) (tell to :title title))
  (extend write (to item value clock) (tell to :item item :value value :clock clock))
  (extend drop (to item) (tell to :item item))
  (shape open (require :title string))
  (shape write (require :item string) (require :value string) (require :clock hlc))
  (shape drop (require :item string))
  (protocol (then begin open) (then open write) (then open drop))
  (state
    (title (initial open :title))
    (lww (lww-register write :value :clock))
    (own (lww-per-signer write :value :clock))
    (map (lww-map write :item :value :clock drop))
    (values (multi-value-register write :value))
    (all (multi-value-map write :item :value))))"#;

fn dialect(text: &str) -> cbcl_core::dialect::Dialect {
    parse_dialect(&cbcl_parser::parse(text).unwrap()).unwrap()
}
fn act(value: &str, physical: u64, signer: &str) -> Act {
    let text = format!(
        r#"(lang hlc-test (write @a :item "x" :value "{value}" :clock "hlc-{physical:016x}-00000000" :replaces () :from {signer} :thread "t" :caused-by begin))"#
    );
    Act::from_message(parse_message(&text.parse().unwrap()).unwrap(), signer).unwrap()
}

#[test]
fn explicit_hlc_rules_install_and_newer_clock_beats_greater_hash() {
    let d = dialect(D);
    assert!(cbcl_core::r7::r7_violations(&d).is_empty());
    let mut old = act("old", 1, "@alice");
    let mut new = act("new", 2, "@alice");
    // Isolate ordering from the content hash; real-address coverage is in the corpus.
    old.address = format!("sha256-{}", "f".repeat(64));
    new.address = format!("sha256-{}", "0".repeat(64));
    let state = cbcl_core::state::render_json(&fold(d.state.as_ref().unwrap(), None, &[old, new]));
    let state: serde_json::Value = serde_json::from_str(&state).unwrap();
    assert!(
        state["title"].is_null(),
        "no opener means no initializer value"
    );
    assert_eq!(state["lww"], "new");
    assert_eq!(state["own"]["@alice"], "new");
    assert_eq!(state["map"]["x"], "new");
    assert_eq!(state["values"], serde_json::json!(["new", "old"]));
}

fn with_targets(a: &Act, targets: &[String]) -> Act {
    let item = cbcl_core::serializer::serialize(&a.fields["item"]);
    let value = cbcl_core::serializer::serialize(&a.fields["value"]);
    let clock = cbcl_core::serializer::serialize(&a.fields["clock"]);
    let text = format!("(lang hlc-test (write @a :item {item} :value {value} :clock {clock} :replaces ({}) :from {} :thread \"t\" :caused-by begin))", targets.join(" "), a.signer);
    Act::from_message(parse_message(&text.parse().unwrap()).unwrap(), &a.signer).unwrap()
}

fn observe(d: &cbcl_core::dialect::Dialect, acts: &[Act]) -> serde_json::Value {
    serde_json::from_str(&cbcl_core::state::render_json(&fold(
        d.state.as_ref().unwrap(),
        None,
        acts,
    )))
    .unwrap()
}

#[test]
fn clock_ties_use_logical_then_signer_then_address_and_ignore_delivery_order() {
    let d = dialect(D);
    let a = act("alice", 10, "@alice");
    let b = act("bob", 10, "@bob");
    let mut logical = act("logical", 10, "@alice");
    logical.fields.insert(
        "clock".into(),
        "\"hlc-000000000000000a-00000001\"".parse().unwrap(),
    );
    assert_eq!(observe(&d, &[a.clone(), b.clone()])["lww"], "bob");
    assert_eq!(observe(&d, &[b.clone(), a.clone()])["lww"], "bob");
    assert_eq!(
        observe(&d, &[logical.clone(), a.clone(), b.clone()])["lww"],
        "logical"
    );
    let x = act("x", 10, "@alice");
    let y = act("y", 10, "@alice");
    let expected = if x.address > y.address { "x" } else { "y" };
    assert_eq!(observe(&d, &[x.clone(), y.clone()])["lww"], expected);
    assert_eq!(observe(&d, &[y, x])["lww"], expected);
    let empty = observe(&d, &[]);
    assert!(empty["lww"].is_null());
    assert_eq!(empty["own"], serde_json::json!({}));
    assert_eq!(empty["map"], serde_json::json!({}));
}

#[test]
fn explicit_replacement_precedes_clock_arbitration_and_keeps_signer_isolation() {
    let d = dialect(D);
    let a = act("alice-old", 100, "@alice");
    let b = act("bob", 90, "@bob");
    let edit = with_targets(
        &act("alice-edit", 1, "@alice"),
        &[a.address.clone(), b.address.clone()],
    );
    let state = observe(&d, &[a.clone(), b.clone(), edit.clone()]);
    assert_eq!(
        state["lww"], "alice-old",
        "non-replacing LWW uses the clock"
    );
    assert_eq!(state["own"]["@alice"], "alice-edit");
    assert_eq!(
        state["own"]["@bob"], "bob",
        "cross-signer references cannot retire Bob"
    );
    assert_eq!(
        state["map"]["x"], "alice-edit",
        "authorized keyed writes can replace other writers"
    );
    let later = with_targets(
        &act("later", 2, "@alice"),
        std::slice::from_ref(&edit.address),
    );
    let forward = observe(&d, &[a.clone(), b.clone(), edit.clone(), later.clone()]);
    assert_eq!(
        forward["map"]["x"], "later",
        "superseded replacer still retires old writes"
    );
    assert_eq!(forward, observe(&d, &[later, edit, b, a]));
}

#[test]
fn map_deletion_is_observed_and_concurrent_unnamed_writes_survive() {
    let d = dialect(D);
    let a = act("old", 100, "@alice");
    let mut delete = Act::from_message(parse_message(&r#"(lang hlc-test (drop @a :item "x" :replaces () :from @alice :thread "t" :caused-by begin))"#.parse().unwrap()).unwrap(), "@alice").unwrap();
    delete.fields.insert(
        "replaces".into(),
        format!("({})", a.address).parse().unwrap(),
    );
    assert_eq!(
        observe(&d, &[a.clone(), delete.clone()])["map"],
        serde_json::json!({})
    );
    let concurrent = act("concurrent", 1, "@bob");
    assert_eq!(
        observe(&d, &[a, delete.clone(), concurrent])["map"]["x"],
        "concurrent"
    );
    assert!(
        cbcl_core::r7::verify_state_shape(&d, &delete.message).is_ok(),
        "delete needs no HLC"
    );
}

#[test]
fn malformed_clocks_fail_receipt_and_bad_clock_declarations_fail_installation() {
    let d = dialect(D);
    for bad in [
        "",
        "hlc-1-0",
        "hlc-000000000000000A-00000000",
        "hlc-0000000000000000-00000000 trailing",
    ] {
        let raw = format!(
            r#"(lang hlc-test (write @a :item "x" :value "v" :clock "{bad}" :replaces () :from @alice :thread "t" :caused-by begin))"#
        );
        let msg = parse_message(&raw.parse().unwrap()).unwrap();
        let err = cbcl_core::r7::verify_state_shape(&d, &msg).unwrap_err();
        assert_eq!(err.rule, "hlc");
    }
    for source in [
        D.replace("(require :clock hlc)", "(require :clock string)"),
        D.replace("(require :clock hlc)", "(require :clock integer)"),
        D.replace("(require :clock hlc)", "(optional :clock hlc)"),
        D.replace(
            "(lww-register write :value :clock)",
            "(lww-register write :value :value)",
        ),
        D.replace(
            "(lww-map write :item :value :clock drop)",
            "(lww-map write :clock :value :clock drop)",
        ),
        D.replace(
            "(define hlc-test (cbcl) @a",
            "(define hlc-test (cbcl) @a (:state-bounds (max-string 28))",
        ),
    ] {
        match parse_dialect(&source.parse().unwrap()) {
            Err(_) => (),
            Ok(d) => assert!(!cbcl_core::r7::r7_violations(&d).is_empty(), "{source}"),
        }
    }
    for rule in [
        "(lww-register write :value)",
        "(lww-map write :item :value)",
        "(lww-per-signer write :value clock)",
        "(lww-map write :item :value :clock drop extra)",
    ] {
        assert!(cbcl_parser::state_parser::parse_rule(&rule.parse().unwrap()).is_err());
    }
}

#[test]
fn aliases_preserve_body_identity_and_read_back_canonical_operations() {
    let d = dialect(D);
    let canonical = dialect(
        &D.replace("multi-value-register", "values")
            .replace("multi-value-map", "values-per-key"),
    );
    assert_eq!(
        cbcl_core::canonical::dialect_body_hash(&d),
        cbcl_core::canonical::dialect_body_hash(&canonical)
    );
    let text = cbcl_parser::describe::describe_dialect_str(D).unwrap();
    let described: serde_json::Value = serde_json::from_str(&text).unwrap();
    assert_eq!(
        described["state"]["lww"],
        serde_json::json!(["lwwRegister", "write", "value", "clock"])
    );
    assert_eq!(described["state"]["values"][0], "values");
    let schema = cbcl_core::state::render_schema(&cbcl_core::state::state_schema(
        d.state.as_ref().unwrap(),
        &d.shapes,
    ));
    assert!(schema.contains("lww"));
}

#[test]
fn forged_future_clock_wins_only_under_explicit_trusted_clock_contract() {
    let d = dialect(D);
    let honest = act("honest", 100, "@alice");
    let malicious = act("future", u64::MAX, "@mallory");
    assert_eq!(observe(&d, &[honest, malicious])["lww"], "future");
}

fn opener() -> Act {
    Act::from_message(
        parse_message(
            &r#"(lang hlc-test (open @a :title "demo" :from @a :thread "t" :caused-by begin))"#
                .parse()
                .unwrap(),
        )
        .unwrap(),
        "@a",
    )
    .unwrap()
}
fn data(
    item: &str,
    value: &str,
    clock: &str,
) -> std::collections::BTreeMap<String, cbcl_core::sexpr::SExpr> {
    [("item", item), ("value", value), ("clock", clock)]
        .into_iter()
        .map(|(k, v)| {
            (
                k.to_string(),
                cbcl_core::sexpr::SExpr::Atom(cbcl_core::sexpr::Atom::Str(v.to_string())),
            )
        })
        .collect()
}
fn issue(
    d: &cbcl_core::dialect::Dialect,
    acts: &[Act],
    who: &str,
    item: &str,
    value: &str,
    clock: u64,
) -> Act {
    let inst =
        cbcl_core::intend::Instance::new(d, cbcl_core::store::ThreadId("t".into()), acts).unwrap();
    let msg = cbcl_core::intend::intend(
        &inst,
        &cbcl_core::role::AgentKey(who.into()),
        "write",
        data(item, value, &format!("hlc-{clock:016x}-00000000")),
    )
    .unwrap();
    Act::from_message(msg, who).unwrap()
}

#[test]
fn binder_supplies_replacements_but_requires_explicit_clock_and_exports_agree() {
    let d = dialect(D);
    let open = opener();
    let a = issue(&d, std::slice::from_ref(&open), "@alice", "x", "old", 1);
    assert_eq!(a.fields["replaces"], "()".parse().unwrap());
    let b = issue(&d, &[open.clone(), a.clone()], "@alice", "x", "edit", 2);
    assert_eq!(
        b.fields["replaces"],
        format!("({})", a.address).parse().unwrap()
    );
    let acts = vec![open, a, b];
    let inst = cbcl_core::intend::Instance::new(&d, cbcl_core::store::ThreadId("t".into()), &acts)
        .unwrap();
    let mut missing = data("x", "v", "invalid");
    missing.remove("clock");
    assert!(cbcl_core::intend::intend(
        &inst,
        &cbcl_core::role::AgentKey("@alice".into()),
        "write",
        missing
    )
    .is_err());
    assert!(cbcl_core::intend::intend(
        &inst,
        &cbcl_core::role::AgentKey("@alice".into()),
        "write",
        data("x", "v", "invalid")
    )
    .is_err());
    let frame_acts = acts
        .iter()
        .map(|a| {
            format!(
                "({} {})",
                a.signer,
                cbcl_core::intend::canonical_text(&a.message)
            )
        })
        .collect::<Vec<_>>()
        .join(" ");
    let exported =
        cbcl_parser::state_exports::fold_str(&format!("(fold {D} \"t\" (acts {frame_acts}))"))
            .unwrap();
    assert_eq!(
        serde_json::from_str::<serde_json::Value>(&exported).unwrap(),
        observe(&d, &acts)
    );
    for a in &acts {
        assert!(cbcl_core::r7::verify_state_shape(&d, &a.message).is_ok());
    }
    let bad = act("bad", 1, "@alice");
    let raw = cbcl_core::intend::canonical_text(&bad.message)
        .replace("hlc-0000000000000001-00000000", "invalid");
    let frame = format!("(admit {D} \"t\" (acts {frame_acts}) (@alice {raw}))");
    let verdict = cbcl_parser::state_exports::admit_str(&frame).unwrap();
    assert!(verdict.contains("rejected"), "{verdict}");
}

#[test]
fn domain_excluded_high_clock_replacer_changes_neither_values_nor_replacements() {
    let src = D
        .replace(
            "(shape open (require :title string))",
            "(shape open (require :title string) (require :options list))",
        )
        .replace(
            "(state\n",
            "(state\n (options (initial open :options)) (domain write :item options)\n",
        );
    let d = dialect(&src);
    assert!(cbcl_core::r7::r7_violations(&d).is_empty());
    let open_text = r#"(lang hlc-test (open @a :title "demo" :options ("x") :from @a :thread "t" :caused-by begin))"#;
    let open =
        Act::from_message(parse_message(&open_text.parse().unwrap()).unwrap(), "@a").unwrap();
    let a = issue(&d, std::slice::from_ref(&open), "@alice", "x", "old", 1);
    let raw = format!(
        r#"(lang hlc-test (write @a :item "excluded" :value "bad" :clock "hlc-ffffffffffffffff-ffffffff" :replaces ({}) :from @alice :thread "t" :caused-by {}))"#,
        a.address, open.address
    );
    let bad = Act::from_message(parse_message(&raw.parse().unwrap()).unwrap(), "@alice").unwrap();
    assert!(matches!(
        cbcl_parser::state_exports::admit(
            &d,
            &cbcl_core::store::ThreadId("t".into()),
            &[open.clone(), a.clone()],
            &bad
        ),
        cbcl_parser::state_exports::Admission::Accepted
    ));
    assert_eq!(
        observe(&d, &[open.clone(), a.clone()]),
        observe(&d, &[bad, a, open])
    );
}

#[test]
fn authoring_and_description_support_new_rules_without_changing_contract_version() {
    let contract = serde_json::json!({"version":3,"kind":"contract","name":"clock-demo","author":"@a",
       "verbs":{"open":{"after":["begin"],"fields":{"title":"string"}},
                "write":{"after":["open"],"fields":{"item":"string","value":"integer","clock":"hlc"}},
                "drop":{"after":["open"],"fields":{"item":"string"}}},
       "state":{"lww":["lwwRegister","write","value","clock"],
                "own":["lwwPerSigner","write","value","clock"],
                "map":["lwwMap","write","item","value","clock","drop"],
                "values":["multiValueRegister","write","value"],
                "all":["multiValueMap","write","item","value"],
                "tally":["histogram","own"],"total":["sum","map"]}});
    let compiled = cbcl_parser::compile_contract_str(&contract.to_string()).unwrap();
    let compiled: serde_json::Value = serde_json::from_str(&compiled).unwrap();
    let src = compiled["dialect"].as_str().unwrap();
    let d = dialect(src);
    assert!(cbcl_core::r7::r7_violations(&d).is_empty());
    let described: serde_json::Value =
        serde_json::from_str(&cbcl_parser::describe_dialect_str(src).unwrap()).unwrap();
    assert_eq!(described["state"]["map"][0], "lwwMap");
    assert_eq!(described["state"]["values"][0], "values");
}

/// Writes only the new vector. Expected LWW/conflict state is independently asserted.
#[test]
#[ignore = "explicit corpus authoring; never rewrites legacy vectors"]
fn author_hlc_conformance_vector() {
    let d = dialect(D);
    let open = opener();
    let a = issue(&d, std::slice::from_ref(&open), "@alice", "x", "old", 1);
    let b = issue(&d, std::slice::from_ref(&open), "@bob", "x", "bob", 2);
    // Alice has not observed Bob: both remain in the multi-value result.
    let edit = issue(&d, &[open.clone(), a.clone()], "@alice", "x", "edit", 3);
    let accepted = vec![open, a, b, edit];
    let state = observe(&d, &accepted);
    let expected = serde_json::json!({"title":"demo",
        "lww":"edit","own":{"@alice":"edit","@bob":"bob"},"map":{"x":"edit"},
        "values":["bob","edit"],"all":{"x":["bob","edit"]}});
    assert_eq!(state, expected);
    let mut messages=accepted.iter().map(|a|serde_json::json!({"canonical":cbcl_core::intend::canonical_text(&a.message),"signer":a.signer})).collect::<Vec<_>>();
    let bad_text = format!(
        r#"(lang hlc-test (write @a :item "x" :value "bad" :clock "invalid" :replaces () :from @alice :thread "t" :caused-by {}))"#,
        accepted[0].address
    );
    let bad =
        Act::from_message(parse_message(&bad_text.parse().unwrap()).unwrap(), "@alice").unwrap();
    messages.push(serde_json::json!({"canonical":bad_text,"signer":"@alice"}));
    let mut addresses = accepted
        .iter()
        .map(|a| a.address.clone())
        .collect::<Vec<_>>();
    addresses.push(bad.address.clone());
    let mut verdicts = accepted
        .iter()
        .map(|a| (a.address.clone(), serde_json::json!("accepted")))
        .collect::<serde_json::Map<_, _>>();
    verdicts.insert(bad.address, serde_json::json!("rejected"));
    let vector = serde_json::json!({"id":"hlc-registers","covers":["lww-register","lww-per-signer","lww-map","multi-value-register","multi-value-map","explicit-clock","replacement","malformed-clock","exact-hlc-hash-tie"],
        "thread":"t","contract":D,"messages":messages,"intents":[],
        "expect":{"addresses":addresses,"verdicts":verdicts,"state":expected,"intents":[]}});
    std::fs::write(
        concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../test-vectors/state/hlc-registers.json"
        ),
        serde_json::to_string_pretty(&vector).unwrap() + "\n",
    )
    .unwrap();
}

#[test]
fn migrated_dialect_identities_differ_from_retired_definitions() {
    // Generated by the unmodified parser at 45bd3d0, not this implementation.
    let baseline: serde_json::Value = serde_json::from_str(include_str!(
        "../../../proofs/register-semantics/legacy-dialect-identities.json"
    ))
    .unwrap();
    for (name, expected) in baseline.as_object().unwrap() {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../test-vectors/state")
            .join(name);
        let vector: serde_json::Value =
            serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap();
        let d = dialect(vector["contract"].as_str().unwrap());
        if name == "progress-fork.json" {
            continue;
        }
        assert_ne!(
            cbcl_core::canonical::dialect_name(&d),
            expected.as_str().unwrap(),
            "{name}"
        );
    }
}

#[test]
fn excluded_same_key_replacer_cannot_hide_a_write_from_delete_binding() {
    let src = D
        .replace(
            "(shape open (require :title string))",
            "(shape open (require :title string) (require :options list))",
        )
        .replace(
            "(state\n",
            "(state\n (options (initial open :options)) (domain write :value options)\n",
        );
    let d = dialect(&src);
    let open_text = r#"(lang hlc-test (open @a :title "demo" :options ("allowed") :from @a :thread "t" :caused-by begin))"#;
    let open =
        Act::from_message(parse_message(&open_text.parse().unwrap()).unwrap(), "@a").unwrap();
    let a = issue(&d, std::slice::from_ref(&open), "@alice", "x", "allowed", 1);
    let raw = format!(
        r#"(lang hlc-test (write @a :item "x" :value "excluded" :clock "hlc-ffffffffffffffff-ffffffff" :replaces ({}) :from @alice :thread "t" :caused-by {}))"#,
        a.address, open.address
    );
    let excluded =
        Act::from_message(parse_message(&raw.parse().unwrap()).unwrap(), "@alice").unwrap();
    let acts = vec![open, a.clone(), excluded];
    assert_eq!(observe(&d, &acts)["map"]["x"], "allowed");
    let inst = cbcl_core::intend::Instance::new(&d, cbcl_core::store::ThreadId("t".into()), &acts)
        .unwrap();
    let fields = [("item".into(), "\"x\"".parse().unwrap())]
        .into_iter()
        .collect();
    let deletion = cbcl_core::intend::intend(
        &inst,
        &cbcl_core::role::AgentKey("@alice".into()),
        "drop",
        fields,
    )
    .expect("fold-visible write remains deletable");
    let deletion = Act::from_message(deletion, "@alice").unwrap();
    assert_eq!(
        deletion.fields["replaces"],
        format!("({})", a.address).parse().unwrap()
    );
    let mut all = acts;
    all.push(deletion);
    assert_eq!(observe(&d, &all)["map"], serde_json::json!({}));
}

#[test]
fn hlc_signer_binding_is_sorted_bounded_and_excludes_other_signers() {
    let source = format!(
        "{} (state (own (lww-per-signer write :value :clock))))",
        D.split("(state").next().unwrap()
    );
    let d = dialect(&source);
    let open = opener();
    let mut acts = vec![open.clone()];
    for n in 0..70 {
        acts.push(issue(
            &d,
            std::slice::from_ref(&open),
            "@alice",
            "x",
            &format!("{n}"),
            n,
        ));
    }
    let peer = issue(&d, &[open], "@bob", "x", "peer", 100);
    acts.push(peer.clone());
    let next = issue(&d, &acts, "@alice", "x", "next", 101);
    let cbcl_core::sexpr::SExpr::List(targets) = &next.fields["replaces"] else {
        panic!("replacement list")
    };
    let mut expected = acts
        .iter()
        .filter(|a| a.signer == "@alice")
        .map(|a| a.address.clone())
        .collect::<Vec<_>>();
    expected.sort();
    expected.truncate(64);
    let expected = expected
        .into_iter()
        .map(|a| cbcl_core::sexpr::SExpr::Atom(cbcl_core::sexpr::Atom::Symbol(a)))
        .collect::<Vec<_>>();
    assert_eq!(*targets, expected);
    assert!(!targets.contains(&cbcl_core::sexpr::SExpr::Atom(
        cbcl_core::sexpr::Atom::Symbol(peer.address)
    )));
    let inst = cbcl_core::intend::Instance::new(&d, cbcl_core::store::ThreadId("t".into()), &acts)
        .unwrap();
    let mut forged = data("x", "bad", "hlc-0000000000000066-00000000");
    forged.insert("replaces".into(), "()".parse().unwrap());
    assert!(matches!(
        cbcl_core::intend::intend(
            &inst,
            &cbcl_core::role::AgentKey("@alice".into()),
            "write",
            forged
        ),
        Err(cbcl_core::intend::Reject::Forge(_))
    ));
}
