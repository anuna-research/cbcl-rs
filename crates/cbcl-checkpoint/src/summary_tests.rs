use super::*;
use cbcl_core::{
    message::{Message, Performative},
    sexpr::Atom,
};

fn s(x: &str) -> SExpr {
    SExpr::Atom(Atom::Str(x.into()))
}
fn act(
    verb: &str,
    key: &str,
    value: &str,
    refs: &[String],
    nonce: i64,
    signer: &str,
    time: u64,
) -> Act {
    let fields = [
        ("k", s(key)),
        ("v", s(value)),
        ("clock", s(&Hlc::new(time, 0).render())),
        ("replaces", SExpr::List(refs.iter().map(|x| s(x)).collect())),
    ];
    let message = Message::Simple {
        performative: Performative::Custom(verb.into()),
        recipient: None,
        content: SExpr::Atom(Atom::Num(nonce)),
        params: fields
            .into_iter()
            .flat_map(|(k, v)| [SExpr::Atom(Atom::Keyword(k.into())), v])
            .collect(),
        thread: Some("summary-test".into()),
        sender: Some(signer.into()),
        caused_by: None,
    };
    Act::from_message(
        Message::Dialect {
            dialect_name: "summary-test".into(),
            inner: alloc::boxed::Box::new(message),
        },
        signer,
    )
    .unwrap()
}
fn clause(rules: Vec<Rule>) -> StateClause {
    StateClause {
        entries: rules
            .into_iter()
            .enumerate()
            .map(|(i, rule)| Entry::Field {
                name: alloc::format!("f{i}"),
                rule,
            })
            .collect(),
    }
}
fn rules() -> Vec<Rule> {
    vec![
        Rule::Initial {
            verb: "init".into(),
            key: "v".into(),
        },
        Rule::Values {
            verb: "put".into(),
            key: "v".into(),
        },
        Rule::ValuesPerKey {
            verb: "put".into(),
            key: "k".into(),
            value: "v".into(),
            delete: Some("del".into()),
        },
        Rule::ObservedSet {
            add: "put".into(),
            remove: "del".into(),
            key: "k".into(),
        },
        Rule::LwwMap {
            verb: "put".into(),
            key: "k".into(),
            value: "v".into(),
            clock: "clock".into(),
            delete: Some("del".into()),
        },
        Rule::LwwRegister {
            verb: "put".into(),
            key: "v".into(),
            clock: "clock".into(),
        },
        Rule::LwwPerSigner {
            verb: "put".into(),
            key: "v".into(),
            clock: "clock".into(),
        },
    ]
}
fn advance(s: &mut Summary, history: &mut Vec<Act>, a: &Act) {
    let covered: BTreeSet<_> = history.iter().map(|x| x.address.clone()).collect();
    s.apply(a, |id| covered.contains(id)).unwrap();
    history.push(a.clone());
    assert_eq!(
        s.render(),
        state::fold(s.clause(), s.protocol.as_ref(), history)
    );
    s.validate().unwrap();
    let restored = Summary::decode_for(&s.encode(), s.clause(), s.protocol.as_ref()).unwrap();
    assert_eq!(*s, restored);
}
fn permutations(xs: &mut [Act], i: usize, f: &mut impl FnMut(&[Act])) {
    if i == xs.len() {
        f(xs);
        return;
    }
    for j in i..xs.len() {
        xs.swap(i, j);
        permutations(xs, i + 1, f);
        xs.swap(i, j);
    }
}

fn all_plain() -> Vec<Rule> {
    let mut rs = rules();
    rs.extend([
        Rule::Exists { verb: "put".into() },
        Rule::Count { verb: "put".into() },
        Rule::Counter {
            inc: "put".into(),
            dec: "del".into(),
            key: "v".into(),
        },
        Rule::SetUnion {
            verb: "put".into(),
            key: "v".into(),
        },
        Rule::Events {
            verb: "put".into(),
            key: "v".into(),
        },
        Rule::Histogram { field: "f4".into() },
        Rule::Sum {
            field: "f11".into(),
        },
    ]);
    rs
}
fn numeric(mut a: Act, n: i64) -> Act {
    let Message::Dialect { inner, .. } = &mut a.message else {
        panic!("dialect")
    };
    let Message::Simple { params, .. } = inner.as_mut() else {
        panic!("simple")
    };
    for pair in params.chunks_exact_mut(2) {
        if pair[0] == SExpr::Atom(Atom::Keyword("v".into())) {
            pair[1] = SExpr::Atom(Atom::Num(n));
        }
    }
    Act::from_message(a.message, &a.signer).unwrap()
}
#[test]
fn all_fourteen_plain_rules_every_prefix_cut_permutation_duplicate() {
    let c = clause(all_plain());
    let a = numeric(act("put", "x", "", &[], 1, "@a", 10), 12);
    let b = numeric(
        act(
            "put",
            "y",
            "",
            core::slice::from_ref(&a.address),
            2,
            "@b",
            3,
        ),
        -4,
    );
    let d = numeric(
        act(
            "del",
            "x",
            "",
            core::slice::from_ref(&a.address),
            3,
            "@a",
            12,
        ),
        2,
    );
    let e = numeric(
        act(
            "put",
            "x",
            "",
            core::slice::from_ref(&b.address),
            4,
            "@a",
            1,
        ),
        7,
    );
    let mut xs = vec![a, b, d, e];
    let mut final_hash = None;
    permutations(&mut xs, 0, &mut |order| {
        let mut summary = Summary::new(&c, None).unwrap();
        let mut h = vec![];
        for a in order {
            advance(&mut summary, &mut h, a);
            let before = summary.clone();
            advance(&mut summary, &mut h, a);
            assert_eq!(summary, before);
        }
        if let Some(hash) = final_hash {
            assert_eq!(summary.hash(), hash)
        } else {
            final_hash = Some(summary.hash())
        }
        for cut in 0..=order.len() {
            let mut summary = Summary::new(&c, None).unwrap();
            let mut history = vec![];
            for a in &order[..cut] {
                advance(&mut summary, &mut history, a)
            }
            summary = Summary::decode(&summary.encode(), &c).unwrap();
            for a in &order[cut..] {
                advance(&mut summary, &mut history, a)
            }
            assert_eq!(Some(summary.hash()), final_hash);
        }
    });
}
#[test]
fn covered_replay_cannot_restore_retired_contribution() {
    let c = clause(all_plain());
    let a = act("put", "x", "old", &[], 1, "@a", 1);
    let b = act(
        "put",
        "x",
        "new",
        core::slice::from_ref(&a.address),
        2,
        "@a",
        2,
    );
    let mut summary = Summary::new(&c, None).unwrap();
    let mut h = vec![];
    advance(&mut summary, &mut h, &a);
    advance(&mut summary, &mut h, &b);
    let before = summary.clone();
    advance(&mut summary, &mut h, &a);
    assert_eq!(summary, before);
}
#[test]
fn cross_scope_late_nonstate_and_covered_target_pruning() {
    let c = clause(all_plain());
    let target = act("other", "y", "", &[], 1, "@a", 0);
    let mut summary = Summary::new(&c, None).unwrap();
    let mut h = vec![];
    for (i, key) in ["x", "y"].iter().enumerate() {
        let a = act(
            "del",
            key,
            "",
            core::slice::from_ref(&target.address),
            i as i64 + 2,
            "@b",
            1,
        );
        advance(&mut summary, &mut h, &a);
    }
    assert!(summary.pending_references() > 0);
    advance(&mut summary, &mut h, &target);
    assert_eq!(summary.pending_references(), 0);
    let late = act("put", "y", "red", &[], 8, "@a", 1);
    let remove = act(
        "del",
        "x",
        "",
        core::slice::from_ref(&late.address),
        9,
        "@b",
        2,
    );
    advance(&mut summary, &mut h, &remove);
    advance(&mut summary, &mut h, &late);
    assert_eq!(summary.pending_references(), 0);
}
#[test]
fn domains_and_bad_references_fail_closed_atomically() {
    let mut c = clause(all_plain());
    c.entries.push(Entry::Domain {
        verb: "put".into(),
        key: "k".into(),
        field: "f0".into(),
    });
    assert_eq!(Summary::new(&c, None), Err(Error::Unsupported));
    let mut summary = Summary::new(&clause(all_plain()), None).unwrap();
    let before = summary.clone();
    let bad = act(
        "put",
        "x",
        "",
        &[alloc::format!("sha256:{}", "1".repeat(64))],
        1,
        "@a",
        1,
    );
    assert!(summary.apply(&bad, |_| false).is_err());
    assert_eq!(before, summary);
}
#[test]
fn malformed_metadata_and_snapshots_fail_before_mutation() {
    let c = clause(all_plain());
    let a = act("put", "x", "red", &[], 1, "@a", 1);
    let mut summary = Summary::new(&c, None).unwrap();
    for i in 0..5 {
        let mut bad = a.clone();
        match i {
            0 => bad.address.push('x'),
            1 => bad.verb = "del".into(),
            2 => {
                bad.fields.insert("v".into(), s("forged"));
            }
            3 => bad.predecessors.push("forged".into()),
            _ => {
                bad.recipients.insert("@bad".into());
            }
        }
        let before = summary.clone();
        assert!(summary.apply(&bad, |_| false).is_err());
        assert_eq!(summary, before);
    }
    summary.apply(&a, |_| false).unwrap();
    let bytes = summary.encode();
    assert_eq!(&bytes[..4], &2u32.to_be_bytes());
    for n in 0..bytes.len() {
        assert!(Summary::decode(&bytes[..n], &c).is_err())
    }
    let mut old = bytes.clone();
    old[3] = 1;
    assert!(Summary::decode(&old, &c).is_err());
    let mut schema = bytes.clone();
    schema[4] ^= 1;
    assert!(Summary::decode(&schema, &c).is_err());
    let mut trailing = bytes;
    trailing.push(0);
    assert!(Summary::decode(&trailing, &c).is_err());
    if let RowData::Events(xs) = &mut summary.rows[11] {
        xs[0].id = "bad".into();
    } else {
        panic!("events")
    }
    assert!(Summary::decode(&summary.encode(), &c).is_err());
    assert!(serde_json::from_slice::<Summary>(&serde_json::to_vec(&summary).unwrap()).is_err());
}
#[test]
fn binary_snapshot_byte_budget_is_checked_before_recognition() {
    assert_eq!(
        Summary::decode(&vec![0; 16 * 1024 * 1024 + 1], &clause(vec![])),
        Err(Error::Budget)
    );
    let c = clause(all_plain());
    let mut b = Summary::new(&c, None).unwrap().encode();
    b[40..44].copy_from_slice(&u32::MAX.to_be_bytes());
    assert_eq!(Summary::decode(&b, &c), Err(Error::Budget));
}
#[test]
fn events_store_projected_slice_and_derive_histogram_and_sum() {
    let c = clause(vec![
        rules()[4].clone(),
        Rule::Events {
            verb: "put".into(),
            key: "v".into(),
        },
        Rule::Histogram { field: "f0".into() },
        Rule::Sum { field: "f1".into() },
    ]);
    let mut summary = Summary::new(&c, None).unwrap();
    let mut history = vec![];
    for i in 0..12 {
        let mut a = numeric(act("put", "x", "", &[], i, "@a", 1), i % 3);
        let Message::Dialect { inner, .. } = &mut a.message else {
            panic!("dialect")
        };
        let Message::Simple {
            content, params, ..
        } = inner.as_mut()
        else {
            panic!("simple")
        };
        *content = s(&alloc::format!(
            "{i}:{}",
            "UNRELATED_BODY_PAYLOAD".repeat(2048)
        ));
        params.extend([
            SExpr::Atom(Atom::Keyword("not-selected".into())),
            s(&"UNRELATED_FIELD_PAYLOAD".repeat(64)),
        ]);
        a = Act::from_message(a.message, &a.signer).unwrap();
        advance(&mut summary, &mut history, &a);
    }
    let bytes = summary.encode();
    assert!(bytes.len() < 4096);
    assert!(!bytes.windows(b"UNRELATED".len()).any(|w| w == b"UNRELATED"));
    assert_eq!(summary.render()[3].1, Value::Int(12));
    assert_eq!(
        serde_json::from_slice::<Summary>(&serde_json::to_vec(&summary).unwrap()).unwrap(),
        summary
    );
}
#[test]
fn scalar_rows_are_compact_and_overflow_is_atomic() {
    let c = clause(vec![
        Rule::Exists { verb: "put".into() },
        Rule::Count { verb: "put".into() },
        Rule::Counter {
            inc: "put".into(),
            dec: "del".into(),
            key: "v".into(),
        },
    ]);
    let mut summary = Summary::new(&c, None).unwrap();
    let mut history = vec![];
    for i in 0..100 {
        advance(
            &mut summary,
            &mut history,
            &numeric(act("put", "x", "", &[], i, "@a", 1), 3),
        );
    }
    assert_eq!(summary.live_acts(), 0);
    assert!(summary.encode().len() < 128);
    summary.rows[1] = RowData::Count(u64::MAX);
    let before = summary.clone();
    let a = numeric(act("put", "x", "", &[], 101, "@a", 1), 1);
    assert_eq!(summary.apply(&a, |_| false), Err(Error::Budget));
    assert_eq!(before, summary);
    summary.rows[1] = RowData::Count(100);
    summary.rows[2] = RowData::Counter(i128::MAX);
    let before = summary.clone();
    assert_eq!(summary.apply(&a, |_| false), Err(Error::Budget));
    assert_eq!(before, summary);
}
#[test]
fn derived_fields_require_earlier_eligible_materialized_maps() {
    for rs in [
        vec![Rule::Sum {
            field: "later".into(),
        }],
        vec![
            Rule::Events {
                verb: "put".into(),
                key: "v".into(),
            },
            Rule::Histogram { field: "f0".into() },
        ],
        vec![
            Rule::Count { verb: "put".into() },
            Rule::Sum { field: "f0".into() },
        ],
    ] {
        assert_eq!(
            Summary::new(&clause(rs), None),
            Err(Error::Invalid("derived source"))
        );
    }
    let c = clause(vec![
        rules()[6].clone(),
        Rule::Events {
            verb: "put".into(),
            key: "v".into(),
        },
        Rule::Histogram { field: "f0".into() },
        Rule::Sum { field: "f1".into() },
    ]);
    let mut summary = Summary::new(&c, None).unwrap();
    let mut history = vec![];
    for i in 0..4 {
        advance(
            &mut summary,
            &mut history,
            &numeric(act("put", "x", "", &[], i, "@a", 1), -2),
        );
    }
    assert_eq!(summary.render()[3].1, Value::Int(-8));
}

#[test]
fn plain_lww_loser_can_reemerge_only_in_scoped_rules() {
    let c = clause(all_plain());
    let a = act("put", "x", "high", &[], 1, "@a", 99);
    let b = act("put", "x", "low", &[], 2, "@a", 1);
    let d = act(
        "del",
        "x",
        "",
        core::slice::from_ref(&a.address),
        3,
        "@a",
        100,
    );
    let mut summary = Summary::new(&c, None).unwrap();
    let mut history = vec![];
    for a in [a, b, d] {
        advance(&mut summary, &mut history, &a)
    }
}
#[test]
fn known_profile_id_binds_v2_schema_and_rejects_old_bytes() {
    let c = clause(all_plain());
    let s = Summary::new(&c, None).unwrap();
    assert_eq!(
        s.profile_hash(),
        Summary::expected_profile_hash(&c).unwrap()
    );
    let mut reordered = c.clone();
    reordered.entries.swap(0, 1);
    assert_ne!(
        s.profile_hash(),
        Summary::expected_profile_hash(&reordered).unwrap()
    );
    assert_ne!(
        s.profile_hash(),
        crate::hash(b"cbcl/checkpoint/profile/v1", b"state-summary-v1")
    );
    assert_eq!(
        Summary::decode(&s.encode(), &reordered),
        Err(Error::Invalid("summary schema"))
    );
}

#[test]
fn compact_rows_incremental_work_does_not_scan_history() {
    let rs = rules();
    let c = clause(vec![
        rs[2].clone(),
        rs[3].clone(),
        rs[4].clone(),
        Rule::Count { verb: "put".into() },
        Rule::Exists { verb: "put".into() },
    ]);
    let mut summary = Summary::new(&c, None).unwrap();
    let mut seen = BTreeSet::new();
    let mut heads: Vec<Option<String>> = vec![None; 8];
    let _ = work::take();
    for i in 0..300 {
        let refs: Vec<_> = heads[i % 8].iter().cloned().collect();
        let a = act(
            "put",
            &alloc::format!("key{}", i % 8),
            "same",
            &refs,
            i as i64,
            "@a",
            i as u64,
        );
        summary.apply(&a, |id| seen.contains(id)).unwrap();
        heads[i % 8] = Some(a.address.clone());
        seen.insert(a.address);
    }
    let work = work::take();
    assert_eq!(work.incoming_metadata, 300);
    assert_eq!(work.pending_comparisons, 0);
    assert!(work.live_comparisons < 50 * 300);
    assert_eq!(summary.live_acts(), 24);
    assert_eq!(summary.pending_references(), 0);
    assert!(summary.encode().len() < 8192);
}

#[test]
fn all_sixteen_native_prefixes_cuts_and_helper_binding() {
    use crate::{
        certificate::SignedMessage,
        test_support::{parse, Keys},
    };
    use cbcl_core::{
        equivocation::message_content_hash,
        escrow::{CounterRule, Ownership},
        protocol::{NodeRef, StepDecl},
    };
    let resource = CounterRule {
        ownership: Ownership::Account,
        certification: Default::default(),
        floor: 0,
        ceiling: Some(20),
        initial_verb: "open".into(),
        initial_key: "alloc".into(),
        headroom_key: Some("room".into()),
        issuer: "issuer".into(),
        increment: ("mint".into(), "amount".into()),
        decrement: ("burn".into(), "amount".into()),
        transfer: Some(("pay".into(), "to".into(), "amount".into())),
        transfer_headroom: None,
    };
    let mut rs = all_plain();
    rs.push(Rule::Progress { verb: "put".into() });
    rs.push(Rule::BoundedCounter(Box::new(resource)));
    let c = clause(rs);
    let mut p = CausalProtocol {
        steps: BTreeMap::new(),
    };
    for (verb, parent, next) in [
        ("begin", None, Some("open")),
        ("open", Some("begin"), None),
        ("put", Some("open"), None),
        ("del", Some("open"), None),
    ] {
        p.steps.insert(
            verb.into(),
            StepDecl {
                performative: verb.into(),
                predecessors: parent
                    .into_iter()
                    .map(|s| NodeRef::Single(s.into()))
                    .collect(),
                successors: next
                    .into_iter()
                    .map(|s| NodeRef::Single(s.into()))
                    .collect(),
            },
        );
    }
    p.steps.get_mut("open").unwrap().successors = vec![NodeRef::Any(
        ["put".into(), "del".into()].into_iter().collect(),
    )];
    let signed = |text: &str| {
        SignedMessage::sign(parse(text), "@m0", &Keys)
            .unwrap()
            .authenticate(&Keys)
            .unwrap()
    };
    let root=signed("(with-roles ((issuer @m0) (holder @m0 @m1)) (hello :sender @m0 :thread \"all16\" :caused-by begin))");
    let open=signed(&alloc::format!("(lang all16 (open (@m0 @m1) :alloc ((@m0 10) (@m1 0)) :room ((@m0 5) (@m1 5)) :from @m0 :sender @m0 :thread \"all16\" :caused-by \"{}\"))",message_content_hash(root.simple())));
    let put = |nonce: i64, value: i64, refs: &[String]| {
        signed(&alloc::format!("(lang all16 (put (@m0 @m1) \"{nonce}\" :k \"x\" :v {value} :clock \"{}\" :replaces ({}) :sender @m0 :thread \"all16\" :caused-by \"{}\"))",Hlc::new(nonce as u64,0).render(),refs.iter().map(|s|alloc::format!("\"{s}\"")).collect::<Vec<_>>().join(" "),message_content_hash(open.simple())))
    };
    let a = put(1, 3, &[]);
    let b = put(2, 5, core::slice::from_ref(&a.address));
    let h = vec![root, open, a, b];
    for protocol in [None, Some(&p)] {
        let mut summary = Summary::new(&c, protocol).unwrap();
        let mut seen = vec![];
        for a in &h {
            advance(&mut summary, &mut seen, a);
            let before = summary.clone();
            advance(&mut summary, &mut seen, a);
            assert_eq!(before, summary);
        }
        assert_eq!(summary.render(), state::fold(&c, protocol, &h));
        assert!(Summary::decode(&summary.encode(), &c).is_err());
        assert!(summary.progress_resume("put").is_some());
        for cut in 0..=h.len() {
            let mut resume = Summary::new(&c, protocol).unwrap();
            let mut seen = vec![];
            for a in &h[..cut] {
                advance(&mut resume, &mut seen, a)
            }
            resume = Summary::decode_for(&resume.encode(), &c, protocol).unwrap();
            for a in &h[cut..] {
                advance(&mut resume, &mut seen, a)
            }
            assert_eq!(resume, summary);
        }
        if protocol.is_some() {
            assert!(Summary::decode_for(&summary.encode(), &c, None).is_err());
            assert!(summary.global_progress_resume().is_some());
        }
    }
}

#[test]
fn native_identity_variants_have_identical_projected_summary_roots() {
    use cbcl_core::message::{Recipients, WrapperType};
    let c = clause(all_plain());
    let base = act("put", "x", "red", &[], 1, "@a", 1);
    let mut states = vec![];
    for (recipient, signature) in [
        (Some(Recipients::One("@r".into())), "sig-A"),
        (
            Some(Recipients::Set(["@r".into()].into_iter().collect())),
            "sig-B",
        ),
    ] {
        let mut message = base.message.clone();
        let Message::Dialect { inner, .. } = &mut message else {
            panic!("dialect")
        };
        let Message::Simple {
            recipient: slot, ..
        } = inner.as_mut()
        else {
            panic!("simple")
        };
        *slot = recipient;
        let a = Act::from_message(
            Message::Wrapped {
                wrapper: WrapperType::Signed,
                params: vec![SExpr::Atom(Atom::Symbol("@a".into())), s(signature)],
                content: Box::new(message),
            },
            "@a",
        )
        .unwrap();
        let original = a.clone();
        let mut summary = Summary::new(&c, None).unwrap();
        summary.apply(&a, |_| false).unwrap();
        assert_eq!(a, original);
        states.push(summary);
    }
    assert_eq!(states[0], states[1]);
    assert_eq!(states[0].hash(), states[1].hash());
}
#[test]
fn exact_precoverage_footprint_matches_actual_update_queries() {
    let c = clause(all_plain());
    let a = act("put", "x", "red", &[], 1, "@a", 1);
    let b = act(
        "put",
        "y",
        "blue",
        core::slice::from_ref(&a.address),
        2,
        "@b",
        2,
    );
    let mut summary = Summary::new(&c, None).unwrap();
    summary.apply(&a, |_| false).unwrap();
    let expected: BTreeSet<_> = summary
        .query_ids(&b)
        .unwrap()
        .into_iter()
        .chain(core::iter::once(b.address.clone()))
        .collect();
    let visited = core::cell::RefCell::new(BTreeSet::new());
    summary
        .apply(&b, |id| {
            visited.borrow_mut().insert(id.to_string());
            id == a.address
        })
        .unwrap();
    assert_eq!(expected, visited.into_inner());
}
