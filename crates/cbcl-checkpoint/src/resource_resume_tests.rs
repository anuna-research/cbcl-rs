use super::*;
use crate::{
    certificate::SignedMessage,
    test_support::{parse, Keys},
};
use alloc::{format, vec};
fn rule() -> CounterRule {
    CounterRule {
        ownership: escrow::Ownership::Account,
        certification: Default::default(),
        floor: 0,
        ceiling: Some(20),
        initial_verb: "open".into(),
        initial_key: "alloc".into(),
        headroom_key: Some("room".into()),
        issuer: "issuer".into(),
        increment: ("mint".into(), "amount".into()),
        decrement: ("burn".into(), "amount".into()),
        transfer: Some(("pay".into(), "recipient".into(), "amount".into())),
        transfer_headroom: Some(("give-room".into(), "recipient".into(), "amount".into())),
    }
}
fn signed(text: &str, key: &str) -> Act {
    SignedMessage::sign(parse(text), key, &Keys)
        .unwrap()
        .authenticate(&Keys)
        .unwrap()
}
fn bootstrap() -> Vec<Act> {
    let root=signed("(with-roles ((issuer @m0) (holder @m0 @m1)) (hello :sender @m0 :thread \"resource\" :caused-by begin))","@m0");
    let open=signed(&format!("(lang resource (open (@m0 @m1) :alloc ((@m0 10) (@m1 0)) :room ((@m0 5) (@m1 5)) :from @m0 :sender @m0 :thread \"resource\" :caused-by {}))",root.address),"@m0");
    vec![root, open]
}
fn operation(
    verb: &str,
    signer: &str,
    prev: &str,
    deps: &[String],
    amount: i64,
    nonce: usize,
) -> Act {
    signed(&format!("(lang resource ({verb} (@m0 @m1) :amount {amount} :recipient @m1 :escrow-prev {prev} :escrow-deps ({}) :escrow-nonce {nonce} :from {signer} :sender {signer} :thread \"resource\" :caused-by begin))",deps.join(" ")),signer)
}
fn compare(c: &CounterRule, history: &[Act]) {
    let mut s = Summary::default();
    let mut covered = BTreeSet::new();
    let mut seen = Vec::new();
    assert_eq!(s.render(c), escrow::observe(c, &seen).value());
    assert_eq!(Summary::decode(&s.encode(), c).unwrap(), s);
    for a in history {
        let footprint: BTreeSet<_> = s.query_ids(c, a).unwrap().into_iter().collect();
        let queried = core::cell::RefCell::new(BTreeSet::new());
        s.apply(c, a, |id| {
            queried.borrow_mut().insert(String::from(id));
            covered.contains(id)
        })
        .unwrap();
        assert_eq!(queried.into_inner(), footprint, "resource proof footprint");
        covered.insert(a.address.clone());
        seen.push(a.clone());
        assert_eq!(
            *s.outcome,
            escrow::observe(c, &seen),
            "prefix {}",
            seen.len()
        );
        assert_eq!(s.render(c), escrow::observe(c, &seen).value());
        let restored = Summary::decode(&s.encode(), c).unwrap();
        assert_eq!(restored, s);
    }
    for cut in [0, 1.min(history.len()), history.len() / 2, history.len()] {
        let mut s = Summary::default();
        let mut covered = BTreeSet::new();
        for a in &history[..cut] {
            s.apply(c, a, |id| covered.contains(id)).unwrap();
            covered.insert(a.address.clone());
        }
        let mut s = Summary::decode(&s.encode(), c).unwrap();
        for a in &history[cut..] {
            s.apply(c, a, |id| covered.contains(id)).unwrap();
            covered.insert(a.address.clone());
        }
        assert_eq!(
            s.render(c),
            escrow::observe(c, history).value(),
            "cut {cut}"
        );
    }
}
#[test]
fn native_ready_prefixes_cuts_delayed_operations_and_duplicates() {
    let c = rule();
    let mut h = bootstrap();
    let open = h[1].address.clone();
    let pay = operation("pay", "@m0", &open, &[], 4, 1);
    let burn = operation(
        "burn",
        "@m1",
        &open,
        core::slice::from_ref(&pay.address),
        2,
        2,
    );
    let mint = operation("mint", "@m0", &pay.address, &[], 3, 3);
    h.extend([pay.clone(), burn.clone(), mint.clone(), burn]);
    compare(&c, &h);
    assert!(
        matches!(escrow::observe(&c, &h), Outcome::Ready(_)),
        "{:?}",
        escrow::observe(&c, &h)
    );
    let mut reverse = h.clone();
    reverse.reverse();
    compare(&c, &reverse);
    let mut delayed = bootstrap();
    delayed.extend([mint, pay]);
    compare(&c, &delayed);
}
#[test]
fn missing_to_wrong_type_dependencies_before_and_after_cut() {
    let c = rule();
    let base = bootstrap();
    let noise=signed("(lang resource (tell @m1 :unrelated \"body\" :from @m0 :sender @m0 :thread \"resource\" :caused-by begin))","@m0");
    let bad = operation(
        "burn",
        "@m0",
        &base[1].address,
        core::slice::from_ref(&noise.address),
        1,
        4,
    );
    let mut h = base.clone();
    h.push(bad.clone());
    assert!(matches!(escrow::observe(&c, &h), Outcome::Pending(_)));
    h.push(noise.clone());
    compare(&c, &h);
    assert!(
        matches!(escrow::observe(&c,&h),Outcome::Fault{reason,..}if reason=="foreign resource dependency")
    );
    let mut old = base;
    old.extend([noise, bad]);
    compare(&c, &old);
}
#[test]
fn native_faults_keep_tags_and_evidence() {
    let c = rule();
    let base = bootstrap();
    let open = &base[1].address;
    let pay = operation("pay", "@m0", open, &[], 4, 1);
    let fork = operation("burn", "@m0", open, &[], 1, 2);
    let wrong_owner = operation("burn", "@m1", &pay.address, &[], 1, 3);
    let unauthorized = operation("mint", "@m1", open, &[], 1, 4);
    let overspend = operation("burn", "@m1", open, &[], 1, 5);
    for (tail, tag) in [
        (vec![pay.clone(), fork], "owner fork"),
        (vec![pay, wrong_owner], "wrong owner previous link"),
        (vec![unauthorized], "unauthorized increment"),
        (vec![overspend], "insufficient rights"),
        (
            vec![operation("burn", "@m0", open, &[], 0, 6)],
            "resource amount must be positive",
        ),
        (
            vec![operation("mint", "@m0", open, &[], 6, 7)],
            "insufficient headroom",
        ),
        (
            vec![operation("burn", "@m0", "not-an-address", &[], 1, 8)],
            "missing escrow previous address",
        ),
        (
            vec![operation(
                "burn",
                "@m0",
                open,
                &[String::from("not-an-address")],
                1,
                9,
            )],
            "invalid escrow dependency",
        ),
    ] {
        let mut h = base.clone();
        h.extend(tail);
        compare(&c, &h);
        assert!(
            matches!(escrow::observe(&c,&h),Outcome::Fault{reason,..}if reason==tag),
            "{tag}: {:?}",
            escrow::observe(&c, &h)
        );
    }
    let mut bounded = c.clone();
    bounded.ceiling = Some(19);
    compare(&bounded, &base);
    assert!(
        matches!(escrow::observe(&bounded,&base),Outcome::Fault{reason,..}if reason=="initial rights plus headroom must equal ceiling minus floor")
    );
}
#[test]
fn collective_and_quorum_remain_native_faults_not_certificate_authority() {
    for mode in [0, 1] {
        let mut c = rule();
        if mode == 0 {
            c.ownership = escrow::Ownership::Collective;
        } else {
            c.certification = cbcl_core::certification::Certification::QuorumBudget {
                validators: None,
                faults: None,
            };
        }
        let h = bootstrap();
        compare(&c, &h);
        assert!(matches!(escrow::observe(&c, &h), Outcome::Fault { .. }));
    }
}
#[test]
fn projection_drops_unrelated_bodies_and_validation_is_atomic() {
    let c = rule();
    let mut h = bootstrap();
    let payload = "x".repeat(60_000);
    let extra=signed(&format!("(lang resource (tell @m1 :payload \"{payload}\" :sender @m0 :from @m0 :thread \"resource\" :caused-by begin))"),"@m0");
    h.push(extra);
    let heavy = signed(&format!("(lang resource (burn (@m0 @m1) :amount 1 :escrow-prev {} :escrow-deps () :payload \"{payload}\" :from @m0 :sender @m0 :thread \"resource\" :caused-by begin))", h[1].address), "@m0");
    h.push(heavy);
    let mut s = Summary::default();
    let mut covered = BTreeSet::new();
    for a in &h {
        s.apply(&c, a, |id| covered.contains(id)).unwrap();
        covered.insert(a.address.clone());
    }
    assert_eq!(s.facts.len(), 3);
    assert!(s.encode().len() < 4096);
    let raw_bytes: usize = h
        .iter()
        .map(|a| codec::message_bytes(&a.message).len())
        .sum();
    assert!(s.encode().len() * 10 < raw_bytes);
    assert_eq!(*s.outcome, escrow::observe(&c, &h));
    let mut bad = h[1].clone();
    bad.address.push('x');
    let before = s.clone();
    assert!(s.apply(&c, &bad, |_| false).is_err());
    assert_eq!(before, s);
    let mut other = c.clone();
    other.floor = 1;
    assert!(Summary::decode(&s.encode(), &other).is_err());
    let mut trailing = s.encode();
    trailing.push(0);
    assert!(Summary::decode(&trailing, &c).is_err());
    let json = serde_json::to_vec(&s).unwrap();
    assert_eq!(serde_json::from_slice::<Summary>(&json).unwrap(), s);
}
#[test]
fn projected_cycle_uses_native_cycle_fault_not_a_balance_shortcut() {
    // Abstract imported fact graph: an actual native hash cycle is not fabricated.
    let c = rule();
    let h = bootstrap();
    let a = operation("burn", "@m0", &h[1].address, &[], 1, 1);
    let b = operation("burn", "@m0", &a.address, &[], 1, 2);
    let mut s = Summary::default();
    for x in h.iter().chain([&a, &b]) {
        s.apply(&c, x, |_| false).unwrap();
    }
    s.facts.get_mut(&a.address).unwrap().fields.insert(
        escrow::PREV.into(),
        SExpr::Atom(Atom::Symbol(b.address.clone())),
    );
    *s.outcome = recompute(&c, &s.facts, &s.known);
    assert!(matches!(&*s.outcome,Outcome::Fault{reason,..}if reason=="cyclic escrow dependencies"));
    let restored = Summary::decode(&s.encode(), &c).unwrap();
    assert_eq!(restored.outcome, s.outcome);
}

#[test]
fn multihash_links_resolve_to_state_wire_facts_without_false_wrong_type() {
    let c = rule();
    let base = bootstrap();
    let root = base[0].clone();
    let native_root = crate::certificate::native(&root.address);
    let open=signed(&format!("(lang resource (open (@m0 @m1) :alloc ((@m0 10) (@m1 0)) :room ((@m0 5) (@m1 5)) :from @m0 :sender @m0 :thread \"resource\" :caused-by {native_root}))"),"@m0");
    assert_eq!(open.predecessors[0], root.address);
    // Before the shared projection's alias correction, native observe looked
    // this colon spelling up directly in the dash-keyed Act index and stayed pending.
    let pay = operation(
        "pay",
        "@m0",
        &crate::certificate::native(&open.address),
        &[],
        4,
        99,
    );
    let burn = operation(
        "burn",
        "@m1",
        &crate::certificate::native(&open.address),
        &[crate::certificate::native(&pay.address)],
        2,
        100,
    );
    let history = vec![root, open, pay, burn];
    compare(&c, &history);
    assert!(matches!(escrow::observe(&c, &history), Outcome::Ready(_)));
    let mut s = Summary::default();
    let mut covered = BTreeSet::new();
    for a in &history {
        assert!(s
            .query_ids(&c, a)
            .unwrap()
            .iter()
            .all(|id| cbcl_core::r7::is_address(id)));
        s.apply(&c, a, |id| covered.contains(id)).unwrap();
        covered.insert(a.address.clone());
    }
}

#[test]
fn native_headroom_transfer_and_late_funding_preserve_account_arithmetic() {
    let mut c = rule();
    c.issuer = "holder".into();
    let base = bootstrap();
    let give = operation("give-room", "@m0", &base[1].address, &[], 2, 1);
    let mint = operation(
        "mint",
        "@m1",
        &base[1].address,
        core::slice::from_ref(&give.address),
        6,
        2,
    );
    let mut history = base.clone();
    history.extend([give.clone(), mint.clone()]);
    compare(&c, &history);
    let Outcome::Ready(snapshot) = escrow::observe(&c, &history) else {
        panic!("native headroom ready");
    };
    assert_eq!(snapshot.value, 16);
    assert_eq!(snapshot.rights["@m1"], 6);
    assert_eq!(snapshot.headroom.as_ref().unwrap()["@m1"], 1);
    let mut late = base;
    late.extend([mint, give]);
    compare(&c, &late);
}

#[test]
fn accepted_native_recipient_aliases_have_identical_resource_snapshots() {
    use cbcl_core::message::{Message, Performative, Recipients, WrapperType};
    fn alias_unsigned(m: &Message) -> Message {
        match m {
            Message::Wrapped {
                wrapper: WrapperType::Signed,
                content,
                ..
            } => alias_unsigned(content),
            Message::Wrapped {
                wrapper,
                params,
                content,
            } => Message::Wrapped {
                wrapper: *wrapper,
                params: params.clone(),
                content: Box::new(alias_unsigned(content)),
            },
            Message::Dialect {
                dialect_name,
                inner,
            } => Message::Dialect {
                dialect_name: dialect_name.clone(),
                inner: Box::new(alias_unsigned(inner)),
            },
            Message::Simple { .. } => {
                let mut out = m.clone();
                if let Message::Simple {
                    recipient,
                    performative,
                    ..
                } = &mut out
                {
                    *recipient = match recipient.take() {
                        None => Some(Recipients::Set(BTreeSet::new())),
                        Some(Recipients::One(r)) => Some(Recipients::Set(BTreeSet::from([r]))),
                        other => other,
                    };
                    if let Performative::Core(p) = performative {
                        *performative = Performative::Custom(p.as_str().into());
                    }
                }
                out
            }
            _ => panic!("resource native simple"),
        }
    }
    let c = rule();
    let root = bootstrap().remove(0);
    let open=signed(&format!("(lang resource (open @m0 :alloc ((@m0 10) (@m1 0)) :room ((@m0 5) (@m1 5)) :from @m0 :sender @m0 :thread \"resource\" :caused-by {}))",root.address),"@m0");
    let burn=signed(&format!("(lang resource (burn @m1 :amount 1 :escrow-prev {} :escrow-deps () :from @m0 :sender @m0 :thread \"resource\" :caused-by begin))",open.address),"@m0");
    let canonical = vec![root, open, burn];
    let aliases: Vec<_> = canonical
        .iter()
        .enumerate()
        .map(|(index, a)| {
            if index == 0 {
                a.clone()
            } else {
                SignedMessage::sign(alias_unsigned(&a.message), &a.signer, &Keys)
                    .unwrap()
                    .authenticate(&Keys)
                    .unwrap()
            }
        })
        .collect();
    for (index, (a, b)) in canonical.iter().zip(&aliases).enumerate() {
        if index == 0 {
            continue;
        }
        assert_eq!(a.address, b.address);
        assert_ne!(a.message, b.message);
        assert_eq!(
            escrow::project_resource_fact(&c, a).unwrap(),
            escrow::project_resource_fact(&c, b).unwrap()
        );
    }
    assert_eq!(
        escrow::observe(&c, &canonical),
        escrow::observe(&c, &aliases)
    );
    let mut members = [Summary::default(), Summary::default()];
    for (s, history) in members.iter_mut().zip([&canonical, &aliases]) {
        let mut covered = BTreeSet::new();
        for a in history {
            s.apply(&c, a, |id| covered.contains(id)).unwrap();
            covered.insert(a.address.clone());
        }
    }
    assert_eq!(members[0].encode(), members[1].encode());
    let before = members[0].encode();
    for a in &aliases {
        members[0].apply(&c, a, |_| true).unwrap();
    }
    assert_eq!(members[0].encode(), before);
    let attempts: Vec<_> = canonical.iter().chain(&aliases).cloned().collect();
    // Direct observe retains diagnostics for conflicting raw AST attempts.
    // The checkpoint contract uses an ID-normalized accepted store. Resource
    // state::fold itself deliberately preserves diagnostics on a raw attempt list.
    assert!(
        matches!(escrow::observe(&c,&attempts),Outcome::Fault{reason,..}if reason=="conflicting authenticated identity")
    );
    let clause = cbcl_core::state::StateClause {
        entries: vec![cbcl_core::state::Entry::Field {
            name: "resource".into(),
            rule: cbcl_core::state::Rule::BoundedCounter(Box::new(c.clone())),
        }],
    };
    let mut ids = BTreeSet::new();
    let accepted: Vec<_> = attempts
        .iter()
        .filter(|a| ids.insert(a.address.clone()))
        .cloned()
        .collect();
    assert_eq!(
        cbcl_core::state::fold(&clause, None, &accepted)[0].1,
        members[0].render(&c)
    );
    assert_eq!(
        cbcl_core::state::fold(&clause, None, &attempts)[0].1,
        escrow::observe(&c, &attempts).value()
    );
}
