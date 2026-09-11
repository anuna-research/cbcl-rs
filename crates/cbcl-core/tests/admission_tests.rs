//! Execution invariants and scheduler regressions. TestGate is a deterministic
//! test fixture, NOT cryptographic authentication for deployment.
use cbcl_core::admission::{AdmissionError, AdmissionGate, AdmissionMonitor, AdmissionState};
use cbcl_core::canonical::{canonical_encode, dialect_hash};
use cbcl_core::dialect::{Dialect, PerformativeDef, ResourceBounds};
use cbcl_core::message::{CausedBy, Message};
use cbcl_core::projection::verify_causal_for_role;
use cbcl_core::protocol::{CausalProtocol, NodeRef, StepDecl, VerificationResult};
use cbcl_core::role::{parse_roles, parse_wrapper_cast, Endpoint, RoleAnnotation};
use cbcl_core::sexpr::SExpr;
use cbcl_core::store::{ContentHash, MessageStore, ThreadId, ThreadedMessageStore};
use sha2::{Digest, Sha256};

struct TestGate;
fn identity(m: &Message) -> ContentHash {
    let digest = Sha256::digest(canonical_encode(&SExpr::from(m.clone())));
    ContentHash(format!("sha256:{digest:x}"))
}
impl AdmissionGate for TestGate {
    fn authenticate(&self, m: &Message) -> Result<ContentHash, String> {
        if format!("{}", SExpr::from(m.clone())).contains("bad-signature") {
            Err("test authentication failure".into())
        } else {
            Ok(identity(m))
        }
    }
}
fn msg(s: &str) -> Message {
    Message::try_from(&s.parse::<SExpr>().unwrap()).unwrap()
}
fn ep(role: &str) -> Endpoint {
    Endpoint {
        role: role.into(),
        occupant: None,
    }
}
fn dialect() -> Dialect {
    let nodes = [
        (
            "start",
            "a",
            vec!["b", "c"],
            vec![NodeRef::Single("begin".into())],
            vec!["left", "right"],
        ),
        (
            "left",
            "b",
            vec!["a", "c"],
            vec![NodeRef::Single("start".into())],
            vec!["finish"],
        ),
        (
            "right",
            "c",
            vec!["a", "b"],
            vec![NodeRef::Single("start".into())],
            vec!["finish"],
        ),
        (
            "finish",
            "a",
            vec!["b", "c"],
            vec![NodeRef::All(
                ["left".into(), "right".into()].into_iter().collect(),
            )],
            vec![],
        ),
    ];
    let mut d = Dialect {
        name: "admission".into(),
        extends: vec![],
        author: None,
        roles: parse_roles(&"(a b c)".parse().unwrap()).unwrap(),
        causal_locality: Default::default(),
        performatives: nodes
            .iter()
            .map(|(name, from, to, _, _)| PerformativeDef {
                name: (*name).into(),
                params: vec![],
                template: "t".parse().unwrap(),
                role: Some(RoleAnnotation {
                    from: (*from).into(),
                    to: to.iter().map(|s| (*s).into()).collect(),
                }),
            })
            .collect(),
        resources: ResourceBounds {
            max_depth: 8,
            max_expansion_size: 512,
            verification_time_ms: 10,
        },
        examples: vec![],
        signature: None,
        hash: None,
        protocol: None,
        shapes: vec![],
        causal_protocol: Some(CausalProtocol {
            steps: nodes
                .into_iter()
                .map(|(name, _, _, predecessors, successors)| {
                    (
                        name.into(),
                        StepDecl {
                            performative: name.into(),
                            predecessors,
                            successors: successors
                                .into_iter()
                                .map(|s| NodeRef::Single(s.into()))
                                .collect(),
                        },
                    )
                })
                .chain(std::iter::once((
                    "begin".into(),
                    StepDecl {
                        performative: "begin".into(),
                        predecessors: vec![],
                        successors: vec![NodeRef::Single("start".into())],
                    },
                )))
                .collect(),
        }),
    };
    d.hash = Some(dialect_hash(&d));
    d
}
fn root(d: &Dialect) -> Message {
    msg(&format!("(with-roles ((a @a) (b @b) (c @c)) :dialect {} (signed @a \"sig\" (hello :thread \"t\" :caused-by begin)))", d.hash.as_ref().unwrap()))
}
fn act(perf: &str, signer: &str, recipients: &str, payload: &str, predecessor: &str) -> Message {
    msg(&format!("(signed {signer} \"sig\" (lang admission ({perf} ({recipients}) \"{payload}\" :thread \"t\" :caused-by {predecessor})))"))
}
fn fixture() -> (Dialect, Message, Vec<Message>) {
    let d = dialect();
    let root = root(&d);
    let start = act("start", "@a", "@b @c", "start", &identity(&root).0);
    let left = act("left", "@b", "@a @c", "left", &identity(&start).0);
    let right = act("right", "@c", "@a @b", "right", &identity(&start).0);
    let finish = act(
        "finish",
        "@a",
        "@b @c",
        "finish",
        &format!("({} {})", identity(&left).0, identity(&right).0),
    );
    (d, root, vec![start, left, right, finish])
}
fn monitor(d: &Dialect, r: &Message, role: &str) -> AdmissionMonitor<TestGate> {
    AdmissionMonitor::new(d.clone(), ep(role), r.clone(), TestGate).unwrap()
}
fn assert_invariant(
    m: &AdmissionMonitor<TestGate>,
    d: &Dialect,
    r: &Message,
    candidates: &[Message],
) {
    let Message::Wrapped { params, .. } = r else {
        unreachable!()
    };
    let cast = parse_wrapper_cast(params, &d.roles).unwrap();
    for message in std::iter::once(r).chain(candidates) {
        let hash = identity(message);
        if m.accepted().contains(&hash, m.thread()) {
            assert_eq!(m.state(&hash), Some(&AdmissionState::Accepted));
            assert!(m.received_message(&hash).is_some());
            match message.innermost_simple().unwrap().caused_by() {
                Some(CausedBy::Single(h)) => {
                    assert!(m.accepted().contains(&ContentHash(h.clone()), m.thread()))
                }
                Some(CausedBy::Multiple(hs)) => {
                    for h in hs {
                        assert!(m.accepted().contains(&ContentHash(h.clone()), m.thread()));
                    }
                }
                _ => assert_eq!(&hash, m.root()),
            }
            assert_eq!(
                verify_causal_for_role(
                    message,
                    &ep("a"),
                    d,
                    &cast,
                    m.accepted(),
                    m.thread(),
                    m.root()
                ),
                VerificationResult::Valid
            );
        }
    }
}

#[test]
fn all_delivery_permutations_preserve_safety_and_eventually_accept_fanin() {
    let (d, root, trace) = fixture();
    for a in 0..4 {
        for b in 0..4 {
            for c in 0..4 {
                for e in 0..4 {
                    let order = [a, b, c, e];
                    if order
                        .iter()
                        .collect::<std::collections::BTreeSet<_>>()
                        .len()
                        != 4
                    {
                        continue;
                    }
                    for role in ["a", "b", "c"] {
                        let mut m = monitor(&d, &root, role);
                        assert!(!m.accepted().contains(m.root(), m.thread()));
                        for index in order {
                            m.receive(trace[index].clone()).unwrap();
                            m.step();
                            assert_invariant(&m, &d, &root, &trace);
                        }
                        m.drain_ready();
                        assert_eq!(m.pending_len(), 0);
                        for message in &trace {
                            assert_eq!(
                                m.state(&identity(message)),
                                Some(&AdmissionState::Accepted)
                            );
                        }
                        assert_invariant(&m, &d, &root, &trace);
                    }
                }
            }
        }
    }
}

#[test]
fn invalid_received_predecessor_cannot_justify_accepted_child() {
    let (d, root, _) = fixture();
    let mut m = monitor(&d, &root, "c");
    let bad_start = act("start", "@b", "@b @c", "wrong sender", &identity(&root).0);
    let child = act("left", "@b", "@a @c", "child", &identity(&bad_start).0);
    m.receive(child.clone()).unwrap();
    m.receive(bad_start.clone()).unwrap();
    m.drain_ready();
    assert!(matches!(
        m.state(&identity(&bad_start)),
        Some(AdmissionState::Rejected(_))
    ));
    assert_eq!(m.state(&identity(&child)), Some(&AdmissionState::Pending));
    assert!(!m.accepted().contains(&identity(&bad_start), m.thread()));
    assert!(!m.accepted().contains(&identity(&child), m.thread()));
}

#[test]
fn pending_fanin_is_not_rejected_early_and_duplicates_do_not_reapply() {
    let (d, root, trace) = fixture();
    let mut m = monitor(&d, &root, "a");
    m.receive(trace[3].clone()).unwrap();
    m.receive(trace[0].clone()).unwrap();
    m.receive(trace[1].clone()).unwrap();
    m.drain_ready();
    assert_eq!(
        m.state(&identity(&trace[3])),
        Some(&AdmissionState::Pending)
    );
    let before = m.pending_len();
    m.receive(trace[3].clone()).unwrap();
    assert_eq!(m.pending_len(), before);
    m.receive(trace[2].clone()).unwrap();
    let events = m.drain_ready();
    assert_eq!(
        events
            .iter()
            .filter(|e| e.hash == identity(&trace[3]) && e.state == AdmissionState::Accepted)
            .count(),
        1
    );
    m.receive(trace[3].clone()).unwrap();
    assert!(m.drain_ready().is_empty());
}

#[test]
fn root_must_be_accepted_before_a_reference_is_rewritten_to_begin() {
    let (d, root, trace) = fixture();
    let mut m = monitor(&d, &root, "a");
    m.receive(trace[0].clone()).unwrap();
    assert!(!m.accepted().contains(m.root(), m.thread()));
    assert_eq!(m.step().unwrap().hash, identity(&root));
    assert!(!m.accepted().contains(&identity(&trace[0]), m.thread()));
    assert_eq!(m.step().unwrap().state, AdmissionState::Accepted);
}

#[test]
fn new_arrivals_do_not_starve_an_enabled_candidate() {
    let (d, root, trace) = fixture();
    let mut m = monitor(&d, &root, "a");
    m.drain_ready();
    let missing = act("left", "@b", "@a @c", "missing", "sha256:missing");
    m.receive(missing).unwrap();
    m.receive(trace[0].clone()).unwrap();
    for i in 0..3 {
        let noise = act(
            "start",
            "@a",
            "@b @c",
            &format!("noise-{i}"),
            &identity(&root).0,
        );
        m.receive(noise).unwrap();
        m.step();
    }
    assert_eq!(
        m.state(&identity(&trace[0])),
        Some(&AdmissionState::Accepted)
    );
}

#[test]
fn strict_context_rejects_unpinned_duplicate_and_derived_dialects() {
    let (d, root, _) = fixture();
    let unpinned = msg("(with-roles ((a @a) (b @b) (c @c)) (signed @a \"sig\" (hello :thread \"t\" :caused-by begin)))");
    assert!(AdmissionMonitor::new(d.clone(), ep("a"), unpinned, TestGate).is_err());
    let mut duplicate = d.clone();
    duplicate
        .performatives
        .push(duplicate.performatives[0].clone());
    assert!(AdmissionMonitor::new(duplicate, ep("a"), root.clone(), TestGate).is_err());
    let mut derived = d.clone();
    derived.causal_locality = cbcl_core::role::CausalLocality::Derive(Default::default());
    assert!(AdmissionMonitor::new(derived, ep("a"), root.clone(), TestGate).is_err());
    let mut altered = d.clone();
    altered.performatives[0].template = "changed".parse().unwrap();
    assert!(AdmissionMonitor::new(altered, ep("a"), root.clone(), TestGate).is_err());
    assert!(AdmissionMonitor::new(d, ep("absent"), root, TestGate).is_err());
}

#[test]
fn gate_and_thread_failures_leave_history_unchanged() {
    let (d, root, trace) = fixture();
    let mut m = monitor(&d, &root, "a");
    let bad_sig =
        msg(&format!("{}", SExpr::from(trace[0].clone())).replace("\"sig\"", "\"bad-signature\""));
    assert!(matches!(
        m.receive(bad_sig),
        Err(AdmissionError::Authentication(_))
    ));
    let wrong_thread =
        msg(&format!("{}", SExpr::from(trace[0].clone())).replace("\"t\"", "\"other\""));
    assert!(matches!(
        m.receive(wrong_thread),
        Err(AdmissionError::Message(_))
    ));
    let second_root =
        msg(&format!("{}", SExpr::from(root.clone())).replace("\"sig\"", "\"sig-2\""));
    assert!(matches!(
        m.receive(second_root),
        Err(AdmissionError::Message(_))
    ));
    let naked_begin = act("start", "@a", "@b @c", "unanchored", "begin");
    assert!(m.receive(naked_begin).is_err());
    assert_eq!(m.pending_len(), 1);
    assert!(!m.accepted().contains(m.root(), m.thread()));
}

#[test]
fn hash_conflicts_cannot_replace_pending_or_accepted_records() {
    struct ConstantGate;
    impl AdmissionGate for ConstantGate {
        fn authenticate(&self, _: &Message) -> Result<ContentHash, String> {
            Ok(ContentHash("same".into()))
        }
    }
    let (d, root, trace) = fixture();
    let mut m = AdmissionMonitor::new(d, ep("a"), root.clone(), ConstantGate).unwrap();
    assert!(matches!(
        m.receive(trace[0].clone()),
        Err(AdmissionError::ConflictingIdentity(_))
    ));
    m.drain_ready();
    assert!(matches!(
        m.receive(trace[0].clone()),
        Err(AdmissionError::ConflictingIdentity(_))
    ));
    assert_eq!(m.accepted().lookup(m.root()), Some(&root));
}

#[test]
fn asynchronous_endpoint_union_remains_closed_and_valid_without_coverage() {
    let (d, root, trace) = fixture();
    let mut a = monitor(&d, &root, "a");
    let mut b = monitor(&d, &root, "b");
    a.receive(trace[0].clone()).unwrap();
    a.receive(trace[1].clone()).unwrap();
    a.drain_ready();
    b.receive(trace[0].clone()).unwrap();
    b.receive(trace[2].clone()).unwrap();
    b.drain_ready();
    assert!(!b.accepted().contains(&identity(&trace[1]), b.thread()));
    assert!(!a.accepted().contains(&identity(&trace[2]), a.thread()));
    let mut union = ThreadedMessageStore::new();
    for message in std::iter::once(&root).chain(&trace) {
        let hash = identity(message);
        if a.accepted().contains(&hash, a.thread()) || b.accepted().contains(&hash, b.thread()) {
            union.append(hash, ThreadId("t".into()), message.clone());
        }
    }
    let Message::Wrapped { params, .. } = &root else {
        unreachable!()
    };
    let cast = parse_wrapper_cast(params, &d.roles).unwrap();
    for message in std::iter::once(&root).chain(&trace[..3]) {
        assert_eq!(
            verify_causal_for_role(message, &ep("a"), &d, &cast, &union, a.thread(), a.root()),
            VerificationResult::Valid
        );
    }
}

#[test]
fn mixed_wrong_and_missing_fanin_waits_for_resolution_before_rejection() {
    let (d, root, trace) = fixture();
    let mut m = monitor(&d, &root, "a");
    let wrong_fanin = act(
        "finish",
        "@a",
        "@b @c",
        "wrong types",
        &format!("({} {})", identity(&trace[0]).0, identity(&trace[2]).0),
    );
    m.receive(trace[0].clone()).unwrap();
    m.receive(wrong_fanin.clone()).unwrap();
    m.drain_ready();
    assert_eq!(
        m.state(&identity(&wrong_fanin)),
        Some(&AdmissionState::Pending)
    );
    m.receive(trace[2].clone()).unwrap();
    m.drain_ready();
    assert!(matches!(
        m.state(&identity(&wrong_fanin)),
        Some(AdmissionState::Rejected(_))
    ));
    assert!(!m.accepted().contains(&identity(&wrong_fanin), m.thread()));
}

#[test]
fn indexed_endpoint_uses_occupant_identity_and_full_member_fanin() {
    use cbcl_core::role::AgentKey;
    let mut d = dialect();
    // A sealed group sends starts to a; a's terminal result requires all of them.
    d.roles = parse_roles(&"(a (* b))".parse().unwrap()).unwrap();
    d.performatives
        .retain(|p| p.name == "start" || p.name == "finish");
    d.performatives[0].role = Some(RoleAnnotation {
        from: "b".into(),
        to: ["a".into()].into_iter().collect(),
    });
    d.performatives[1].role = Some(RoleAnnotation {
        from: "a".into(),
        to: Default::default(),
    });
    let protocol = d.causal_protocol.as_mut().unwrap();
    protocol
        .steps
        .retain(|name, _| ["begin", "start", "finish"].contains(&name.as_str()));
    protocol.steps.get_mut("start").unwrap().successors = vec![NodeRef::Single("finish".into())];
    protocol.steps.get_mut("finish").unwrap().predecessors =
        vec![NodeRef::All(["start".into()].into_iter().collect())];
    d.hash = Some(dialect_hash(&d));
    let root = msg(&format!("(with-roles ((a @a) (b @b1 @b2)) :dialect {} (signed @a \"sig\" (hello :thread \"t\" :caused-by begin)))", d.hash.as_ref().unwrap()));
    let mut hub = monitor(&d, &root, "a");
    let mut b1 = AdmissionMonitor::new(
        d.clone(),
        Endpoint {
            role: "b".into(),
            occupant: Some(AgentKey("@b1".into())),
        },
        root.clone(),
        TestGate,
    )
    .unwrap();
    let first = act("start", "@b1", "@a", "first", &identity(&root).0);
    let second = act("start", "@b2", "@a", "second", &identity(&root).0);
    assert!(b1.receive(second.clone()).is_err());
    b1.receive(first.clone()).unwrap();
    b1.drain_ready();
    assert_eq!(b1.state(&identity(&first)), Some(&AdmissionState::Accepted));
    let finish = msg(&format!(
        "(signed @a \"sig\" (lang admission (finish \"done\" :thread \"t\" :caused-by ({} {}))))",
        identity(&first).0,
        identity(&second).0
    ));
    hub.receive(finish.clone()).unwrap();
    hub.receive(first).unwrap();
    hub.drain_ready();
    assert_eq!(
        hub.state(&identity(&finish)),
        Some(&AdmissionState::Pending)
    );
    hub.receive(second).unwrap();
    hub.drain_ready();
    assert_eq!(
        hub.state(&identity(&finish)),
        Some(&AdmissionState::Accepted)
    );
}
