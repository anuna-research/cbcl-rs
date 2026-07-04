//! SPEC-014 TEST-639: the sealed-bid auction end-to-end (SPEC-004's demo
//! through the role layer) — the paper's trace h₀…h₇ with an indexed
//! `(* bidder)` cast sealed at the root.

use cbcl_core::dialect::{Dialect, PerformativeDef, ResourceBounds};
use cbcl_core::message::Message;
use cbcl_core::projection::{project, verify_causal_for_role, LocalStep};
use cbcl_core::protocol::{CausalProtocol, CausalViolation, NodeRef, StepDecl, VerificationResult};
use cbcl_core::r6::{r6_instantiated_violations, r6_violations};
use cbcl_core::role::{parse_cast, parse_roles, AgentKey, Cast, Endpoint};
use cbcl_core::sexpr::SExpr;
use cbcl_core::store::{ContentHash, MessageStore, ThreadId, ThreadedMessageStore};
use std::collections::{BTreeMap, BTreeSet};

fn auction_dialect() -> Dialect {
    let ann = |from: &str, to: &[&str]| {
        Some(cbcl_core::role::RoleAnnotation {
            from: from.to_string(),
            to: to.iter().map(|s| s.to_string()).collect(),
        })
    };
    let perf = |name: &str, role| PerformativeDef {
        name: name.to_string(),
        params: Vec::new(),
        template: "t".parse::<SExpr>().unwrap(),
        role,
    };
    let mut steps: BTreeMap<String, StepDecl> = BTreeMap::new();
    let step = |name: &str, preds: Vec<NodeRef>, succs: Vec<NodeRef>| StepDecl {
        performative: name.to_string(),
        predecessors: preds,
        successors: succs,
    };
    steps.insert(
        "begin".into(),
        step("begin", vec![], vec![NodeRef::Single("commit".into())]),
    );
    steps.insert(
        "commit".into(),
        step(
            "commit",
            vec![NodeRef::Single("begin".into())],
            vec![NodeRef::Single("reveal".into())],
        ),
    );
    steps.insert(
        "reveal".into(),
        step("reveal", vec![NodeRef::Single("commit".into())], vec![]),
    );
    steps.insert(
        "declare-winner".into(),
        step(
            "declare-winner",
            vec![NodeRef::All(["reveal".to_string()].into_iter().collect())],
            vec![],
        ),
    );
    Dialect {
        causal_locality: Default::default(),
        roles: parse_roles(&"(auctioneer (* bidder))".parse::<SExpr>().unwrap()).unwrap(),
        name: "auction".into(),
        extends: Vec::new(),
        author: None,
        performatives: vec![
            perf("commit", ann("bidder", &["auctioneer"])),
            perf("reveal", ann("bidder", &["auctioneer"])),
            perf("declare-winner", ann("auctioneer", &[])),
        ],
        resources: ResourceBounds {
            max_depth: 8,
            max_expansion_size: 512,
            verification_time_ms: 10,
        },
        examples: Vec::new(),
        signature: None,
        hash: None,
        protocol: None,
        causal_protocol: Some(CausalProtocol { steps }),
        shapes: Vec::new(),
    }
}

fn cast(d: &Dialect) -> Cast {
    parse_cast(
        &"((auctioneer @auc) (bidder @b1 @b2 @b3))"
            .parse::<SExpr>()
            .unwrap(),
        &d.roles,
    )
    .unwrap()
}

fn msg(src: &str) -> Message {
    Message::try_from(&src.parse::<SExpr>().unwrap()).unwrap()
}

fn tid() -> ThreadId {
    ThreadId("conv-7".into())
}

/// The paper's trace h₀…h₇.
fn trace() -> Vec<(&'static str, Message)> {
    vec![
        ("h0", msg("(with-roles ((auctioneer @auc) (bidder @b1 @b2 @b3)) (signed @auc \"sig\" (hello :thread \"conv-7\" :caused-by begin)))")),
        ("h1", msg("(signed @b1 \"sig\" (commit @auc \"sha256:9f\" :caused-by h0))")),
        ("h2", msg("(signed @b2 \"sig\" (commit @auc \"sha256:3a\" :caused-by h0))")),
        ("h3", msg("(signed @b3 \"sig\" (commit @auc \"sha256:c7\" :caused-by h0))")),
        ("h4", msg("(signed @b1 \"sig\" (reveal @auc 42 :caused-by h1))")),
        ("h5", msg("(signed @b2 \"sig\" (reveal @auc 17 :caused-by h2))")),
        ("h6", msg("(signed @b3 \"sig\" (reveal @auc 55 :caused-by h3))")),
        ("h7", msg("(signed @auc \"sig\" (declare-winner \"b3\" :caused-by (h4 h5 h6)))")),
    ]
}

/// Run-level projection (paper Def. run-proj + root convention): the
/// messages whose sender key or recipient keys include the endpoint's,
/// plus the thread root, which is addressed to the entire cast.
fn project_run(trace: &[(&'static str, Message)], key: &str) -> BTreeSet<&'static str> {
    let mut set = BTreeSet::new();
    for (h, m) in trace {
        if *h == "h0" {
            set.insert(*h); // root convention: every role holds the root
            continue;
        }
        let sender_matches = matches!(m.inner_message().map(|_| ()), Some(())) && {
            // sender = signed wrapper key
            let s = match m {
                Message::Wrapped { params, .. } => params.first().and_then(|p| match p {
                    SExpr::Atom(cbcl_core::sexpr::Atom::Symbol(s)) => Some(s.as_str()),
                    _ => None,
                }),
                _ => None,
            };
            s == Some(key)
        };
        let recipient_matches = m
            .innermost_simple()
            .map(|s| s.recipient_set().contains(key))
            .unwrap_or(false);
        if sender_matches || recipient_matches {
            set.insert(*h);
        }
    }
    set
}

#[test]
fn auction_end_to_end() {
    let d = auction_dialect();
    let c = cast(&d);

    // R6 passes at both levels for the terminal declare-winner.
    assert_eq!(r6_violations(&d), Vec::new());
    assert_eq!(r6_instantiated_violations(&d, &c), Vec::new());

    // Local protocols: bidder = two Sends and no sight of other bids;
    // auctioneer = Recv per type plus the fan-in.
    let bidder_local = project(
        &d,
        &Endpoint {
            role: "bidder".into(),
            occupant: Some(AgentKey("@b1".into())),
        },
        Some(&c),
    );
    assert_eq!(bidder_local.steps.get("commit"), Some(&LocalStep::Send));
    assert_eq!(bidder_local.steps.get("reveal"), Some(&LocalStep::Send));
    assert_eq!(bidder_local.steps.get("declare-winner"), None);

    // Verify the whole trace on the full store: every commit/reveal Valid
    // (root typing resolves h0 → begin), the fan-in Valid at 3/3.
    let trace = trace();
    let mut store = ThreadedMessageStore::new();
    for (h, m) in &trace {
        store.append(ContentHash((*h).into()), tid(), m.clone());
    }
    let auc = Endpoint {
        role: "auctioneer".into(),
        occupant: None,
    };
    for (h, m) in &trace {
        let v = verify_causal_for_role(
            m,
            &auc,
            &d,
            &c,
            &store,
            &tid(),
            &ContentHash("h0".to_string()),
        );
        assert_eq!(v, VerificationResult::Valid, "{h} must be Valid");
    }

    // Fan-in gate: Unknown at 2/3 reveals.
    let mut partial = ThreadedMessageStore::new();
    for (h, m) in &trace {
        if *h != "h6" && *h != "h7" {
            partial.append(ContentHash((*h).into()), tid(), m.clone());
        }
    }
    let h7 = &trace.iter().find(|(h, _)| *h == "h7").unwrap().1;
    assert_eq!(
        verify_causal_for_role(
            h7,
            &auc,
            &d,
            &c,
            &partial,
            &tid(),
            &ContentHash("h0".to_string())
        ),
        VerificationResult::Unknown
    );

    // A fourth reveal from a non-member key is a Violation.
    let intruder = msg("(signed @b4 \"sig\" (reveal @auc 99 :caused-by h3))");
    assert!(matches!(
        verify_causal_for_role(
            &intruder,
            &auc,
            &d,
            &c,
            &store,
            &tid(),
            &ContentHash("h0".to_string())
        ),
        VerificationResult::Violation(CausalViolation::RoleConformance { .. })
    ));

    // Run projection: project(C, bidder@b1) = {h0, h1, h4} (the paper's
    // exact set), and the auctioneer holds every message.
    assert_eq!(
        project_run(&trace, "@b1"),
        ["h0", "h1", "h4"].into_iter().collect::<BTreeSet<_>>()
    );
    assert_eq!(project_run(&trace, "@auc").len(), 8);

    // Gluing the four local runs reconstructs the global trace exactly.
    let mut glued: BTreeSet<&str> = BTreeSet::new();
    for key in ["@auc", "@b1", "@b2", "@b3"] {
        glued.extend(project_run(&trace, key));
    }
    assert_eq!(glued.len(), 8, "glue(project(C)) = C");
}
