//! Bounded differential coverage against the pre-refactor verifier, including
//! complete diagnostic equality. This is a regression test, not a proof of adapters.
#[path = "support/legacy_causal.rs"]
mod legacy;
use cbcl_core::message::{CausedBy, Message};
use cbcl_core::protocol::{verify_causal, CausalProtocol, NodeRef, StepDecl};
use cbcl_core::sexpr::SExpr;
use cbcl_core::store::{ContentHash, MessageStore, ThreadId, ThreadedMessageStore};

#[test]
fn all_routes_match_legacy_including_diagnostics() {
    let thread = ThreadId("t".into());
    let other_thread = ThreadId("elsewhere".into());
    let mut store = ThreadedMessageStore::new();
    for (hash, perf, wrapped) in [("ha", "a", false), ("hb", "b", true), ("hx", "x", false)] {
        let text = if wrapped {
            format!("(lang d (signed :by key ({perf} :thread t)))")
        } else {
            format!("(lang d ({perf} :thread t))")
        };
        let msg = Message::try_from(&text.parse::<SExpr>().unwrap()).unwrap();
        store.append(ContentHash(hash.into()), thread.clone(), msg);
    }
    let clauses = vec![
        NodeRef::Single("a".into()),
        NodeRef::Single("begin".into()),
        NodeRef::Any(["a".into(), "b".into()].into_iter().collect()),
        NodeRef::Any(Default::default()),
        NodeRef::All(["a".into(), "b".into()].into_iter().collect()),
        NodeRef::All(["x".into()].into_iter().collect()),
        NodeRef::All(Default::default()),
    ];
    let mut declarations = vec![vec![]];
    for first in &clauses {
        declarations.push(vec![first.clone()]);
        for second in &clauses {
            declarations.push(vec![first.clone(), second.clone()]);
        }
    }
    let ids = ["ha", "hb", "hx", "missing"];
    let mut citations = vec![None, Some(CausedBy::Begin)];
    for h in ids {
        citations.push(Some(CausedBy::Single(h.into())));
    }
    for len in 0..=4 {
        for mut code in 0..4usize.pow(len) {
            let mut hashes = Vec::new();
            for _ in 0..len {
                hashes.push(ids[code % 4].into());
                code /= 4;
            }
            citations.push(Some(CausedBy::Multiple(hashes)));
        }
    }
    let mut comparisons = 0;
    for predecessors in declarations {
        let protocol = CausalProtocol {
            steps: [(
                "target".into(),
                StepDecl {
                    performative: "target".into(),
                    predecessors,
                    successors: vec![],
                },
            )]
            .into_iter()
            .collect(),
        };
        for perf in ["target", "undeclared"] {
            for scope in [&thread, &other_thread] {
                for citation in &citations {
                    assert_eq!(
                        verify_causal(perf, citation.as_ref(), &store, &protocol, scope),
                        legacy::verify_causal(perf, citation.as_ref(), &store, &protocol, scope),
                        "perf={perf} citation={citation:?} protocol={protocol:?} thread={scope:?}",
                    );
                    comparisons += 1;
                }
            }
        }
    }
    assert_eq!(comparisons, 79_116);
}
