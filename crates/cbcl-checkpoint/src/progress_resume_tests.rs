use super::*;
use crate::{certificate::SignedMessage, test_support::Keys};
use alloc::{collections::BTreeMap, format, vec};
use cbcl_core::{
    protocol::{verify_causal, CausalProtocol, NodeRef, StepDecl, VerificationResult},
    state::{self, Entry, Rule, StateClause, Value},
};
use core::cell::Cell;
fn protocol(depth: usize) -> CausalProtocol {
    let mut steps = BTreeMap::new();
    for (name, parent, next) in [
        ("begin".to_string(), None, Some("open".to_string())),
        (
            "open".to_string(),
            Some("begin".to_string()),
            Some("tick#1".to_string()),
        ),
    ] {
        steps.insert(
            name.clone(),
            StepDecl {
                performative: name,
                predecessors: parent.into_iter().map(NodeRef::Single).collect(),
                successors: next.into_iter().map(NodeRef::Single).collect(),
            },
        );
    }
    for i in 1..=depth {
        let name = format!("tick#{i}");
        steps.insert(
            name.clone(),
            StepDecl {
                performative: name,
                predecessors: vec![NodeRef::Single(if i == 1 {
                    "open".into()
                } else {
                    format!("tick#{}", i - 1)
                })],
                successors: if i == depth {
                    vec![]
                } else {
                    vec![NodeRef::Single(format!("tick#{}", i + 1))]
                },
            },
        );
    }
    CausalProtocol { steps }
}
fn signed(verb: &str, parent: Option<&str>, nonce: usize) -> SignedMessage {
    let inner = if verb == "hello" {
        "(with-roles ((member @m0 @m1 @m2 @m3)) (hello :sender @m0 :thread \"resume\" :caused-by begin))".into()
    } else {
        format!("(lang resume ({verb} (@m0 @m1 @m2 @m3) \"{nonce}\" :sender @m0 :thread \"resume\" :caused-by {}))",parent.unwrap())
    };
    SignedMessage::sign(
        Message::try_from(&inner.parse::<cbcl_core::sexpr::SExpr>().unwrap()).unwrap(),
        "@m0",
        &Keys,
    )
    .unwrap()
}
fn act(m: &SignedMessage) -> Act {
    m.authenticate(&Keys).unwrap()
}
struct Port<'a> {
    resume: &'a ProgressResume,
    body_reads: Cell<usize>,
}
impl MessageStore for Port<'_> {
    fn materialized_positions(&self) -> Option<&MaterializedPositions> {
        self.resume.materialized()
    }
    fn lookup(&self, _: &ContentHash) -> Option<&Message> {
        self.body_reads.set(self.body_reads.get() + 1);
        None
    }
    fn lookup_in_thread(&self, _: &ContentHash, _: &ThreadId) -> Option<&Message> {
        self.body_reads.set(self.body_reads.get() + 1);
        None
    }
    fn contains(&self, _: &ContentHash, _: &ThreadId) -> bool {
        false
    }
    fn append(&mut self, _: ContentHash, _: ThreadId, _: Message) -> bool {
        false
    }
    fn frontier(&self, _: &ThreadId) -> Vec<&ContentHash> {
        vec![]
    }
    fn causal_closure(&self, _: &ContentHash, _: &ThreadId) -> Vec<ContentHash> {
        panic!("prefix traversal")
    }
}
#[test]
fn native_progress_fold_and_repeat_tail_match() {
    let p = protocol(8);
    let mut resume = ProgressResume::new(Some(&p), "tick").unwrap();
    let root = signed("hello", None, 0);
    resume.apply(&act(&root)).unwrap();
    let open = signed("open", Some(&root.id().unwrap()), 1);
    resume.apply(&act(&open)).unwrap();
    let mut history = vec![act(&root), act(&open)];
    let clause = StateClause {
        entries: vec![Entry::Field {
            name: "progress".into(),
            rule: Rule::Progress {
                verb: "tick".into(),
            },
        }],
    };
    let mut prev = open;
    for i in 1..=8 {
        let tick = signed("tick", Some(&prev.id().unwrap()), i + 1);
        let a = act(&tick);
        resume.apply(&a).unwrap();
        history.push(a);
        assert_eq!(resume.progress(), i);
        assert_eq!(
            state::fold(&clause, Some(&p), &history)
                .iter()
                .find(|(name, _)| name == "progress")
                .map(|(_, value)| value),
            Some(&Value::Int(i as i128))
        );
        let bytes = resume.encode();
        let decoded = ProgressResume::decode(&bytes, Some(&p)).unwrap();
        assert_eq!(decoded, resume);
        let port = Port {
            resume: &decoded,
            body_reads: Cell::new(0),
        };
        if i < 8 {
            assert_eq!(
                verify_causal(
                    "tick",
                    Some(&CausedBy::Single(tick.id().unwrap())),
                    &port,
                    &p,
                    &ThreadId("resume".into())
                ),
                VerificationResult::Valid
            );
            assert_eq!(port.body_reads.get(), 0);
        }
        prev = tick;
    }
}
#[test]
fn missing_out_of_order_context_and_codec_fail_closed() {
    let p = protocol(4);
    let root = signed("hello", None, 0);
    let open = signed("open", Some(&root.id().unwrap()), 1);
    let a = signed("tick", Some(&open.id().unwrap()), 2);
    let b = signed("tick", Some(&a.id().unwrap()), 3);
    let mut r = ProgressResume::new(Some(&p), "tick").unwrap();
    assert!(r.apply(&act(&open)).is_err());
    r.apply(&act(&root)).unwrap();
    r.apply(&act(&open)).unwrap();
    let frozen = r.clone();
    assert!(r.apply(&act(&b)).is_err());
    assert_eq!(r, frozen);
    r.apply(&act(&a)).unwrap();
    r.apply(&act(&b)).unwrap();
    let duplicate = r.clone();
    r.apply(&act(&a)).unwrap();
    assert_eq!(r, duplicate);
    let bytes = r.encode();
    assert!(ProgressResume::decode(&bytes, Some(&protocol(5))).is_err());
    assert!(ProgressResume::decode(&bytes, None).is_err());
    for n in [0, 1, 8, bytes.len() - 1] {
        assert!(ProgressResume::decode(&bytes[..n], Some(&p)).is_err());
    }
    let mut trailing = bytes.clone();
    trailing.push(0);
    assert!(ProgressResume::decode(&trailing, Some(&p)).is_err());
    let mut schema = bytes.clone();
    schema[4] ^= 1;
    assert!(ProgressResume::decode(&schema, Some(&p)).is_err());
    let mut body = bytes;
    *body.last_mut().unwrap() = 255;
    assert!(ProgressResume::decode(&body, Some(&p)).is_err());
    let mut wrong = act(&a);
    if let Message::Wrapped { content, .. } = &mut wrong.message {
        if let Message::Dialect { inner, .. } = &mut **content {
            if let Message::Simple { thread, .. } = &mut **inner {
                *thread = Some("foreign".into());
            }
        }
    }
    assert!(r.apply(&wrong).is_err());
    let mut none = ProgressResume::new(None, "tick").unwrap();
    none.apply(&act(&root)).unwrap();
    none.apply(&act(&open)).unwrap();
    none.apply(&act(&a)).unwrap();
    assert_eq!(none.progress(), 0);
}
#[test]
fn five_thousand_accepted_messages_resume_without_prefix_body_reads() {
    let p = protocol(32);
    let root = signed("hello", None, 0);
    let open = signed("open", Some(&root.id().unwrap()), 1);
    let mut r = ProgressResume::new(Some(&p), "tick").unwrap();
    r.apply(&act(&root)).unwrap();
    r.apply(&act(&open)).unwrap();
    let openid = open.id().unwrap();
    let mut parent = openid.clone();
    for i in 0..5000 {
        if i % 32 == 0 {
            parent = openid.clone();
        }
        let m = signed("tick", Some(&parent), i + 2);
        r.apply(&act(&m)).unwrap();
        parent = m.id().unwrap();
    }
    let frozen = r.clone();
    let decoded = ProgressResume::decode(&r.encode(), Some(&p)).unwrap();
    assert_eq!(decoded.progress(), 32);
    let port = Port {
        resume: &decoded,
        body_reads: Cell::new(0),
    };
    assert_eq!(
        verify_causal(
            "tick",
            Some(&CausedBy::Single(parent)),
            &port,
            &p,
            &ThreadId("resume".into())
        ),
        VerificationResult::Valid
    );
    assert_eq!(port.body_reads.get(), 0);
    assert_eq!(frozen, r);
}

#[test]
fn installed_port_requires_actual_native_certificate_and_bound_summary() {
    use crate::test_support::{installed, parse, Fixture};
    use cbcl_core::store::ThreadedMessageStore;
    let target = installed(
        r#"(define repeat-checkpoint-target (cbcl) @anuna
      (:roles ((* member)))
      (extend open (to title) :from member :to member (tell to :title title))
      (extend tick (to) :from member :to member (tell to))
      (shape open (require :title string))
      (protocol (then begin open (repeat 3 tick)))
      (state (title (initial open :title)) (rank (progress tick))))"#,
    );
    let f = Fixture::with_target(target);
    let tick=SignedMessage::sign(parse(&format!("(lang {} (tick (@m0 @m1 @m2 @m3) \"one\" :sender @m0 :thread \"target\" :caused-by \"{}\"))",f.context.target().name,f.target_open.id().unwrap())),"@m0",&f.keys).unwrap();
    let members = f.members(core::slice::from_ref(&tick));
    let cert = f.certificate(&members);
    let empty = ThreadedMessageStore::new();
    let port = CertifiedProgressPort::install_materialized_port(
        &empty, "tick", &cert, &f.context, &f.keys,
    )
    .unwrap();
    assert_eq!(port.materialized_positions().unwrap().progress("tick"), 1);
    assert_eq!(
        verify_causal(
            "tick",
            Some(&CausedBy::Single(tick.id().unwrap())),
            &port,
            f.context.target().causal_protocol.as_ref().unwrap(),
            &ThreadId("target".into())
        ),
        VerificationResult::Valid
    );
    let mut forged = cert.clone();
    forged.endorsements.clear();
    assert!(CertifiedProgressPort::install_materialized_port(
        &empty, "tick", &forged, &f.context, &f.keys
    )
    .is_err());
    let mut wrong = cert.clone();
    wrong.summary[0] ^= 1;
    assert!(CertifiedProgressPort::install_materialized_port(
        &empty, "tick", &wrong, &f.context, &f.keys
    )
    .is_err());
    let foreign = Fixture::new();
    assert!(CertifiedProgressPort::install_materialized_port(
        &empty,
        "tick",
        &cert,
        &foreign.context,
        &foreign.keys
    )
    .is_err());
}

#[test]
fn protocol_none_accepts_bare_unthreaded_act_and_roundtrips_native_zero() {
    use cbcl_core::{message::Performative, sexpr::SExpr};
    let message = Message::Simple {
        performative: Performative::Custom("tick".into()),
        recipient: None,
        content: SExpr::List(vec![]),
        params: vec![],
        thread: None,
        sender: None,
        caused_by: None,
    };
    let bare = Act::from_message(message, "@typed-kernel").unwrap();
    let mut resume = ProgressResume::new(None, "tick").unwrap();
    let empty_encoding = resume.encode();
    resume.apply(&bare).unwrap();
    assert_eq!(resume.progress(), 0);
    assert!(resume.materialized().is_none());
    assert_eq!(resume.encode(), empty_encoding);
    assert_eq!(
        ProgressResume::decode(&resume.encode(), None).unwrap(),
        resume
    );
    let mut invalid = bare.clone();
    invalid.address.push('0');
    assert!(resume.apply(&invalid).is_err());

    let clause = StateClause {
        entries: vec![Entry::Field {
            name: "rank".into(),
            rule: Rule::Progress {
                verb: "tick".into(),
            },
        }],
    };
    let mut summary = crate::summary::Summary::new(&clause, None).unwrap();
    summary.apply(&bare, |_| false).unwrap();
    let decoded = crate::summary::Summary::decode_for(&summary.encode(), &clause, None).unwrap();
    assert_eq!(
        decoded.render(),
        state::fold(&clause, None, core::slice::from_ref(&bare))
    );
    assert_eq!(decoded.render(), vec![("rank".into(), Value::Int(0))]);
    assert!(decoded
        .progress_resume("tick")
        .unwrap()
        .materialized()
        .is_none());
}
