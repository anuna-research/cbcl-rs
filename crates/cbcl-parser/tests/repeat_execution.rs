//! End-to-end regression: repeat positions are inferred from causal evidence,
//! never from the number of received messages or an untrusted position field.
use cbcl_core::intend::{intend, Instance};
use cbcl_core::role::AgentKey;
use cbcl_core::state::{fold, Act, Value};
use cbcl_core::store::{MessageStore, ThreadId};
use cbcl_parser::state_exports::{admit, Admission};
use cbcl_parser::{parse, parse_dialect, parse_message};
use std::collections::BTreeMap;

fn dialect(body: &str) -> cbcl_core::dialect::Dialect {
    let d = parse_dialect(&parse(&format!("(define demo (cbcl) @author (extend tick (to) (tell to)) (extend close (to) (tell to)) (protocol (then begin {body})) (state (number (count tick)) (closed (exists close))))")).unwrap()).unwrap();
    let mut registry = cbcl_core::dialect::DialectRegistry::new();
    registry.install(d).unwrap();
    registry.iter().last().unwrap().clone()
}
fn act(verb: &str, cb: &str, signer: &str) -> Act {
    let message = parse_message(
        &parse(&format!(
            "(lang demo ({verb} @all {cb} :thread \"t\" :from {signer}))"
        ))
        .unwrap(),
    )
    .unwrap();
    Act::from_message(message, signer).unwrap()
}
fn tick(pred: &str, signer: &str) -> Act {
    act("tick", &format!(":caused-by {pred}"), signer)
}
fn thread() -> ThreadId {
    ThreadId("t".into())
}
fn accepted(d: &cbcl_core::dialect::Dialect, history: &[Act], a: &Act) {
    assert_eq!(admit(d, &thread(), history, a), Admission::Accepted);
}

#[test]
fn repeat_requires_causal_evidence_and_waits_for_missing_ancestors() {
    let d = dialect("(repeat 100 tick)");
    assert!(matches!(
        admit(&d, &thread(), &[], &act("tick", "", "@a")),
        Admission::Rejected(_)
    ));
    let first = tick("begin", "@a");
    accepted(&d, &[], &first);
    let second = tick(&first.address, "@b");
    assert_eq!(admit(&d, &thread(), &[], &second), Admission::Pending);
    accepted(&d, &[first.clone()], &second);
    let third = tick(&second.address, "@c");
    // Having the immediate predecessor is insufficient to establish its position.
    assert_eq!(admit(&d, &thread(), &[second], &third), Admission::Pending);
}

#[test]
fn hundred_ticks_then_close_but_no_101st_tick() {
    let d = dialect("(repeat 100 tick) close");
    let mut history = Vec::new();
    for i in 0..100 {
        let pred = history
            .last()
            .map(|a: &Act| a.address.as_str())
            .unwrap_or("begin");
        let a = tick(pred, ["@a", "@b", "@c"][i % 3]);
        accepted(&d, &history, &a);
        history.push(a);
        let close = act(
            "close",
            &format!(":caused-by {}", history.last().unwrap().address),
            "@a",
        );
        if i == 99 {
            accepted(&d, &history, &close);
        } else {
            assert!(matches!(
                admit(&d, &thread(), &history, &close),
                Admission::Rejected(_)
            ));
        }
    }
    assert!(matches!(
        admit(
            &d,
            &thread(),
            &history,
            &tick(&history.last().unwrap().address, "@a")
        ),
        Admission::Rejected(_)
    ));
    assert_eq!(
        fold(
            d.state.as_ref().unwrap(),
            d.causal_protocol.as_ref(),
            &history
        )[0]
        .1,
        Value::Int(100)
    );
}

#[test]
fn binder_advances_repeated_opener_verb_and_stops_at_the_last_position() {
    let d = dialect("(repeat 3 tick)");
    let mut history = vec![tick("begin", "@a")];
    for who in ["@b", "@a"] {
        let inst = Instance::new(&d, thread(), &history).unwrap();
        let message = intend(&inst, &AgentKey(who.into()), "tick", BTreeMap::new()).unwrap();
        let a = Act::from_message(message, who).unwrap();
        assert_eq!(
            a.predecessors,
            vec![history.last().unwrap().address.clone()]
        );
        accepted(&d, &history, &a);
        history.push(a);
    }
    let inst = Instance::new(&d, thread(), &history).unwrap();
    assert!(intend(&inst, &AgentKey("@a".into()), "tick", BTreeMap::new()).is_err());
}

#[test]
fn repeats_are_not_a_global_message_quota() {
    let d = dialect("(repeat 2 tick)");
    let a = tick("begin", "@a");
    let b = tick("begin", "@b");
    accepted(&d, &[a.clone()], &b);
    let c = tick(&a.address, "@c");
    let e = tick(&b.address, "@a");
    accepted(&d, &[a.clone(), b.clone()], &c);
    accepted(&d, &[a.clone(), b.clone(), c.clone()], &e);
    let history = [a, b, c, e];
    assert_eq!(
        fold(
            d.state.as_ref().unwrap(),
            d.causal_protocol.as_ref(),
            &history
        )[0]
        .1,
        Value::Int(4)
    );
}

#[test]
fn nested_repeat_and_thread_isolation() {
    let d = dialect("(repeat 2 (repeat 2 tick))");
    let mut history = Vec::new();
    for i in 0..4 {
        let pred = history
            .last()
            .map(|a: &Act| a.address.as_str())
            .unwrap_or("begin");
        let a = tick(pred, ["@a", "@b", "@c"][i % 3]);
        accepted(&d, &history, &a);
        history.push(a);
    }
    let extra = tick(&history.last().unwrap().address, "@b");
    assert!(matches!(
        admit(&d, &thread(), &history, &extra),
        Admission::Rejected(_)
    ));
    use cbcl_core::protocol::{verify_causal, VerificationResult};
    use cbcl_core::store::{ContentHash, ThreadedMessageStore};
    let mut store = ThreadedMessageStore::new();
    store.append(
        ContentHash(history[0].address.clone()),
        ThreadId("other".into()),
        history[0].message.clone(),
    );
    let descendant = tick(&history[0].address, "@c");
    assert_eq!(
        verify_causal(
            "tick",
            descendant.simple().caused_by(),
            &store,
            d.causal_protocol.as_ref().unwrap(),
            &thread()
        ),
        VerificationResult::Unknown
    );
}

fn multi(body: &str) -> cbcl_core::dialect::Dialect {
    let source = format!("(define demo (cbcl) @author (extend open (to) (tell to)) (extend x (to) (tell to)) (extend y (to) (tell to)) (extend z (to) (tell to)) (extend close (to) (tell to)) (protocol (then begin {body})) (state (number (count x))))");
    let mut registry = cbcl_core::dialect::DialectRegistry::new();
    registry
        .install(parse_dialect(&parse(&source).unwrap()).unwrap())
        .unwrap();
    registry.iter().last().unwrap().clone()
}
fn linked(verb: &str, pred: &str) -> Act {
    act(verb, &format!(":caused-by {pred}"), "@a")
}

#[test]
fn any_seams_and_plain_to_repeated_base_execute() {
    let d = multi("(repeat 2 x (any y z)) close");
    let mut history = Vec::new();
    for verb in ["x", "y", "x", "z", "close"] {
        let pred = history
            .last()
            .map(|a: &Act| a.address.as_str())
            .unwrap_or("begin");
        let a = linked(verb, pred);
        accepted(&d, &history, &a);
        history.push(a);
    }
    assert!(matches!(
        admit(
            &d,
            &thread(),
            &history,
            &linked("close", &history[1].address)
        ),
        Admission::Rejected(_)
    ));
    let d = multi("x (repeat 2 x)");
    let mut history = vec![];
    for _ in 0..3 {
        let pred = history
            .last()
            .map(|a: &Act| a.address.as_str())
            .unwrap_or("begin");
        let a = linked("x", pred);
        accepted(&d, &history, &a);
        history.push(a);
    }
    assert!(matches!(
        admit(&d, &thread(), &history, &linked("x", &history[2].address)),
        Admission::Rejected(_)
    ));
}

#[test]
fn all_fanin_is_copy_specific_and_preserves_iteration_seams() {
    let d = multi("open (repeat 2 (all x y) z) close");
    let opener = linked("open", "begin");
    accepted(&d, &[], &opener);
    let mut pred = opener.address.clone();
    let mut history = vec![opener];
    for _ in 0..2 {
        let x = linked("x", &pred);
        let y = linked("y", &pred);
        accepted(&d, &history, &x);
        accepted(&d, &history, &y);
        let z = linked("z", &format!("({} {})", x.address, y.address));
        history.push(x);
        history.push(y);
        accepted(&d, &history, &z);
        pred = z.address.clone();
        history.push(z);
    }
    accepted(&d, &history, &linked("close", &pred));
    let crossed = linked(
        "z",
        &format!("({} {})", history[1].address, history[5].address),
    );
    assert!(matches!(
        admit(&d, &thread(), &history, &crossed),
        Admission::Rejected(_)
    ));
    // Missing evidence is Unknown; known wrong evidence dominates missing evidence.
    let missing = linked("z", &format!("({} sha256-missing)", history[4].address));
    assert_eq!(admit(&d, &thread(), &history, &missing), Admission::Pending);
    let wrong = linked("z", &format!("({} sha256-missing)", history[3].address));
    assert!(matches!(
        admit(&d, &thread(), &history, &wrong),
        Admission::Rejected(_)
    ));
}

#[test]
fn role_annotated_repeats_resolve_the_pinned_root_through_ancestors() {
    let source = "(define demo (cbcl) @author (:roles (a b)) (extend x (to) :from a :to (b) (tell to)) (extend y (to) :from b :to (a) (tell to)) (protocol (then begin (repeat 2 x y))) (state (number (count x))))";
    let mut registry = cbcl_core::dialect::DialectRegistry::new();
    registry
        .install(parse_dialect(&parse(source).unwrap()).unwrap())
        .unwrap();
    let d = registry.iter().last().unwrap();
    let root = Act::from_message(
        parse_message(
            &parse(
                "(with-roles ((a @a) (b @b)) (signed @a (hello :thread \"t\" :caused-by begin)))",
            )
            .unwrap(),
        )
        .unwrap(),
        "@a",
    )
    .unwrap();
    accepted(d, &[], &root);
    let mut history = vec![root];
    for (verb, signer, to) in [
        ("x", "@a", "@b"),
        ("y", "@b", "@a"),
        ("x", "@a", "@b"),
        ("y", "@b", "@a"),
    ] {
        let text = format!("(signed {signer} (lang demo ({verb} {to} :caused-by {} :thread \"t\" :from {signer})))", history.last().unwrap().address);
        let a = Act::from_message(parse_message(&parse(&text).unwrap()).unwrap(), signer).unwrap();
        accepted(d, &history, &a);
        history.push(a);
    }
}

#[test]
fn indexed_role_fanin_requires_every_occupant_at_the_same_copy() {
    let source = "(define demo (cbcl) @author (:roles (owner (* member))) (extend open (to) :from owner :to (owner member) (tell to)) (extend ack (to) :from member :to (owner member) (tell to)) (extend stamp (to) :from owner :to (owner member) (tell to)) (extend done (to) :from owner :to (owner member) (tell to)) (protocol (then begin open (repeat 2 (all ack stamp) done))) (state (number (count ack))))";
    let mut registry = cbcl_core::dialect::DialectRegistry::new();
    registry
        .install(parse_dialect(&parse(source).unwrap()).unwrap())
        .unwrap();
    let d = registry.iter().last().unwrap();
    let root = Act::from_message(parse_message(&parse("(with-roles ((owner @a) (member @b @c)) (signed @a (hello :thread \"t\" :caused-by begin)))").unwrap()).unwrap(), "@a").unwrap();
    let signed = |verb: &str, pred: &str, who: &str| {
        Act::from_message(parse_message(&parse(&format!("(signed {who} (lang demo ({verb} (@a @b @c) :caused-by {pred} :thread \"t\" :from {who})))")).unwrap()).unwrap(), who).unwrap()
    };
    accepted(d, &[], &root);
    let open = signed("open", &root.address, "@a");
    accepted(d, &[root.clone()], &open);
    let mut history = vec![root, open];
    for _ in 0..2 {
        let b = signed("ack", &history.last().unwrap().address, "@b");
        let c = signed("ack", &history.last().unwrap().address, "@c");
        let stamp = signed("stamp", &history.last().unwrap().address, "@a");
        accepted(d, &history, &stamp);
        accepted(d, &history, &b);
        accepted(d, &history, &c);
        history.push(b.clone());
        history.push(c.clone());
        history.push(stamp.clone());
        let incomplete = signed("done", &format!("({} {})", b.address, stamp.address), "@a");
        assert!(matches!(
            admit(d, &thread(), &history, &incomplete),
            Admission::Rejected(_)
        ));
        let done = signed(
            "done",
            &format!("({} {} {})", b.address, c.address, stamp.address),
            "@a",
        );
        let instance = Instance::new(d, thread(), &history).unwrap();
        let bound = intend(&instance, &AgentKey("@a".into()), "done", BTreeMap::new()).unwrap();
        let bound = Act::from_message(
            parse_message(
                &parse(&format!(
                    "(signed @a {})",
                    cbcl_core::intend::canonical_text(&bound)
                ))
                .unwrap(),
            )
            .unwrap(),
            "@a",
        )
        .unwrap();
        assert_eq!(bound.predecessors, done.predecessors);
        accepted(d, &history, &bound);
        accepted(d, &history, &done);
        history.push(done);
    }
    let mixed = signed(
        "done",
        &format!(
            "({} {} {})",
            history[2].address, history[7].address, history[8].address
        ),
        "@a",
    );
    assert!(matches!(
        admit(d, &thread(), &history, &mixed),
        Admission::Rejected(_)
    ));
}

/// Finite live comparison, not a proof of the Rust compiler or all Rust inputs.
#[test]
#[ignore = "requires lake build LeanCbcl.Repeat; run explicitly for proof changes"]
fn native_repeat_verdicts_match_kernel_reduced_lean() {
    use cbcl_core::protocol::{verify_causal, VerificationResult};
    use cbcl_core::store::{ContentHash, ThreadedMessageStore};
    use std::fmt::Write;
    let mut lean = String::from("import LeanCbcl.Repeat\nopen CBCL.Repeat\nset_option maxRecDepth 4096\nset_option maxHeartbeats 0\n");
    let mut cases = 0;
    for bound in [1, 2, 3, 5, 10, 100] {
        let d = dialect(&format!("(repeat {bound} tick)"));
        let mut history = Vec::new();
        for i in 0..=bound {
            let pred = history
                .last()
                .map(|a: &Act| a.address.as_str())
                .unwrap_or("begin");
            history.push(tick(pred, ["@a", "@b", "@c"][i % 3]));
        }
        let mut store = ThreadedMessageStore::new();
        for a in &history {
            store.append(ContentHash(a.address.clone()), thread(), a.message.clone());
        }
        // The actual Rust content addresses are mapped injectively to finite
        // model addresses. The predecessor graph and wire metadata are retained.
        writeln!(lean, "def s{bound} : Store := fun h => match h with").unwrap();
        writeln!(lean, "  | 0 => some ⟨0, \"tick\", .begin⟩").unwrap();
        for i in 1..history.len() {
            writeln!(lean, "  | {i} => some ⟨0, \"tick\", .previous {}⟩", i - 1).unwrap();
        }
        writeln!(lean, "  | 999 => some ⟨0, \"tick\", .absent⟩\n  | 1000 => some ⟨0, \"tick\", .previous 998⟩\n  | _ => none").unwrap();
        let vectors = history
            .iter()
            .enumerate()
            .map(|(i, a)| (i, a.clone()))
            .chain([
                (999, act("tick", "", "@a")),
                (1000, tick("sha256-missing", "@a")),
            ]);
        for (h, a) in vectors {
            let actual = verify_causal(
                "tick",
                a.simple().caused_by(),
                &store,
                d.causal_protocol.as_ref().unwrap(),
                &thread(),
            );
            let expected = match actual {
                VerificationResult::Valid => format!(".position {}", h + 1),
                VerificationResult::Unknown => ".unknown".into(),
                VerificationResult::Violation(_) => ".invalid".into(),
            };
            let name = format!("comparison{cases}");
            writeln!(lean, "theorem {name} : resolve {} s{bound} 0 \"tick\" {bound} {h} = {expected} := by decide\n#print axioms {name}", bound+2).unwrap();
            cases += 1;
        }
    }
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../lean-cbcl");
    let path = std::env::temp_dir().join(format!("cbcl-repeat-{}.lean", std::process::id()));
    std::fs::write(&path, lean).unwrap();
    let output = std::process::Command::new("lake")
        .args(["env", "lean"])
        .arg(&path)
        .current_dir(&root)
        .output()
        .unwrap();
    let _ = std::fs::remove_file(path);
    let report = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.status.success(), "{report}");
    assert!(
        !report.contains("sorry") && !report.contains("sorryAx"),
        "{report}"
    );
    assert_eq!(
        report.matches("does not depend on any axioms").count(),
        cases,
        "{report}"
    );
}

#[test]
fn repeat_positions_use_authenticated_redacted_and_opened_causal_headers() {
    use cbcl_core::attest::sign_attestation_v2;
    use cbcl_core::envelope::{build_opened, redact, HEADER_FIELDS};
    use cbcl_core::equivocation::attestation_header_for;
    use cbcl_core::keyid::SignatureSuite;
    use cbcl_core::protocol::{verify_causal, VerificationResult};
    use cbcl_core::r4::Signer;
    use cbcl_core::store::{ContentHash, ThreadedMessageStore};
    use cbcl_core::typed_addr::FieldId;
    struct FixtureSigner;
    impl Signer for FixtureSigner {
        fn sign(&self, data: &[u8]) -> Vec<u8> {
            data.to_vec()
        }
        fn verify(&self, data: &[u8], signature: &[u8]) -> bool {
            data == signature
        }
    }
    let d = dialect("(repeat 3 tick)");
    let wire_tick = |pred: &str, who: &str| {
        let mut a = Act::from_message(
            parse_message(
                &parse(&format!(
                    "(lang demo (tick @all :caused-by \"{pred}\" :thread \"t\" :sender {who}))"
                ))
                .unwrap(),
            )
            .unwrap(),
            who,
        )
        .unwrap();
        // Envelope shelves use the typed-root ':' spelling; keep the test's
        // content-address index and references in that same spelling.
        a.address = a.address.replacen("sha256-", "sha256:", 1);
        a
    };
    let first = wire_tick("begin", "@a");
    let second = wire_tick(&first.address, "@b");
    let third = wire_tick(&second.address, "@c");
    let extra = wire_tick(&third.address, "@a");
    let mut redacted = ThreadedMessageStore::new();
    let mut opened = ThreadedMessageStore::new();
    let mut partial = ThreadedMessageStore::new();
    for a in [&first, &second, &third] {
        let signature =
            sign_attestation_v2(&FixtureSigner, &attestation_header_for(a.simple()).unwrap())
                .unwrap();
        let envelope = redact(a.simple(), signature).unwrap();
        assert_eq!(envelope.content_hash(), a.address);
        redacted.append_envelope(envelope, &FixtureSigner).unwrap();
        opened
            .append_opened(
                build_opened(
                    a.simple(),
                    &HEADER_FIELDS,
                    &SignatureSuite::Ed25519,
                    &FixtureSigner,
                )
                .unwrap(),
                &FixtureSigner,
            )
            .unwrap();
        partial
            .append_opened(
                build_opened(
                    a.simple(),
                    &[FieldId::Performative, FieldId::Thread],
                    &SignatureSuite::Ed25519,
                    &FixtureSigner,
                )
                .unwrap(),
                &FixtureSigner,
            )
            .unwrap();
    }
    for store in [&redacted, &opened] {
        assert_eq!(
            verify_causal(
                "tick",
                third.simple().caused_by(),
                store,
                d.causal_protocol.as_ref().unwrap(),
                &thread()
            ),
            VerificationResult::Valid
        );
        assert!(matches!(
            verify_causal(
                "tick",
                extra.simple().caused_by(),
                store,
                d.causal_protocol.as_ref().unwrap(),
                &thread()
            ),
            VerificationResult::Violation(_)
        ));
        assert!(store
            .lookup_in_thread(&ContentHash(first.address.clone()), &thread())
            .is_none());
    }
    assert_eq!(
        verify_causal(
            "tick",
            third.simple().caused_by(),
            &partial,
            d.causal_protocol.as_ref().unwrap(),
            &thread()
        ),
        VerificationResult::Unknown
    );
}

#[test]
fn repeat_does_not_change_the_legacy_non_protocol_route() {
    // close is declared but is not part of this protocol. Strict monitor users
    // separately reject non-protocol messages; the low-level API stays compatible.
    let d = dialect("(repeat 3 tick)");
    accepted(&d, &[], &act("close", "", "@a"));
    assert!(matches!(
        admit(&d, &thread(), &[], &act("tick", "", "@a")),
        Admission::Rejected(_)
    ));
}
