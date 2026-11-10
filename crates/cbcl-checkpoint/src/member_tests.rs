use super::*;

#[test]
fn proof_footprint_failure_is_atomic_and_floor_checks_final_root() {
    // These unit-level fences do not rely on certificate or signing fixtures.
    let clause = cbcl_core::state::StateClause { entries: vec![] };
    let summary = Summary::new(&clause, None).unwrap();
    let mut index = Coverage::default();
    let left = alloc::format!("f1220{}", "1".repeat(64));
    let right = alloc::format!("f1220{}", "2".repeat(64));
    index.insert(&left);
    let mut client = Client {
        context: [3; 32],
        coverage: index.root(),
        summary,
        frontier: vec![left.clone()],
        evidence: Evidence::new(),
    };
    let floor = Floor {
        context: client.context,
        root: [4; 32],
        frontier: vec![left.clone(), right.clone()],
    };
    let before = client.clone();
    assert!(client
        .check_floor(
            &floor,
            &[
                (left.clone(), index.proof(&left)),
                (right.clone(), index.proof(&right))
            ]
        )
        .is_err());
    assert_eq!(client, before);
    index.insert(&right);
    client.coverage = index.root();
    client
        .check_floor(
            &floor,
            &[
                (left.clone(), index.proof(&left)),
                (right.clone(), index.proof(&right)),
            ],
        )
        .unwrap();
    assert!(matches!(
        client.check_floor(&floor, &[(left.clone(), index.proof(&left))]),
        Err(Error::Missing(_))
    ));
    assert!(client
        .check_floor(
            &floor,
            &[
                (left.clone(), index.proof(&left)),
                (left.clone(), index.proof(&left))
            ]
        )
        .is_err());
    let mut other = client.clone();
    other.context = [9; 32];
    let old = client.clone();
    assert!(client.retain_from(&other).is_err());
    assert_eq!(client, old);
}

use crate::test_support::Fixture;
use alloc::format;

fn mutate_simple(m: &Message, f: &mut impl FnMut(&mut Message)) -> Message {
    match m {
        Message::Wrapped {
            wrapper,
            params,
            content,
        } => Message::Wrapped {
            wrapper: *wrapper,
            params: params.clone(),
            content: alloc::boxed::Box::new(mutate_simple(content, f)),
        },
        Message::Dialect {
            dialect_name,
            inner,
        } => Message::Dialect {
            dialect_name: dialect_name.clone(),
            inner: alloc::boxed::Box::new(mutate_simple(inner, f)),
        },
        m => {
            let mut m = m.clone();
            f(&mut m);
            m
        }
    }
}
fn unsigned(m: &SignedMessage) -> Message {
    let Message::Wrapped {
        wrapper: WrapperType::Signed,
        content,
        ..
    } = m.message()
    else {
        panic!("signed")
    };
    content.as_ref().clone()
}
fn resign(m: &SignedMessage, f: &Fixture, edit: &mut impl FnMut(&mut Message)) -> SignedMessage {
    SignedMessage::sign(mutate_simple(&unsigned(m), edit), "@m0", &f.keys).unwrap()
}

#[test]
fn native_thirty_tail_matches_ordinary_admission_and_fold_after_every_step() {
    let f = Fixture::new();
    let c = &f.context;
    let mut members = f.members(&[]);
    let cert = f.certificate(&members);
    let mut client = Client::from_certificate(c, &cert, &f.keys).unwrap();
    let mut monitor = AdmissionMonitor::new(
        c.target.clone(),
        endpoint(c).unwrap(),
        c.target_root.message().clone(),
        Gate { c, keys: &f.keys },
    )
    .unwrap();
    monitor.drain_ready();
    monitor.receive(f.target_open.message().clone()).unwrap();
    monitor.drain_ready();
    let mut acts = vec![
        c.target_root.authenticate(&f.keys).unwrap(),
        f.target_open.authenticate(&f.keys).unwrap(),
    ];
    let mut previous = None;
    for i in 0..30 {
        let refs = previous.iter().cloned().collect::<Vec<_>>();
        let m = f.write(&format!("v{i}"), i + 1, &refs, "@m0");
        let step = members[0].step(&m).unwrap();
        assert!(step
            .replacements
            .iter()
            .all(|(id, p)| p.verify(client.coverage, &native(id)).is_ok()));
        client.apply(&step, c, &f.keys).unwrap();
        for member in &mut members {
            member.accept(&m, c, &f.keys).unwrap();
        }
        monitor.receive(m.message().clone()).unwrap();
        monitor.drain_ready();
        assert_eq!(
            monitor.state(&ContentHash(m.id().unwrap())),
            Some(&AdmissionState::Accepted)
        );
        acts.push(m.authenticate(&f.keys).unwrap());
        assert_eq!(
            client.summary.render_json(),
            cbcl_core::state::render_json(&cbcl_core::state::fold(
                c.target.state.as_ref().unwrap(),
                c.target.causal_protocol.as_ref(),
                &acts
            ))
        );
        assert_eq!(client.coverage, members[0].coverage().root());
        previous = Some(m.authenticate(&f.keys).unwrap().address);
        let replay = members[0].step(&m).unwrap();
        let before = client.clone();
        client.apply(&replay, c, &f.keys).unwrap();
        assert_eq!(client, before);
    }
    let renewed = f.certificate(&members);
    let mut cold = Client::from_certificate(c, &renewed, &f.keys).unwrap();
    cold.check_floor(
        &client.floor(),
        &client
            .frontier
            .iter()
            .map(|id| (id.clone(), members[0].coverage().proof(id)))
            .collect::<Vec<_>>(),
    )
    .unwrap();
    cold.retain_from(&client).unwrap();
    assert_eq!(cold, client);
    let encoded = serde_json::to_vec(&client).unwrap();
    assert_eq!(serde_json::from_slice::<Client>(&encoded).unwrap(), client);
}

#[test]
fn older_known_cut_derives_independently_unknown_and_tampered_cuts_decline() {
    let f = Fixture::new();
    let c = &f.context;
    let mut members = f.members(&[]);
    let old = members[0].manifest(c).unwrap();
    let a = f.write("a", 1, &[], "@m0");
    let b = f.write("b", 2, &[], "@m1");
    for m in &mut members {
        m.accept(&a, c, &f.keys).unwrap();
        m.accept(&b, c, &f.keys).unwrap();
    }
    assert_eq!(members[0].derive(&old.frontier, c, &f.keys).unwrap(), old);
    let latest = members[0].manifest(c).unwrap();
    assert_eq!(latest.frontier.len(), 2);
    assert_eq!(
        members[0].derive(&latest.frontier, c, &f.keys).unwrap(),
        latest
    );
    let e = f.endorsement(&members[0], &old);
    e.authenticate(&f.keys).unwrap();
    let mut unknown = old.clone();
    unknown.frontier = vec![format!("f1220{}", "a".repeat(64))];
    assert!(matches!(
        members[0].derive(&unknown.frontier, c, &f.keys),
        Err(Error::Missing(_))
    ));
    let mut bad = old.clone();
    bad.coverage = [0; 32];
    let candidate = unsigned(&e);
    assert!(members[0]
        .authorize_endorse_with_opener(&bad, candidate.clone(), &f.opener, c, &f.keys)
        .is_err());
    let mut bad = old.clone();
    bad.summary = [0; 32];
    assert!(members[0]
        .authorize_endorse_with_opener(&bad, candidate.clone(), &f.opener, c, &f.keys)
        .is_err());
    // Match the candidate's signed manifest claim to the tampered proposal.
    // Signature, scope, native thread and bootstrap all pass; only independent
    // reconstruction can refuse to issue authority for these wrong roots.
    for change in 0..2 {
        let mut bad = old.clone();
        if change == 0 {
            bad.coverage = [0; 32];
        } else {
            bad.summary = [0; 32];
        }
        let matching = mutate_simple(&candidate, &mut |m| {
            if let Message::Simple { params, .. } = m {
                for field in params.chunks_exact_mut(2) {
                    if field[0] == SExpr::Atom(Atom::Keyword("manifest".into())) {
                        field[1] = SExpr::Atom(Atom::Str(crate::hex(&bad.hash())));
                    }
                }
            }
        });
        let signed = SignedMessage::sign(matching.clone(), members[0].signer(), &f.keys).unwrap();
        let act = signed.authenticate(&f.keys).unwrap();
        crate::certificate::check_scope(&act, c, Some(bad.hash())).unwrap();
        crate::certificate::verify_coordination(
            &signed,
            c,
            &cbcl_parser::checkpoint_dialect::builtin().unwrap(),
            &[c.companion_root().clone(), f.opener.clone()],
            &f.keys,
        )
        .unwrap();
        assert!(
            members[0]
                .authorize_endorse_with_opener(&bad, matching, &f.opener, c, &f.keys,)
                .is_err(),
            "matching signed proposal claims cannot replace independent cut derivation"
        );
    }
    let mut redundant = latest.frontier.clone();
    redundant.push(f.target_open.id().unwrap());
    redundant.sort();
    assert!(members[0].derive(&redundant, c, &f.keys).is_err());
    let recovered = Member::restore(&members[0].snapshot(), c, &f.keys).unwrap();
    assert_eq!(recovered.manifest(c).unwrap(), latest);
    assert_eq!(recovered.derive(&old.frontier, c, &f.keys).unwrap(), old);
}

#[test]
fn concurrent_floor_cannot_drop_a_branch_but_authenticated_tail_can_reach_it() {
    let f = Fixture::new();
    let c = &f.context;
    let mut members = f.members(&[]);
    let left = f.write("left", 1, &[], "@m0");
    let right = f.write("right", 2, &[], "@m1");
    for m in &mut members {
        m.accept(&left, c, &f.keys).unwrap();
    }
    let cert = f.certificate(&members);
    // The same three native signers may independently certify incomparable cuts.
    // Neither certificate elects a history; both continue by ordinary admission.
    let right_members = f.members(core::slice::from_ref(&right));
    let right_cert = f.certificate(&right_members);
    assert_ne!(cert.manifest.coverage, right_cert.manifest.coverage);
    assert_eq!(
        cert.verify(c, &f.keys).unwrap(),
        right_cert.verify(c, &f.keys).unwrap()
    );
    let mut right_client = Client::from_certificate(c, &right_cert, &f.keys).unwrap();
    let left_step = right_members[0].step(&left).unwrap();
    let mut client = Client::from_certificate(c, &cert, &f.keys).unwrap();
    let step = members[0].step(&right).unwrap();
    for m in &mut members {
        m.accept(&right, c, &f.keys).unwrap();
    }
    let full = members[0].client();
    let floor = full.floor();
    assert_eq!(floor.frontier.len(), 2);
    let proofs: Vec<_> = floor
        .frontier
        .iter()
        .map(|id| (id.clone(), members[0].coverage().proof(id)))
        .collect();
    let before = client.clone();
    assert!(client.check_floor(&floor, &proofs).is_err());
    assert_eq!(client, before);
    client.apply(&step, c, &f.keys).unwrap();
    client.check_floor(&floor, &proofs).unwrap();
    assert_eq!(client.summary, full.summary);
    right_client.apply(&left_step, c, &f.keys).unwrap();
    assert_eq!(right_client.summary, client.summary);
    assert_eq!(right_client.coverage, client.coverage);
    assert_eq!(right_client.frontier, client.frontier);
    let parent = f.target_open.id().unwrap();
    assert!(!client.frontier.contains(&parent));
}

#[test]
fn invalid_and_missing_footprints_never_change_client_or_evidence() {
    let f = Fixture::new();
    let c = &f.context;
    let members = f.members(&[]);
    let cert = f.certificate(&members);
    let client = Client::from_certificate(c, &cert, &f.keys).unwrap();
    let a = f.write("a", 1, &[], "@m0");
    let step = members[0].step(&a).unwrap();
    assert_eq!(step.ancestry.len(), 1);
    let mut cases = Vec::new();
    let mut s = step.clone();
    s.identity.present = true;
    cases.push((s, false));
    let mut s = step.clone();
    s.ancestry[0].1.siblings[10] = [9; 32];
    cases.push((s, false));
    let mut s = step.clone();
    s.ancestry.clear();
    cases.push((s, true));
    let mut s = step.clone();
    s.ancestry.push(s.ancestry[0].clone());
    cases.push((s, false));
    let mut s = step.clone();
    s.message = resign(&a, &f, &mut |m| {
        if let Message::Simple { caused_by, .. } = m {
            *caused_by = Some(CausedBy::Single(c.target_root.id().unwrap()));
        }
    });
    s.identity = members[0].coverage().proof(&s.message.id().unwrap());
    s.ancestry.clear();
    cases.push((s, false));
    let mut s = step.clone();
    s.message = resign(&a, &f, &mut |m| {
        if let Message::Simple { params, .. } = m {
            params.extend([
                SExpr::Atom(Atom::Keyword("value".into())),
                SExpr::Atom(Atom::Str("hidden".into())),
            ]);
        }
    });
    s.identity = members[0].coverage().proof(&s.message.id().unwrap());
    cases.push((s, false));
    let mut s = step.clone();
    s.message = resign(&a, &f, &mut |m| {
        if let Message::Simple { params, .. } = m {
            params.extend([
                SExpr::Atom(Atom::Keyword("extraneous".into())),
                SExpr::Atom(Atom::Str("hidden".into())),
            ]);
        }
    });
    s.identity = members[0].coverage().proof(&s.message.id().unwrap());
    cases.push((s, false));
    let mut s = step.clone();
    s.message = resign(&a, &f, &mut |m| {
        if let Message::Simple { params, .. } = m {
            params.extend([
                SExpr::Atom(Atom::Keyword("thread".into())),
                SExpr::Atom(Atom::Str("target".into())),
            ]);
        }
    });
    s.identity = members[0].coverage().proof(&s.message.id().unwrap());
    cases.push((s, false));
    let mut s = step.clone();
    s.message = resign(&a, &f, &mut |m| {
        if let Message::Simple { caused_by, .. } = m {
            *caused_by = Some(CausedBy::Single("not-a-native-id".into()));
        }
    });
    s.identity = members[0].coverage().proof(&s.message.id().unwrap());
    s.ancestry.clear();
    cases.push((s, false));
    for (bad, missing) in cases {
        let mut actual = client.clone();
        let result = actual.apply(&bad, c, &f.keys);
        assert!(result.is_err());
        if missing {
            assert!(matches!(result, Err(Error::Missing(_))));
        }
        assert_eq!(actual, client);
    }
    let mut p = f.members(&[]).remove(0);
    p.accept(&a, c, &f.keys).unwrap();
    let refs = vec![a.authenticate(&f.keys).unwrap().address];
    let b = f.write("b", 2, &refs, "@m0");
    let mut missing = p.step(&b).unwrap();
    missing.replacements.clear();
    let mut actual = p.client().clone();
    let before = actual.clone();
    assert!(matches!(
        actual.apply(&missing, c, &f.keys),
        Err(Error::Missing(_))
    ));
    assert_eq!(actual, before);
}

#[test]
fn imported_certificate_never_creates_independent_signing_provenance() {
    let f = Fixture::new();
    let c = &f.context;
    let history = vec![f.write("a", 1, &[], "@m0")];
    let members = f.members(&history);
    let cert = f.certificate(&members);
    let imported = Client::from_certificate(c, &cert, &f.keys).unwrap();
    let empty = f.members(&[]).remove(0);
    assert!(empty.derive(&imported.frontier, c, &f.keys).is_err());
    let mut claimed = empty.snapshot();
    claimed.independent = true;
    // A serialized flag cannot supply the unknown accepted branches.
    let restored = Member::restore(&claimed, c, &f.keys).unwrap();
    assert!(restored.derive(&imported.frontier, c, &f.keys).is_err());
    claimed.accepted.push(history[0].clone());
    let reconstructed = Member::restore(&claimed, c, &f.keys).unwrap();
    assert_eq!(reconstructed.manifest(c).unwrap(), cert.manifest);
    claimed.accepted.push(resign(&history[0], &f, &mut |m| {
        if let Message::Simple { caused_by, .. } = m {
            *caused_by = Some(CausedBy::Single(c.target_root.id().unwrap()));
        }
    }));
    assert!(Member::restore(&claimed, c, &f.keys).is_err());
}

#[test]
fn capability_binds_actual_unsigned_message_and_verified_opener_before_signing() {
    let f = Fixture::new();
    let c = &f.context;
    let members = f.members(&[]);
    let m = &members[0];
    let manifest = m.manifest(c).unwrap();
    let signed = f.endorsement(m, &manifest);
    let candidate = unsigned(&signed);
    let capability = m
        .authorize_endorse_with_opener(&manifest, candidate.clone(), &f.opener, c, &f.keys)
        .unwrap();
    assert_eq!(capability.unsigned(), &candidate);
    assert_eq!(capability.signer(), "@m0");
    assert_eq!(capability.sign(&f.keys).unwrap(), signed);
    let altered = mutate_simple(&candidate, &mut |m| {
        if let Message::Simple { thread, .. } = m {
            *thread = Some("foreign".into());
        }
    });
    assert!(m
        .authorize_endorse_with_opener(&manifest, altered, &f.opener, c, &f.keys)
        .is_err());
    let altered = mutate_simple(&candidate, &mut |m| {
        if let Message::Simple { params, .. } = m {
            params.extend([
                SExpr::Atom(Atom::Keyword("manifest".into())),
                SExpr::Atom(Atom::Str(crate::hex(&manifest.hash()))),
            ]);
        }
    });
    assert!(m
        .authorize_endorse_with_opener(&manifest, altered, &f.opener, c, &f.keys)
        .is_err());
    let mut foreign = c.clone();
    foreign.profile = [99; 32];
    assert!(m.derive(&manifest.frontier, &foreign, &f.keys).is_err());
}

#[test]
fn pinned_opener_default_authorizer_cannot_bypass_native_bootstrap() {
    let f = Fixture::new();
    let c = &f.context;
    let mut members = f.members(&[]);
    let manifest = members[0].manifest(c).unwrap();
    let signed = f.endorsement(&members[0], &manifest);
    let candidate = unsigned(&signed);
    assert!(members[0]
        .authorize_endorse(&manifest, candidate.clone(), c, &f.keys)
        .is_err());
    members[0].pin_opener(&f.opener, c, &f.keys).unwrap();
    let cap = members[0]
        .authorize_endorse(&manifest, candidate.clone(), c, &f.keys)
        .unwrap();
    assert_eq!(cap.sign(&f.keys).unwrap(), signed);
    let record = members[0].snapshot();
    let restored = Member::restore(&record, c, &f.keys).unwrap();
    restored
        .authorize_endorse(&manifest, candidate, c, &f.keys)
        .unwrap();
    let opener_unsigned = unsigned(&f.opener);
    let wrong = SignedMessage::sign(
        mutate_simple(&opener_unsigned, &mut |m| {
            if let Message::Simple { thread, .. } = m {
                *thread = Some("wrong".into());
            }
        }),
        "@init",
        &f.keys,
    )
    .unwrap();
    assert!(members[0].pin_opener(&wrong, c, &f.keys).is_err());
    assert!(members[0]
        .authorize_endorse_with_opener(&manifest, unsigned(&signed), &wrong, c, &f.keys)
        .is_err());
}

#[test]
fn stale_proofs_wrong_context_language_and_bad_signatures_cannot_install() {
    let f = Fixture::new();
    let c = &f.context;
    let mut members = f.members(&[]);
    let cert = f.certificate(&members);
    let mut client = Client::from_certificate(c, &cert, &f.keys).unwrap();
    let a = f.write("a", 1, &[], "@m0");
    let b = f.write("b", 2, &[], "@m0");
    let old_step = members[0].step(&b).unwrap();
    let step = members[0].step(&a).unwrap();
    client.apply(&step, c, &f.keys).unwrap();
    for m in &mut members {
        m.accept(&a, c, &f.keys).unwrap();
    }
    let before = client.clone();
    assert!(client.apply(&old_step, c, &f.keys).is_err());
    assert_eq!(client, before);
    let mut foreign = c.clone();
    foreign.profile = [44; 32];
    let good = members[0].step(&b).unwrap();
    assert!(client.apply(&good, &foreign, &f.keys).is_err());
    assert_eq!(client, before);
    let mut bad = good.clone();
    let Message::Wrapped { params, .. } = bad.message.message().clone() else {
        panic!("signed")
    };
    let mut message = bad.message.message().clone();
    if let Message::Wrapped { params, .. } = &mut message {
        params[1] = SExpr::Atom(Atom::Str("00".repeat(64)));
    }
    bad.message = SignedMessage::from_message(message);
    assert!(client.apply(&bad, c, &f.keys).is_err());
    assert_eq!(client, before);
    assert_eq!(params.len(), 2);
    let mut message = unsigned(&b);
    if let Message::Dialect { dialect_name, .. } = &mut message {
        *dialect_name = "wrong-language".into();
    }
    let badmessage = SignedMessage::sign(message, "@m0", &f.keys).unwrap();
    let bad = members[0].step(&badmessage).unwrap();
    assert!(client.apply(&bad, c, &f.keys).is_err());
    assert_eq!(client, before);
    let mut wrongsummary = cert.clone();
    wrongsummary.summary.push(0);
    assert!(Client::from_certificate(c, &wrongsummary, &f.keys).is_err());
}

#[test]
fn scoped_position_profile_still_refuses_global_fanin() {
    let f = Fixture::new();
    let mut c = f.context.clone();
    validate_profile(&c).unwrap();
    c.target
        .causal_protocol
        .as_mut()
        .unwrap()
        .steps
        .get_mut("write")
        .unwrap()
        .predecessors = vec![NodeRef::All(["open".into()].into_iter().collect())];
    assert_eq!(validate_profile(&c), Err(Error::Unsupported));
}

#[test]
fn covered_replays_preserve_distinct_signature_attempts_without_refolding() {
    let f = Fixture::new();
    let c = &f.context;
    let a = f.write("a", 1, &[], "@m0");
    let members = f.members(core::slice::from_ref(&a));
    let cert = f.certificate(&members);
    let mut client = Client::from_certificate(c, &cert, &f.keys).unwrap();
    let step = members[0].step(&a).unwrap();
    client.apply(&step, c, &f.keys).unwrap();
    let original = client.clone();
    // Isolate identity-vs-attempt retention using an explicit test verifier with
    // two accepted signature encodings. Real Ed25519 authenticates all fixture
    // inputs in the other tests; this does not claim this alternate is Ed25519.
    struct Alternate<'a>(&'a crate::test_support::Keys);
    impl KeyVerifier for Alternate<'_> {
        fn verify(&self, key: &str, p: &[u8], s: &[u8]) -> bool {
            s == [77; 64] || self.0.verify(key, p, s)
        }
    }
    let mut alternate = a.message().clone();
    if let Message::Wrapped { params, .. } = &mut alternate {
        params[1] = SExpr::Atom(Atom::Str(crate::hex(&[77; 64])));
    }
    let mut replay = step.clone();
    replay.message = SignedMessage::from_message(alternate);
    assert_eq!(replay.message.id().unwrap(), a.id().unwrap());
    assert_ne!(replay.message.encode(), a.encode());
    client.apply(&replay, c, &Alternate(&f.keys)).unwrap();
    assert_eq!(client.coverage, original.coverage);
    assert_eq!(client.summary, original.summary);
    assert_eq!(client.frontier, original.frontier);
    assert_eq!(client.evidence.len(), original.evidence.len() + 1);
    let mut rebased = Client::from_certificate(c, &cert, &f.keys).unwrap();
    rebased.retain_from(&client).unwrap();
    assert_eq!(rebased.evidence, client.evidence);
}

#[test]
fn member_archive_counters_measure_actual_delta_reads_and_current_freeze() {
    fn assert_send<T: Send>() {}
    assert_send::<Member>();
    fn assert_no_prefix_or_snapshot(work: MemberWork) {
        assert_eq!(work.prefix_reconstruction_body_reads, 0);
        assert_eq!(work.snapshot_body_records, 0);
    }
    let f = Fixture::new();
    for prefix in [0, 7, 31] {
        let mut member = Member::new(&f.context, "@m0", &f.keys).unwrap();
        member.accept(&f.target_open, &f.context, &f.keys).unwrap();
        let mut previous = None;
        for i in 0..prefix {
            let refs = previous.iter().cloned().collect::<Vec<_>>();
            let message = f.write(&format!("prefix-{i}"), i + 1, &refs, "@m0");
            member.accept(&message, &f.context, &f.keys).unwrap();
            previous = Some(message.authenticate(&f.keys).unwrap().address);
        }
        member.reset_work();
        let freeze = member.manifest(&f.context).unwrap();
        assert_eq!(
            member
                .derive(&freeze.frontier, &f.context, &f.keys)
                .unwrap(),
            freeze
        );
        assert_eq!(member.work(), MemberWork::default());
        for i in 0..32 {
            let refs = previous.iter().cloned().collect::<Vec<_>>();
            let message = f.write(&format!("delta-{i}"), prefix + i + 1, &refs, "@m0");
            let _offered = member.step(&message).unwrap();
            member.accept(&message, &f.context, &f.keys).unwrap();
            previous = Some(message.authenticate(&f.keys).unwrap().address);
        }
        let latest = member.manifest(&f.context).unwrap();
        assert_eq!(
            member
                .derive(&latest.frontier, &f.context, &f.keys)
                .unwrap(),
            latest
        );
        let work = member.work();
        assert_eq!(
            work.dependency_body_lookups, 64,
            "each of 32 messages has one named accepted parent, looked up by step and accept"
        );
        assert_no_prefix_or_snapshot(work);
        member.reset_work();
        let audited = member.audit_replay(&f.context, &f.keys).unwrap();
        assert_eq!(audited, latest);
        assert_eq!(
            member.work().prefix_reconstruction_body_reads,
            prefix as usize + 34
        );
        assert_eq!(
            member.work().dependency_body_lookups,
            0,
            "temporary replay members maintain separate archive counters"
        );
        assert_eq!(member.work().snapshot_body_records, 0);
        // Same dynamic acceptance predicate as current freezing. A deliberate
        // full replay inside a freeze must trip it, rather than a zero counter
        // making the negative control indistinguishable from the fast path.
        #[cfg(feature = "std")]
        {
            member.reset_work();
            let detected = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let _freeze = member.audit_replay(&f.context, &f.keys).unwrap();
                assert_no_prefix_or_snapshot(member.work());
            }));
            assert!(
                detected.is_err(),
                "the work fence must detect replay-in-freeze"
            );
        }
    }
}

#[test]
fn older_cut_counts_only_selected_archive_bodies_and_snapshot_counts_actual_records() {
    let f = Fixture::new();
    let mut member = Member::new(&f.context, "@m0", &f.keys).unwrap();
    member.accept(&f.target_open, &f.context, &f.keys).unwrap();
    let old = member.manifest(&f.context).unwrap();
    for i in 0..9 {
        member
            .accept(
                &f.write(&format!("later-{i}"), i + 1, &[], "@m0"),
                &f.context,
                &f.keys,
            )
            .unwrap();
    }
    member.reset_work();
    assert_eq!(
        member.derive(&old.frontier, &f.context, &f.keys).unwrap(),
        old
    );
    assert_eq!(
        member.work(),
        MemberWork {
            dependency_body_lookups: 0,
            prefix_reconstruction_body_reads: 2,
            snapshot_body_records: 0
        },
        "derive reads only selected root/open, not every later body to recover their order"
    );
    member.reset_work();
    let snapshot = member.snapshot();
    assert_eq!(
        member.work().snapshot_body_records,
        snapshot.accepted.len() + snapshot.evidence.len()
    );
    assert_eq!(member.work().dependency_body_lookups, 0);
    assert_eq!(member.work().prefix_reconstruction_body_reads, 0);
    assert_eq!(snapshot.accepted.len(), 11);
    // The counter records each copied record again, rather than claiming that
    // a repeated full snapshot is free because no state effects changed.
    let second = member.snapshot();
    assert_eq!(
        member.work().snapshot_body_records,
        2 * (second.accepted.len() + second.evidence.len())
    );
    member.reset_work();
    assert_eq!(member.work(), MemberWork::default());
    let recovered = Member::restore(&snapshot, &f.context, &f.keys).unwrap();
    assert_eq!(
        recovered.manifest(&f.context).unwrap(),
        member.manifest(&f.context).unwrap()
    );
}
