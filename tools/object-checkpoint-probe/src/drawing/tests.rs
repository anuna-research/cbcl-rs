use super::*;

fn status(f: &Fixture, all: &[Wire], candidate: &Wire) -> Result<VerificationResult> {
    let m = replay(f, all)?;
    match m.state(&ContentHash(candidate.id())) {
        Some(AdmissionState::Accepted) => Ok(VerificationResult::Valid),
        Some(AdmissionState::Pending) => Ok(VerificationResult::Unknown),
        Some(AdmissionState::Rejected(e)) => Ok(VerificationResult::Violation(e.clone())),
        None => Err("not received".into()),
    }
}

#[test]
fn cached_certificate_and_offline_reconstruction_admit_the_same_tail_as_core() {
    let f = Fixture::new(40, 8, 24);
    let config = Config::new(&f);
    let archive = Archive::new(&f);
    let (cert, recon, mut p) = packages(&f, 24, &archive).unwrap();
    let mut a = cert.open(&config).unwrap();
    let mut b = recon.open(&config).unwrap();
    let mut all = f.edits.clone();
    let mut known = BTreeSet::new();
    archive.reset();
    for w in tail(&f, 24) {
        let step = p.step(&w, &archive, &mut known, &f.root.id()).unwrap();
        all.push(w.clone());
        let expected = status(&f, &all, &w).unwrap();
        assert_eq!(expected, VerificationResult::Valid);
        assert_eq!(a.admit(&step, &config).unwrap(), expected);
        assert_eq!(b.admit(&step, &config).unwrap(), expected);
        let m = replay(&f, &all).unwrap();
        assert_eq!(render_state(&a.state, &f.dialect), folded(&f, &m, &all));
        assert_eq!(a.state, b.state);
    }
    assert_eq!(archive.body_reads.get(), 0);
    assert!(archive.header_reads.get() > 0);
}

#[test]
fn missing_ancestry_is_unknown_and_complete_evidence_retries_successfully() {
    let f = Fixture::new(20, 8, 10);
    let config = Config::new(&f);
    let archive = Archive::new(&f);
    let (cert, _, mut p) = packages(&f, 10, &archive).unwrap();
    let w = tail(&f, 10).remove(0);
    let good = p
        .step(&w, &archive, &mut BTreeSet::new(), &f.root.id())
        .unwrap();
    assert!(good.ancestry.len() > 1);
    let mut bad = good.clone();
    bad.ancestry.pop();
    let mut client = cert.open(&config).unwrap();
    let before = client.state.clone();
    let root = client.coverage;
    assert_eq!(
        client.admit(&bad, &config).unwrap(),
        VerificationResult::Unknown
    );
    assert_eq!(client.state, before);
    assert_eq!(client.coverage, root);
    assert_eq!(
        client.admit(&good, &config).unwrap(),
        VerificationResult::Valid
    );
}

#[test]
fn authentic_but_invalid_repeat_position_is_not_checkpoint_bypassed() {
    let f = Fixture::new(16, 8, 8);
    let config = Config::new(&f);
    let archive = Archive::new(&f);
    let (cert, _, mut p) = packages(&f, 8, &archive).unwrap();
    let last = f.edits.last().unwrap();
    let invalid = fixture::edit("shape-0", "red", false, &[], &last.id(), 900, 3, &f.keys);
    let step = p
        .step(&invalid, &archive, &mut BTreeSet::new(), &f.root.id())
        .unwrap();
    let mut all = f.edits.clone();
    all.push(invalid.clone());
    let expected = status(&f, &all, &invalid).unwrap();
    assert!(matches!(expected, VerificationResult::Violation(_)));
    let mut client = cert.open(&config).unwrap();
    let before = client.state.clone();
    let root = client.coverage;
    assert_eq!(client.admit(&step, &config).unwrap(), expected);
    assert_eq!(client.state, before);
    assert_eq!(client.coverage, root);
}

#[test]
fn uncovered_dependency_is_unknown_and_cannot_be_injected_as_an_envelope() {
    let f = Fixture::new(20, 8, 10);
    let config = Config::new(&f);
    let archive = Archive::new(&f);
    let (cert, _, p) = packages(&f, 10, &archive).unwrap();
    let missing = fixture::edit(
        "x",
        "missing",
        false,
        &[],
        &f.edits[0].id(),
        500,
        3,
        &f.keys,
    );
    let child = fixture::edit("x", "child", false, &[], &missing.id(), 501, 3, &f.keys);
    let act = child.act();
    let mut c = p.coverage.clone();
    let identity = c.proof(&act.address);
    c.insert(&act.address);
    let step = Step {
        wire: child.clone(),
        identity,
        replacements: vec![],
        ancestry: vec![],
    };
    let mut all = f.edits.clone();
    all.push(child.clone());
    assert_eq!(
        status(&f, &all, &child).unwrap(),
        VerificationResult::Unknown
    );
    let mut client = cert.open(&config).unwrap();
    assert_eq!(
        client.admit(&step, &config).unwrap(),
        VerificationResult::Unknown
    );
    let mut injected = step;
    injected.ancestry.push(EnvelopeEvidence {
        header: opened(&missing),
        coverage: p.coverage.proof(&missing.act().address),
    });
    assert!(client.admit(&injected, &config).is_err());
}

#[test]
fn coverage_opening_signature_and_semantic_envelope_mutations_reject_atomically() {
    let f = Fixture::new(20, 8, 10);
    let config = Config::new(&f);
    let archive = Archive::new(&f);
    let (cert, _, mut p) = packages(&f, 10, &archive).unwrap();
    let w = tail(&f, 10).remove(0);
    let good = p
        .step(&w, &archive, &mut BTreeSet::new(), &f.root.id())
        .unwrap();
    let reject = |step: &Step| {
        let mut client = cert.open(&config).unwrap();
        let before = client.state.clone();
        let root = client.coverage;
        assert!(client.admit(step, &config).is_err());
        assert_eq!(client.state, before);
        assert_eq!(client.coverage, root);
    };
    let mut s = good.clone();
    s.wire.signature[0] ^= 1;
    reject(&s);
    let mut s = good.clone();
    s.wire.root_signature[0] ^= 1;
    reject(&s);
    let mut s = good.clone();
    s.ancestry[0].coverage.present = false;
    reject(&s);
    let mut s = good.clone();
    s.ancestry[0].coverage.siblings[0].1[0] ^= 1;
    reject(&s);
    let mut s = good.clone();
    s.ancestry[0].header.envelope.signature[0] ^= 1;
    reject(&s);
    let mut s = good.clone();
    s.ancestry[0].header.envelope.openings[0].value = SExpr::Atom(Atom::Symbol("open".into()));
    reject(&s);
    let mut s = good.clone();
    s.ancestry[0].header.cause = Some(CausedBy::Single(f.root.id()));
    reject(&s);
    let mut s = good.clone();
    s.ancestry[0].header.envelope.openings.pop();
    reject(&s);
}

#[test]
fn cached_policy_is_three_distinct_pinned_votes_and_context_is_immutable() {
    let f = Fixture::new(20, 8, 10);
    let config = Config::new(&f);
    let archive = Archive::new(&f);
    let (cert, recon, _) = packages(&f, 10, &archive).unwrap();
    let mut bad = cert.clone();
    bad.votes.pop();
    assert!(bad.open(&config).is_err());
    let mut bad = cert.clone();
    bad.votes[1] = bad.votes[0].clone();
    assert!(bad.open(&config).is_err());
    let mut bad = cert.clone();
    bad.cut.context = [0; 32];
    assert!(bad.open(&config).is_err());
    let mut bad = cert.clone();
    bad.state.live.clear();
    assert!(bad.open(&config).is_err());
    let mut bad = cert.clone();
    bad.votes[0].signature[0] ^= 1;
    assert!(bad.open(&config).is_err());
    let mut bad = recon;
    bad.anchors.pop();
    assert!(bad.open(&config).is_err());
}

#[test]
fn replayed_covered_write_does_not_resurrect_deleted_state() {
    let f = Fixture::new(25, 8, 10);
    let config = Config::new(&f);
    let archive = Archive::new(&f);
    let (cert, _, mut p) = packages(&f, 10, &archive).unwrap();
    let old = &f.edits[2];
    let step = p
        .step(old, &archive, &mut BTreeSet::new(), &f.root.id())
        .unwrap();
    let mut client = cert.open(&config).unwrap();
    let before = client.state.clone();
    let root = client.coverage;
    assert_eq!(
        client.admit(&step, &config).unwrap(),
        VerificationResult::Valid
    );
    assert_eq!(client.state, before);
    assert_eq!(client.coverage, root);
}

#[test]
fn concurrent_choices_remain_verdict_neutral_and_messages_are_retained() {
    let f = Fixture::new(20, 8, 10);
    let config = Config::new(&f);
    let archive = Archive::new(&f);
    let (cert, _, mut p) = packages(&f, 10, &archive).unwrap();
    let parent = &f.edits[0];
    let a = fixture::edit("fork", "red", false, &[], &parent.id(), 700, 3, &f.keys);
    let b = fixture::edit("fork", "", true, &[], &parent.id(), 701, 3, &f.keys);
    let mut client = cert.open(&config).unwrap();
    let mut known = BTreeSet::new();
    let mut all = f.edits.clone();
    for w in [&a, &b] {
        let step = p.step(w, &archive, &mut known, &f.root.id()).unwrap();
        assert_eq!(
            client.admit(&step, &config).unwrap(),
            VerificationResult::Valid
        );
        all.push(w.clone());
    }
    let core = replay(&f, &all).unwrap();
    assert_eq!(
        render_state(&client.state, &f.dialect),
        folded(&f, &core, &all)
    );
    assert!(client
        .store
        .contains(&ContentHash(a.id()), &config.thread()));
    assert!(client
        .store
        .contains(&ContentHash(b.id()), &config.thread()));
    // The existing detector does not resolve expanded repeat names to wire names.
    // Preserve its verdicts; do not claim this experiment fixes that limitation.
    assert_eq!(
        cbcl_core::equivocation::equivocation(
            &KeyId::parse("@m3").unwrap(),
            &config.thread(),
            &client.store,
            &f.dialect
        )
        .is_some(),
        cbcl_core::equivocation::equivocation(
            &KeyId::parse("@m3").unwrap(),
            &config.thread(),
            core.accepted(),
            &f.dialect
        )
        .is_some()
    );
}

#[test]
fn unindexed_equivocation_still_detects_after_checkpoint_loading() {
    let f = Fixture::new(20, 8, 10);
    let config = Config::new(&f);
    let archive = Archive::new(&f);
    let (cert, _, mut p) = packages(&f, 10, &archive).unwrap();
    fn content(message: &mut Message, value: &str) {
        match message {
            Message::Wrapped { content: c, .. } => content(c, value),
            Message::Dialect { inner, .. } => content(inner, value),
            Message::Simple { content, .. } => *content = SExpr::Atom(Atom::Str(value.into())),
            _ => panic!("unexpected fixture"),
        }
    }
    let mut client = cert.open(&config).unwrap();
    for value in ["fork-a", "fork-b"] {
        let mut m = f.edits[0].message.clone();
        content(&mut m, value);
        let w = Wire::signed(m, 0, &f.keys);
        let step = p
            .step(&w, &archive, &mut BTreeSet::new(), &f.root.id())
            .unwrap();
        assert_eq!(
            client.admit(&step, &config).unwrap(),
            VerificationResult::Valid
        );
    }
    assert!(cbcl_core::equivocation::equivocation(
        &KeyId::parse("@m0").unwrap(),
        &config.thread(),
        &client.store,
        &f.dialect
    )
    .is_some());
}

#[test]
fn supplied_covered_replay_preserves_evidence_for_a_new_equivocation() {
    let f = Fixture::new(20, 8, 10);
    let config = Config::new(&f);
    let archive = Archive::new(&f);
    let (cert, _, mut p) = packages(&f, 10, &archive).unwrap();
    let old = f.edits[0].clone();
    let mut replacement = old.message.clone();
    let Message::Wrapped { content, .. } = &mut replacement else {
        panic!("signed wrapper")
    };
    let Message::Dialect { inner, .. } = content.as_mut() else {
        panic!("dialect")
    };
    let Message::Simple { content, .. } = inner.as_mut() else {
        panic!("simple")
    };
    *content = SExpr::Atom(Atom::Str("conflicting-open".into()));
    let new = Wire::signed(replacement, 0, &f.keys);
    let mut client = cert.open(&config).unwrap();
    let mut known = BTreeSet::new();
    for w in [&old, &new] {
        let step = p.step(w, &archive, &mut known, &f.root.id()).unwrap();
        assert_eq!(
            client.admit(&step, &config).unwrap(),
            VerificationResult::Valid
        );
    }
    assert!(client
        .store
        .contains(&ContentHash(old.id()), &config.thread()));
    client.signed_bodies[&old.id()]
        .authenticate(&f.dialect, &config.roster)
        .unwrap();
    assert!(cbcl_core::equivocation::equivocation(
        &KeyId::parse("@m0").unwrap(),
        &config.thread(),
        &client.store,
        &f.dialect
    )
    .is_some());
    let proof = cbcl_core::equivocation::EquivocationProof {
        key: KeyId::parse("@m0").unwrap(),
        thread: config.thread().0,
        dialect_hash: dialect_hash(&f.dialect),
        first: cbcl_core::equivocation::ProofMember::OpenedEnvelope(
            opened(&client.signed_bodies[&old.id()]).envelope,
        ),
        second: cbcl_core::equivocation::ProofMember::OpenedEnvelope(
            opened(&client.signed_bodies[&new.id()]).envelope,
        ),
    };
    cbcl_core::equivocation::verify_equivocation_proof(
        &proof,
        &f.dialect,
        &KeyVerifier(config.roster[0]),
    )
    .unwrap();
}

fn retained(client: &Client, config: &Config<'_>) -> BTreeSet<ContentHash> {
    client
        .store
        .frontier(&config.thread())
        .into_iter()
        .flat_map(|h| client.store.causal_closure(h, &config.thread()))
        .collect()
}

#[test]
fn anchor_order_does_not_discard_bridge_evidence() {
    let f = Fixture::new(40, 8, 24);
    let config = Config::new(&f);
    let archive = Archive::new(&f);
    let (_, recon, _) = packages(&f, 24, &archive).unwrap();
    let a = recon.open(&config).unwrap();
    let mut reversed = recon;
    reversed.anchors.reverse();
    let b = reversed.open(&config).unwrap();
    assert_eq!(a.state, b.state);
    assert_eq!(a.coverage, b.coverage);
    assert_eq!(retained(&a, &config), retained(&b, &config));
    assert_eq!(
        a.signed_bodies.keys().collect::<Vec<_>>(),
        b.signed_bodies.keys().collect::<Vec<_>>()
    );
    assert_eq!(retained(&a, &config).len(), 25);
}

#[test]
fn longer_continuation_matches_core_without_implicit_history_collection() {
    let f = Fixture::new(32, 8, 24);
    let config = Config::new(&f);
    let archive = Archive::new(&f);
    let (cert, _, mut p) = packages(&f, 24, &archive).unwrap();
    let mut client = cert.open(&config).unwrap();
    let mut known = BTreeSet::new();
    let mut all = f.edits.clone();
    let mut previous = f.edits[0].id();
    let mut replaced: Vec<String> = vec![];
    for i in 0..40 {
        if i % 8 == 0 {
            previous = f.edits[0].id();
        }
        let w = fixture::edit(
            "continuation",
            "blue",
            false,
            &replaced,
            &previous,
            2000 + i,
            0,
            &f.keys,
        );
        let step = p.step(&w, &archive, &mut known, &f.root.id()).unwrap();
        assert_eq!(
            client.admit(&step, &config).unwrap(),
            VerificationResult::Valid
        );
        previous = w.id();
        replaced = vec![w.act().address];
        all.push(w);
    }
    let full = replay(&f, &all).unwrap();
    assert_eq!(
        render_state(&client.state, &f.dialect),
        folded(&f, &full, &all)
    );
    assert_eq!(retained(&client, &config).len(), 41);
}

#[test]
fn signed_nonsimple_input_is_rejected_without_panicking() {
    let f = Fixture::new(2, 2, 1);
    let message = Message::Meta {
        dialect_def: SExpr::List(vec![]),
    };
    let signature = f.keys[0].sign(&encoded(&message)).to_bytes().to_vec();
    let wire = Wire {
        message,
        signer: 0,
        signature,
        root_signature: vec![0; 64],
    };
    assert!(wire
        .authenticate(&f.dialect, &fixture::roster(&f.keys))
        .is_err());
}

#[test]
fn public_cached_wires_suffice_to_build_native_openings() {
    let f = Fixture::new(4, 4, 2);
    let roster = fixture::roster(&f.keys);
    let serialized = encoded(&f.edits);
    // Deserialize just public transport; no signing key enters opened().
    let wires: Vec<Wire> = serde_json::from_slice(&serialized).unwrap();
    for w in wires {
        let record = opened(&w);
        cbcl_core::envelope::verify_opened(&record.envelope, &KeyVerifier(roster[w.signer]))
            .unwrap();
        assert!(record.envelope.opening(FieldId::Payload).is_none());
    }
}

#[test]
fn valid_and_corrupt_attempts_of_one_message_do_not_alias() {
    let f = Fixture::new(2, 2, 1);
    let good = f.edits[1].clone();
    let mut bad = good.clone();
    bad.signature[0] ^= 1;
    for attempts in [
        vec![good.clone(), bad.clone()],
        vec![bad.clone(), good.clone()],
    ] {
        let gate = Gate::new(&f.dialect, &fixture::roster(&f.keys), &attempts);
        assert!(gate.check_attempt(&good).is_ok());
        assert!(gate.check_attempt(&bad).is_err());
    }
    let mut history = f.edits.clone();
    history.push(bad);
    assert!(replay(&f, &history).is_err());
}

#[test]
fn layered_full_message_queries_match_a_materialized_union() {
    let f = Fixture::new(6, 8, 2);
    let thread = ThreadId(fixture::THREAD.into());
    let mut base = ThreadedMessageStore::new();
    let mut staged = ThreadedMessageStore::new();
    let mut union = ThreadedMessageStore::new();
    let mut ids = Vec::new();
    for (i, w) in f.edits.iter().enumerate() {
        // Exercise both top-level Simple and opaque wrapper store semantics.
        let m = if i % 2 == 0 {
            w.message.clone()
        } else {
            w.message.innermost_simple().unwrap().clone()
        };
        let id = ContentHash(w.id());
        ids.push(id.clone());
        if i % 2 == 0 {
            base.append(id.clone(), thread.clone(), m.clone());
        } else {
            staged.append(id.clone(), thread.clone(), m.clone());
        }
        union.append(id, thread.clone(), m);
    }
    let layered = Layered {
        base: &base,
        staged: &staged,
    };
    for id in ids
        .iter()
        .chain(std::iter::once(&ContentHash("missing".into())))
    {
        assert_eq!(
            layered.lookup_in_thread(id, &thread),
            union.lookup_in_thread(id, &thread)
        );
        assert_eq!(
            layered
                .causal_closure(id, &thread)
                .into_iter()
                .collect::<BTreeSet<_>>(),
            union.causal_closure(id, &thread).into_iter().collect()
        );
        assert!(!layered.contains(id, &ThreadId("other-thread".into())));
    }
    assert_eq!(
        layered
            .frontier(&thread)
            .into_iter()
            .collect::<BTreeSet<_>>(),
        union.frontier(&thread).into_iter().collect()
    );
}
