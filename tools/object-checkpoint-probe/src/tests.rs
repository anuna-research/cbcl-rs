use super::*;

fn keys() -> (Vec<SigningKey>, Vec<VerifyingKey>) {
    let keys: Vec<_> = (1..=3).map(|i| SigningKey::from_bytes(&[i; 32])).collect();
    let roster = keys.iter().map(SigningKey::verifying_key).collect();
    (keys, roster)
}

#[test]
fn same_set_has_same_summary_and_root_under_reordering_and_duplicates() {
    let ops = workload(40);
    let mut reverse = ops.clone();
    reverse.reverse();
    reverse.extend(ops.iter().cloned());
    let mut a = Replica::new();
    let mut b = Replica::new();
    for op in &ops {
        a.apply(op).unwrap();
    }
    for op in &reverse {
        b.apply(op).unwrap();
    }
    assert_eq!(a.summary, b.summary);
    assert_eq!(a.coverage.root(), b.coverage.root());
    assert_eq!(a.summary.render(), oracle(&ops));
}

#[test]
fn independent_kernel_agrees_after_every_prefix_and_uncovered_edit() {
    // Deterministic mixed concurrent/overwrite/delete/replay workload.
    let mut seed = 42_u64;
    let mut ops: Vec<Op> = Vec::new();
    let mut replica = Replica::new();
    for i in 0..100 {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        let key = format!("shape-{}", seed % 5);
        let refs: Vec<_> = ops
            .iter()
            .rev()
            .filter(|o| o.key == key)
            .take((seed % 3) as usize)
            .map(|o| o.id.clone())
            .collect();
        let op = if i > 0 && i % 11 == 0 {
            ops[i / 2].clone()
        } else {
            operation(&key, &format!("v{}", seed % 7), i % 7 == 0, &refs, i as u64)
        };
        replica.apply(&op).unwrap();
        ops.push(op);
        assert_eq!(replica.summary.render(), oracle(&ops), "prefix {i}");
    }
}

#[test]
fn delayed_creation_does_not_resurrect_a_deleted_shape() {
    let creation = operation("x", "red", false, &[], 1);
    let deletion = operation("x", "", true, std::slice::from_ref(&creation.id), 2);
    let (keys, roster) = keys();
    let ops = vec![deletion.clone()];
    let (snapshot, mut provider) = build(&ops, &[1, 1, 1], &keys);
    let mut client = verify(&snapshot, &roster).unwrap();
    assert_eq!(client.pending.len(), 1);
    let mut root = snapshot.target_coverage;
    let step = provider.apply(&creation).unwrap();
    advance(&mut client, &mut root, &step).unwrap();
    assert!(client.live.is_empty());
    assert!(client.pending.is_empty());
    assert_eq!(client.render(), oracle(&[deletion, creation]));
}

#[test]
fn snapshots_with_lagging_members_continue_without_covered_bodies() {
    let ops = workload(50);
    let (keys, roster) = keys();
    let (snapshot, mut provider) = build(&ops, &[15, 35, 50], &keys);
    let mut client = verify(&snapshot, &roster).unwrap();
    let mut root = snapshot.target_coverage;
    let old = ops[4].clone();
    let concurrent = operation("shape-4", "concurrent", false, &[], 100);
    let erase = operation(
        "shape-4",
        "",
        true,
        std::slice::from_ref(&concurrent.id),
        101,
    );
    let mut all = ops;
    for op in [old, concurrent, erase] {
        let step = provider.apply(&op).unwrap();
        advance(&mut client, &mut root, &step).unwrap();
        all.push(op);
        assert_eq!(client.render(), oracle(&all));
    }
}

#[test]
fn snapshot_of_snapshot_and_unequal_compaction_horizons() {
    let ops = workload(40);
    let (keys, roster) = keys();
    let (first, mut provider) = build(&ops, &[38, 39, 40], &keys);
    let state = verify(&first, &roster).unwrap();
    let mut second = first.clone();
    // A client can sign its verified compact state without holding old bodies/index.
    for (member, a) in second.anchors.iter_mut().enumerate() {
        a.state = state.clone();
        a.descriptor = Descriptor {
            scope: SCOPE.into(),
            member,
            coverage: first.target_coverage,
            summary: state.hash(),
        };
        a.signature = keys[member]
            .sign(&encoded(&a.descriptor))
            .to_bytes()
            .to_vec();
        a.bridge.clear();
    }
    let tail = operation("fresh", "green", false, &[], 999);
    let step = provider.apply(&tail).unwrap();
    // Preserve one old anchor: verifiers see different retained horizons.
    second.anchors[0] = first.anchors[0].clone();
    for a in &mut second.anchors {
        a.bridge.push(step.clone());
    }
    second.target_coverage = provider.coverage.root();
    second.target_summary = provider.summary.hash();
    let mut all = ops;
    all.push(tail);
    assert_eq!(verify(&second, &roster).unwrap().render(), oracle(&all));
}

#[test]
fn omission_forgery_wrong_scope_and_unpinned_signers_reject() {
    let ops = workload(15);
    let (keys, roster) = keys();
    let (good, _) = build(&ops, &[12, 14, 15], &keys);
    let reject = |s: &Snapshot| assert!(verify(s, &roster).is_err());
    let mut s = good.clone();
    s.anchors[0].bridge.pop();
    reject(&s);
    let mut s = good.clone();
    s.anchors[0].state.live.clear();
    reject(&s);
    let mut s = good.clone();
    s.anchors[0].signature[0] ^= 1;
    reject(&s);
    let mut s = good.clone();
    s.anchors[0].descriptor.scope = "other-drawing".into();
    reject(&s);
    let mut s = good.clone();
    s.anchors[1].descriptor.member = 0;
    reject(&s);
    let mut s = good.clone();
    s.anchors.pop();
    reject(&s);
    let mut s = good.clone();
    s.target_summary = [0; 32];
    reject(&s);
    let mut s = good.clone();
    s.target_coverage = [0; 32];
    reject(&s);
    let mut s = good.clone();
    s.anchors[0].bridge[0].op.value = "forged".into();
    reject(&s);
    assert!(verify(&good, &[]).is_err());
    let wrong: Vec<_> = (4..=6)
        .map(|i| SigningKey::from_bytes(&[i; 32]).verifying_key())
        .collect();
    assert!(verify(&good, &wrong).is_err());
}

#[test]
fn covered_duplicate_and_cross_key_replacement_match_kernel() {
    let a = operation("a", "red", false, &[], 1);
    let b = operation("b", "blue", false, std::slice::from_ref(&a.id), 2);
    let ops = vec![a.clone(), b];
    let (keys, roster) = keys();
    let (snapshot, mut provider) = build(&ops, &[2, 2, 2], &keys);
    let mut state = verify(&snapshot, &roster).unwrap();
    let mut root = snapshot.target_coverage;
    let duplicate = provider.apply(&a).unwrap();
    advance(&mut state, &mut root, &duplicate).unwrap();
    assert_eq!(state.render(), oracle(&ops));
    assert_eq!(state.live.len(), 2);
}

#[test]
fn witness_mutation_and_missing_replacement_evidence_reject() {
    let ops = workload(15);
    let (keys, roster) = keys();
    let (good, _) = build(&ops, &[12, 14, 15], &keys);
    let mut s = good.clone();
    s.anchors[0].bridge[0].identity.present ^= true;
    assert!(verify(&s, &roster).is_err());
    let mut s = good.clone();
    s.anchors[0].bridge[0].replacements.clear();
    assert!(verify(&s, &roster).is_err());
    let mut s = good.clone();
    let proof = &mut s.anchors[0].bridge[0].identity;
    proof.siblings.push((256, [1; 32]));
    assert!(verify(&s, &roster).is_err());
}

#[test]
fn evidence_cost_grows_with_member_lag_not_just_live_shapes() {
    let ops = workload(25);
    let (keys, _) = keys();
    let (near, _) = build(&ops, &[23, 24, 25], &keys);
    let (stale, _) = build(&ops, &[0, 24, 25], &keys);
    assert!(encoded(&stale).len() > encoded(&near).len() * 2);
}

#[test]
fn cross_key_arrival_order_converges_and_independent_anchors_reconcile() {
    let a = operation("a", "red", false, &[], 1);
    let b = operation("b", "blue", false, std::slice::from_ref(&a.id), 2);
    let (keys, roster) = keys();
    let mut forward = Replica::new();
    let mut reverse = Replica::new();
    for op in [&a, &b] {
        forward.apply(op).unwrap();
    }
    for op in [&b, &a] {
        reverse.apply(op).unwrap();
    }
    assert_eq!(forward.summary, reverse.summary);
    assert!(reverse.summary.pending.is_empty());
    let snapshot = Snapshot {
        target_coverage: forward.coverage.root(),
        target_summary: forward.summary.hash(),
        anchors: vec![
            anchor(&forward, 0, &keys[0]),
            anchor(&reverse, 1, &keys[1]),
            anchor(&forward, 2, &keys[2]),
        ],
    };
    assert_eq!(
        verify(&snapshot, &roster).unwrap().render(),
        oracle(&[a, b])
    );
}

#[test]
fn invalid_late_replacement_proof_is_atomic_and_valid_retry_succeeds() {
    let a = operation("x", "red", false, &[], 1);
    let b = operation("x", "blue", false, &[], 2);
    let c = operation("x", "green", false, &[a.id.clone(), b.id.clone()], 3);
    let mut provider = Replica::new();
    provider.apply(&a).unwrap();
    provider.apply(&b).unwrap();
    let mut state = provider.summary.clone();
    let before = state.clone();
    let mut root = provider.coverage.root();
    let old_root = root;
    let good = provider.apply(&c).unwrap();
    let mut bad = good.clone();
    bad.replacements[1].present = false;
    assert!(advance(&mut state, &mut root, &bad).is_err());
    assert_eq!(state, before);
    assert_eq!(root, old_root);
    advance(&mut state, &mut root, &good).unwrap();
    assert_eq!(state.render(), oracle(&[a, b, c]));
}

#[test]
fn canonical_witness_recognition_rejects_all_malformed_sibling_forms() {
    let mut coverage = Coverage::new();
    coverage.insert("one");
    coverage.insert("two");
    let good = coverage.proof("one");
    assert!(good.check(coverage.root(), "other").is_err());
    let mut p = good.clone();
    p.siblings.push(p.siblings[0]);
    assert!(p.check(coverage.root(), "one").is_err());
    let mut p = good.clone();
    let d = p.siblings[0].0;
    p.siblings[0].1 = defaults()[d + 1];
    assert!(p.check(coverage.root(), "one").is_err());
    let mut p = good.clone();
    p.siblings[0].1[0] ^= 1;
    assert!(p.check(coverage.root(), "one").is_err());
}

#[test]
fn honest_anchor_rejects_a_validly_signed_inconsistent_member() {
    let ops = workload(12);
    let (keys, roster) = keys();
    let (mut s, _) = build(&ops, &[12, 12, 12], &keys);
    s.anchors[1].state.live.clear();
    s.anchors[1].descriptor.summary = s.anchors[1].state.hash();
    s.anchors[1].signature = keys[1]
        .sign(&encoded(&s.anchors[1].descriptor))
        .to_bytes()
        .to_vec();
    assert!(verify(&s, &roster).is_err());
}

#[test]
fn identical_concurrent_values_still_require_distinct_live_identities() {
    let ops: Vec<_> = (0..20)
        .map(|i| operation("x", "red", false, &[], i))
        .collect();
    let mut r = Replica::new();
    for op in &ops {
        r.apply(op).unwrap();
    }
    assert_eq!(r.summary.live.len(), 20);
    assert_eq!(r.summary.render(), oracle(&ops[..1]));
    let erase = operation("x", "", true, std::slice::from_ref(&ops[0].id), 99);
    r.apply(&erase).unwrap();
    assert_eq!(r.summary.live.len(), 19);
}
