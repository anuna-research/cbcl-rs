use super::*;

fn members(f: &Fixture, lengths: [usize; 4]) -> Vec<Member> {
    lengths
        .into_iter()
        .enumerate()
        .map(|(i, n)| Member::new(i, f, &f.edits[..n]).unwrap())
        .collect()
}

#[test]
fn independent_members_endorse_only_the_same_accepted_cut() {
    let f = Fixture::new(40, 8, 24);
    let c = Config::new(&f);
    let ms = members(&f, [41, 41, 41, 17]);
    let (proposal, p) = ms[0].propose(&c).unwrap();
    let cert = certify(proposal.clone(), p.state.clone(), &ms, &c).unwrap();
    assert_eq!(cert.votes.len(), 3);
    assert!(ms[3].endorse(&proposal, &c, &f.keys[3]).is_err());
    let mut bad = proposal.clone();
    bad.summary = [0; 32];
    assert!(ms
        .iter()
        .all(|m| m.endorse(&bad, &c, &f.keys[m.index]).is_err()));
    let mut bad = proposal.clone();
    bad.coverage = [0; 32];
    assert!(ms[0].endorse(&bad, &c, &f.keys[0]).is_err());
    let mut bad = proposal;
    bad.frontier.push(f.root.id());
    assert!(ms[0].endorse(&bad, &c, &f.keys[0]).is_err());
    let split = members(&f, [41, 33, 25, 17]);
    let (m, p) = split[0].propose(&c).unwrap();
    assert!(certify(m, p.state, &split, &c).is_err());
}

#[test]
fn ahead_members_can_endorse_an_older_causally_closed_cut() {
    let f = Fixture::new(40, 8, 24);
    let c = Config::new(&f);
    let ms = members(&f, [41, 33, 25, 17]);
    let old = Member::new(0, &f, &f.edits[..17]).unwrap();
    let (m, p) = old.propose(&c).unwrap();
    let cert = certify(m, p.state, &ms, &c).unwrap();
    assert_eq!(cert.votes.len(), 4);
}

#[test]
fn filesystem_cache_rejects_corruption_and_falls_back_without_new_votes() {
    let f = Fixture::new(40, 8, 24);
    let c = Config::new(&f);
    let a = Archive::new(&f);
    let cache = Cache::new();
    let ms = members(&f, [41, 41, 41, 17]);
    let (m, p) = ms[0].propose(&c).unwrap();
    let cert = certify(m, p.state.clone(), &ms, &c).unwrap();
    let good = cache.publish(&cert).unwrap();
    let corrupt = cache
        .publish(&Certificate {
            votes: vec![],
            ..cert.clone()
        })
        .unwrap();
    fs::write(cache.path(corrupt), b"corrupt cache response").unwrap();
    let valid = offer(good, p, &[], &a, &c, None).unwrap();
    let bad = Offer {
        blob: corrupt,
        tail: vec![],
        floor_proofs: vec![],
    };
    let loaded = load(&cache, &[bad, valid], &c, None, None).unwrap();
    assert_eq!(loaded.blob, good);
    assert_eq!(loaded.rejected.len(), 1);
    assert_eq!(cache.reads.get(), 2);
    assert_eq!(loaded.client.state, cert.state);
}

#[test]
fn valid_content_address_does_not_authorize_a_forged_certificate() {
    let f = Fixture::new(24, 8, 8);
    let c = Config::new(&f);
    let a = Archive::new(&f);
    let cache = Cache::new();
    let ms = members(&f, [25, 25, 25, 17]);
    let (m, p) = ms[0].propose(&c).unwrap();
    let cert = certify(m, p.state.clone(), &ms, &c).unwrap();
    for mutate in 0..4 {
        let mut bad = cert.clone();
        match mutate {
            0 => bad.state.live.clear(),
            1 => bad.votes.pop().map(|_| ()).unwrap(),
            2 => bad.votes[1] = bad.votes[0].clone(),
            _ => bad.manifest.context = [0; 32],
        }
        let blob = cache.publish(&bad).unwrap();
        let response = offer(blob, p.clone(), &[], &a, &c, None).unwrap();
        assert!(load(&cache, &[response], &c, None, None).is_err());
    }
}

#[test]
fn stale_valid_snapshot_cannot_roll_back_a_local_floor() {
    let f = Fixture::new(40, 8, 24);
    let c = Config::new(&f);
    let a = Archive::new(&f);
    let cache = Cache::new();
    let ms = members(&f, [41, 41, 41, 17]);
    let (m, new_p) = ms[0].propose(&c).unwrap();
    let newest = certify(m, new_p.state.clone(), &ms, &c).unwrap();
    let floor = Floor::at(&newest);
    let old = Member::new(0, &f, &f.edits[..17]).unwrap();
    let (m, p) = old.propose(&c).unwrap();
    let cert = certify(m, p.state.clone(), &ms, &c).unwrap();
    let blob = cache.publish(&cert).unwrap();
    let response = offer(blob, p, &[], &a, &c, Some(&floor)).unwrap();
    assert!(load(&cache, &[response], &c, Some(&floor), None).is_err());
    // With no remembered floor, valid old state is acceptable, not provably newest.
    let mut response = offer(blob, new_p, &[], &a, &c, None).unwrap();
    response.tail.clear();
    assert!(load(&cache, &[response], &c, None, None).is_ok());
}

#[test]
fn missing_latest_blob_can_use_older_snapshot_and_authenticated_catchup() {
    let f = Fixture::new(40, 8, 24);
    let c = Config::new(&f);
    let a = Archive::new(&f);
    let cache = Cache::new();
    let ms = members(&f, [41, 41, 41, 17]);
    let (m, p) = ms[0].propose(&c).unwrap();
    let newest = certify(m, p.state, &ms, &c).unwrap();
    let floor = Floor::at(&newest);
    let missing = cache.publish(&newest).unwrap();
    fs::remove_file(cache.path(missing)).unwrap();
    let old = Member::new(0, &f, &f.edits[..17]).unwrap();
    let (m, p) = old.propose(&c).unwrap();
    let cert = certify(m, p.state.clone(), &ms, &c).unwrap();
    let blob = cache.publish(&cert).unwrap();
    let fallback = offer(blob, p, &f.edits[17..], &a, &c, Some(&floor)).unwrap();
    let loaded = load(
        &cache,
        &[
            Offer {
                blob: missing,
                tail: vec![],
                floor_proofs: vec![],
            },
            fallback,
        ],
        &c,
        Some(&floor),
        None,
    )
    .unwrap();
    assert_eq!(loaded.client.state, newest.state);
    assert_eq!(loaded.rejected.len(), 1);
}

#[test]
fn warm_rebase_keeps_a_local_edit_and_signed_evidence_or_refuses_installation() {
    let f = Fixture::new(40, 8, 24);
    let c = Config::new(&f);
    let a = Archive::new(&f);
    let cache = Cache::new();
    let ms = members(&f, [41, 41, 41, 17]);
    let (m, mut p) = ms[0].propose(&c).unwrap();
    let cert = certify(m, p.state.clone(), &ms, &c).unwrap();
    let blob = cache.publish(&cert).unwrap();
    let mut previous = cert.open(&c).unwrap();
    let mut floor = Floor::at(&cert);
    let wire = fixture::edit(
        "local",
        "{\"colour\":\"red\"}",
        false,
        &[],
        &f.edits[0].id(),
        10000,
        3,
        &f.keys,
    );
    let step = p
        .step(&wire, &a, &mut BTreeSet::new(), &f.root.id())
        .unwrap();
    assert_eq!(
        previous.admit(&step, &c).unwrap(),
        VerificationResult::Valid
    );
    floor.advance(&step, &previous);
    let before = previous.state.hash();
    let (_, base) = ms[0].propose(&c).unwrap();
    let missing_local = offer(blob, base.clone(), &[], &a, &c, Some(&floor)).unwrap();
    assert!(load(&cache, &[missing_local], &c, Some(&floor), Some(&previous)).is_err());
    assert_eq!(previous.state.hash(), before);
    let response = offer(
        blob,
        base,
        std::slice::from_ref(&wire),
        &a,
        &c,
        Some(&floor),
    )
    .unwrap();
    let loaded = load(&cache, &[response], &c, Some(&floor), Some(&previous)).unwrap();
    assert_eq!(loaded.client.state, previous.state);
    assert!(loaded.client.signed_bodies.contains_key(&wire.id()));
    let mut all = f.edits.clone();
    all.push(wire);
    let monitor = replay(&f, &all).unwrap();
    assert_eq!(
        render_state(&loaded.client.state, &f.dialect),
        folded(&f, &monitor, &all)
    );
}

#[test]
fn malformed_floor_and_advertisement_limits_fail_closed() {
    let f = Fixture::new(16, 8, 8);
    let c = Config::new(&f);
    let cache = Cache::new();
    assert!(load(&cache, &[], &c, None, None).is_err());
    let offers = vec![
        Offer {
            blob: [0; 32],
            tail: vec![],
            floor_proofs: vec![]
        };
        MAX_OFFERS + 1
    ];
    assert!(load(&cache, &offers, &c, None, None).is_err());
    assert_eq!(cache.reads.get(), 0);
}

#[test]
fn accepted_history_cannot_be_reused_under_a_different_dialect_context() {
    let a = Fixture::new(12, 16, 4);
    let b = Fixture::new(12, 8, 4);
    let ca = Config::new(&a);
    let cb = Config::new(&b);
    // Native root message IDs alone do not identify the governing dialect/cast.
    assert_eq!(a.root.id(), b.root.id());
    assert_ne!(ca.context, cb.context);
    let member = Member::new(0, &a, &a.edits).unwrap();
    let (mut proposal, p) = member.propose(&ca).unwrap();
    proposal.context = cb.context;
    assert!(member.endorse(&proposal, &cb, &b.keys[0]).is_err());
    let old = Client::new(
        p.state,
        &Cut {
            context: ca.context,
            coverage: p.coverage.root(),
            summary: proposal.summary,
        },
        &ca,
    )
    .unwrap();
    let cache = Cache::new();
    let floor = Floor {
        context: cb.context,
        coverage: old.coverage,
        frontier: proposal.frontier,
    };
    let offered = Offer {
        blob: [0; 32],
        tail: vec![],
        floor_proofs: vec![],
    };
    assert!(load(&cache, &[offered], &cb, Some(&floor), Some(&old)).is_err());
    assert_eq!(cache.reads.get(), 0);
}

#[test]
fn warm_rebase_retains_superseded_signed_bodies_without_resupplying_them() {
    let f = Fixture::new(40, 8, 24);
    let c = Config::new(&f);
    let archive = Archive::new(&f);
    let cache = Cache::new();
    let ms = members(&f, [41, 41, 41, 17]);
    let (m, new_p) = ms[0].propose(&c).unwrap();
    let newest = certify(m, new_p.state.clone(), &ms, &c).unwrap();
    let older = Member::new(0, &f, &f.edits[..17]).unwrap();
    let (m, mut p) = older.propose(&c).unwrap();
    let cert = certify(m, p.state.clone(), &ms, &c).unwrap();
    let mut previous = cert.open(&c).unwrap();
    for wire in [&f.edits[2], &f.edits[4]] {
        let step = p
            .step(wire, &archive, &mut BTreeSet::new(), &f.root.id())
            .unwrap();
        assert!(step.identity.present);
        assert_eq!(
            previous.admit(&step, &c).unwrap(),
            VerificationResult::Valid
        );
        assert!(!newest.state.live.contains_key(&wire.act().address));
    }
    let old_evidence: BTreeMap<_, _> = previous
        .signed_bodies
        .iter()
        .map(|(id, w)| (id.clone(), encoded(w)))
        .collect();
    let floor = Floor::at(&cert);
    let blob = cache.publish(&newest).unwrap();
    let response = offer(blob, new_p, &[], &archive, &c, Some(&floor)).unwrap();
    assert!(response.tail.is_empty());
    let loaded = load(&cache, &[response], &c, Some(&floor), Some(&previous)).unwrap();
    for (id, bytes) in old_evidence {
        assert_eq!(encoded(&loaded.client.signed_bodies[&id]), bytes);
    }
}

#[test]
fn concurrent_branch_floor_requires_both_branches_and_accepts_missing_branch_tail() {
    let mut f = Fixture::new(1, 8, 0);
    let open = f.edits[0].clone();
    let left = fixture::edit("left", "red", false, &[], &open.id(), 700, 0, &f.keys);
    let right = fixture::edit("right", "blue", false, &[], &open.id(), 701, 1, &f.keys);
    f.edits = vec![open, left.clone(), right.clone()];
    let c = Config::new(&f);
    let archive = Archive::new(&f);
    let cache = Cache::new();
    let ms = members(&f, [3, 3, 3, 3]);
    let (m, p) = ms[0].propose(&c).unwrap();
    let full = certify(m, p.state, &ms, &c).unwrap();
    assert_eq!(full.manifest.frontier.len(), 2);
    let floor = Floor::at(&full);
    let subset = Member::new(0, &f, &f.edits[..2]).unwrap();
    let (m, p) = subset.propose(&c).unwrap();
    let one = certify(m, p.state.clone(), &ms, &c).unwrap();
    let blob = cache.publish(&one).unwrap();
    let omission = offer(blob, p.clone(), &[], &archive, &c, Some(&floor)).unwrap();
    assert!(load(&cache, &[omission], &c, Some(&floor), None).is_err());
    let complete = offer(
        blob,
        p,
        std::slice::from_ref(&right),
        &archive,
        &c,
        Some(&floor),
    )
    .unwrap();
    let loaded = load(&cache, &[complete], &c, Some(&floor), None).unwrap();
    assert_eq!(loaded.client.state, full.state);
}

#[test]
fn excessive_tail_work_is_rejected_before_cache_read_and_allows_fallback() {
    let f = Fixture::new(16, 8, 8);
    let c = Config::new(&f);
    let archive = Archive::new(&f);
    let cache = Cache::new();
    let ms = members(&f, [17, 17, 17, 9]);
    let (m, mut p) = ms[0].propose(&c).unwrap();
    let cert = certify(m, p.state.clone(), &ms, &c).unwrap();
    let blob = cache.publish(&cert).unwrap();
    let duplicate = p
        .step(&f.edits[2], &archive, &mut BTreeSet::new(), &f.root.id())
        .unwrap();
    let excessive = Offer {
        blob,
        tail: vec![duplicate; MAX_TAIL_STEPS + 1],
        floor_proofs: vec![],
    };
    let good = offer(blob, p, &[], &archive, &c, None).unwrap();
    let loaded = load(&cache, &[excessive, good], &c, None, None).unwrap();
    assert_eq!(loaded.rejected.len(), 1);
    assert_eq!(cache.reads.get(), 1);
    let mut writer = ByteBudget {
        used: MAX_OFFER_BYTES,
    };
    assert!(writer.write(b"x").is_err());
}

#[test]
#[cfg(unix)]
fn special_files_and_symlinks_do_not_block_cache_fallback() {
    let f = Fixture::new(16, 8, 8);
    let c = Config::new(&f);
    let archive = Archive::new(&f);
    let cache = Cache::new();
    let ms = members(&f, [17, 17, 17, 9]);
    let (m, p) = ms[0].propose(&c).unwrap();
    let cert = certify(m, p.state.clone(), &ms, &c).unwrap();
    let blob = cache.publish(&cert).unwrap();
    let fifo = [1; 32];
    let link = [2; 32];
    assert!(std::process::Command::new("mkfifo")
        .arg(cache.path(fifo))
        .status()
        .unwrap()
        .success());
    std::os::unix::fs::symlink(cache.path(blob), cache.path(link)).unwrap();
    let good = offer(blob, p, &[], &archive, &c, None).unwrap();
    let loaded = load(
        &cache,
        &[
            Offer {
                blob: fifo,
                tail: vec![],
                floor_proofs: vec![],
            },
            Offer {
                blob: link,
                tail: vec![],
                floor_proofs: vec![],
            },
            good,
        ],
        &c,
        None,
        None,
    )
    .unwrap();
    assert_eq!(loaded.rejected.len(), 2);
    assert_eq!(loaded.blob, blob);
    // A symlink containing exactly the advertised bytes must still be rejected;
    // otherwise a content-address mismatch would mask the no-follow check.
    let backup = cache.dir.join("public-payload-backup");
    fs::rename(cache.path(blob), &backup).unwrap();
    std::os::unix::fs::symlink(&backup, cache.path(blob)).unwrap();
    assert!(cache.read(blob).is_err());
}

#[test]
fn serialized_byte_cap_is_independent_of_step_cap() {
    let f = Fixture::new(16, 8, 8);
    let c = Config::new(&f);
    let archive = Archive::new(&f);
    let cache = Cache::new();
    let ms = members(&f, [17, 17, 17, 9]);
    let (m, mut p) = ms[0].propose(&c).unwrap();
    let cert = certify(m, p.state.clone(), &ms, &c).unwrap();
    let blob = cache.publish(&cert).unwrap();
    let mut huge = p
        .step(&f.edits[2], &archive, &mut BTreeSet::new(), &f.root.id())
        .unwrap();
    huge.wire.message = Message::Meta {
        dialect_def: SExpr::Atom(Atom::Str("x".repeat(MAX_OFFER_BYTES + 1))),
    };
    let oversized = Offer {
        blob,
        tail: vec![huge],
        floor_proofs: vec![],
    };
    let good = offer(blob, p, &[], &archive, &c, None).unwrap();
    let loaded = load(&cache, &[oversized, good], &c, None, None).unwrap();
    assert_eq!(cache.reads.get(), 1);
    assert!(loaded.rejected[0].contains("offer byte budget"));
}

#[test]
fn cache_rejects_valid_certificate_bytes_under_wrong_content_address() {
    let f = Fixture::new(24, 8, 8);
    let c = Config::new(&f);
    let cache = Cache::new();
    let ms = members(&f, [25, 25, 25, 17]);
    let (m, p) = ms[0].propose(&c).unwrap();
    let newer = certify(m, p.state, &ms, &c).unwrap();
    let old = Member::new(0, &f, &f.edits[..17]).unwrap();
    let (m, p) = old.propose(&c).unwrap();
    let older = certify(m, p.state, &ms, &c).unwrap();
    older.open(&c).unwrap();
    newer.open(&c).unwrap();
    let advertised = cache.publish(&newer).unwrap();
    fs::write(cache.path(advertised), encoded(&older)).unwrap();
    assert!(cache.read(advertised).is_err());
}
