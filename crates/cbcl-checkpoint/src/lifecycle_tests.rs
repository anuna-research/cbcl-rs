use super::*;
use crate::{certificate::Certificate, host::*, member::Member, test_support::*};
use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
    time::{Duration, Instant},
};
fn dir() -> PathBuf {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let p = std::env::temp_dir().join(format!(
        "cbcl-checkpoint-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&p).unwrap();
    p
}
#[test]
fn native_certificate_roundtrip_threshold_scope_and_no_companion_history() {
    let f = Fixture::new();
    let members = f.members(&[]);
    let cert = f.certificate(&members);
    assert_eq!(cert.verify(&f.context, &f.keys).unwrap().len(), 3);
    let raw = cert.encode(&f.context);
    let decoded = Certificate::decode(&raw, &f.context).unwrap();
    assert_eq!(cert, decoded);
    let mut too_few = cert.clone();
    too_few.endorsements.pop();
    assert!(too_few.verify(&f.context, &f.keys).is_err());
    let mut duplicate = cert.clone();
    duplicate.endorsements[1] = duplicate.endorsements[0].clone();
    assert!(duplicate.verify(&f.context, &f.keys).is_err());
    let mut forged = cert.clone();
    forged.summary.push(0);
    assert!(forged.verify(&f.context, &f.keys).is_err());
    let mut foreign = f.context.clone();
    foreign.profile[0] ^= 1;
    assert!(cert.verify(&foreign, &f.keys).is_err());
    for wrong_thread in [false, true] {
        let mut wrong = cert.clone();
        for (i, e) in cert.endorsements.iter().enumerate() {
            let cbcl_core::message::Message::Wrapped { content, .. } = e.message() else {
                panic!("native endorsement wrapper")
            };
            let mut unsigned = content.as_ref().clone();
            let cbcl_core::message::Message::Dialect { inner, .. } = &mut unsigned else {
                panic!("native language")
            };
            let cbcl_core::message::Message::Simple { params, thread, .. } = inner.as_mut() else {
                panic!("native payload")
            };
            if wrong_thread {
                *thread = Some("foreign".into());
            } else {
                for pair in params.chunks_exact_mut(2) {
                    if pair[0]
                        == cbcl_core::sexpr::SExpr::Atom(cbcl_core::sexpr::Atom::Keyword(
                            "target".into(),
                        ))
                    {
                        pair[1] = cbcl_core::sexpr::SExpr::Atom(cbcl_core::sexpr::Atom::Str(
                            format!("f1220{}", "0".repeat(64)),
                        ));
                    }
                }
            }
            wrong.endorsements[i] =
                crate::certificate::SignedMessage::sign(unsigned, &format!("@m{i}"), &f.keys)
                    .unwrap();
        }
        assert!(
            wrong.verify(&f.context, &f.keys).is_err(),
            "valid signatures with wrong scope/thread must not count"
        );
    }
    for n in 0..raw.len() {
        assert!(Certificate::decode(&raw[..n], &f.context).is_err());
    }
    let mut extra = raw;
    extra.push(0);
    assert!(Certificate::decode(&extra, &f.context).is_err());
}
#[test]
fn cold_open_fallback_tail_floor_and_durable_restart() {
    let f = Fixture::new();
    let members = f.members(&[]);
    let cert = f.certificate(&members);
    let p = dir();
    let mut cache = Cache::open(p.join("cache")).unwrap();
    let blob = publish(&cache, &cert, &f.context, &f.keys, |_| Ok(())).unwrap();
    let mut member = Member::new(&f.context, "@m0", &f.keys).unwrap();
    member.accept(&f.target_open, &f.context, &f.keys).unwrap();
    let write = f.write("red", 1, &[], "@m0");
    let step = member.step(&write).unwrap();
    member.accept(&write, &f.context, &f.keys).unwrap();
    let missing = Offer {
        blob: [0; 32],
        tail: vec![],
        floor_proofs: vec![],
    };
    let offer = Offer {
        blob,
        tail: vec![step.clone()],
        floor_proofs: vec![],
    };
    let prepared = prepare_open(
        &mut cache,
        &[missing.encode(), offer.encode()],
        &f.context,
        &f.keys,
        None,
        0,
        Mode::Enabled,
        &Limits::default(),
    )
    .unwrap();
    assert_eq!(prepared.metrics().rejected.len(), 1);
    assert_eq!(
        prepared.client().summary.render_json(),
        member.client().summary.render_json()
    );
    assert_eq!(prepared.metrics().companion_history_reads, 0);
    let mut disk =
        DurableClient::create(p.join("client"), prepared.client().clone(), Mode::Enabled).unwrap();
    disk.enqueue("local-pending".into(), b"pending".to_vec())
        .unwrap();
    let floor = member.client().floor();
    let proofs = floor
        .frontier
        .iter()
        .map(|id| (id.clone(), member.coverage().proof(id)))
        .collect();
    let warm = Offer {
        blob,
        tail: vec![step],
        floor_proofs: proofs,
    };
    let prepared = disk
        .prepare(
            &mut cache,
            &[warm.encode()],
            &f.context,
            &f.keys,
            &Limits::default(),
        )
        .unwrap();
    disk.record_retry("pending".into(), 1).unwrap();
    assert_eq!(disk.install(prepared).unwrap_err(), Error::Concurrent);
    let old = disk.client().clone();
    drop(disk);
    let restored =
        DurableClient::recover(p.join("client"), &f.context, &f.keys, Mode::Enabled).unwrap();
    assert_eq!(restored.client(), &old);
    assert!(restored.outbox().contains_key("local-pending"));
    assert_eq!(restored.retries().get("pending"), Some(&1));
    drop(restored);
    fs::remove_dir_all(p).unwrap();
}
#[test]
fn cache_corruption_symlinks_and_runtime_modes_fail_closed() {
    let f = Fixture::new();
    let m = f.members(&[]);
    let cert = f.certificate(&m);
    let p = dir();
    let mut cache = Cache::open(p.join("cache")).unwrap();
    let blob = cache.put(&cert.encode(&f.context)).unwrap();
    let offer = Offer {
        blob,
        tail: vec![],
        floor_proofs: vec![],
    }
    .encode();
    assert_eq!(
        prepare_open(
            &mut cache,
            std::slice::from_ref(&offer),
            &f.context,
            &f.keys,
            None,
            0,
            Mode::Off,
            &Limits::default()
        )
        .unwrap_err(),
        Error::Disabled
    );
    struct WrongAddress(Vec<u8>);
    impl Provider for WrongAddress {
        fn get(&mut self, _: Hash, _: usize, _: Instant) -> Result<Vec<u8>> {
            Ok(self.0.clone())
        }
    }
    let valid_under_wrong_id = Offer {
        blob: [123; 32],
        tail: vec![],
        floor_proofs: vec![],
    }
    .encode();
    assert!(prepare_open(
        &mut WrongAddress(cert.encode(&f.context)),
        &[valid_under_wrong_id],
        &f.context,
        &f.keys,
        None,
        0,
        Mode::Enabled,
        &Limits::default()
    )
    .is_err());
    fs::write(cache.path(blob), b"wrong bytes").unwrap();
    assert!(prepare_open(
        &mut cache,
        std::slice::from_ref(&offer),
        &f.context,
        &f.keys,
        None,
        0,
        Mode::Enabled,
        &Limits::default()
    )
    .is_err());
    fs::remove_file(cache.path(blob)).unwrap();
    cache.put(&cert.encode(&f.context)).unwrap();
    #[cfg(unix)]
    {
        let backup = p.join("valid");
        fs::rename(cache.path(blob), &backup).unwrap();
        std::os::unix::fs::symlink(&backup, cache.path(blob)).unwrap();
        assert!(cache
            .get(
                blob,
                16 * 1024 * 1024,
                Instant::now() + Duration::from_secs(1)
            )
            .is_err());
    }
    fs::remove_dir_all(p).unwrap();
}
#[test]
fn publication_coalesces_and_never_clears_failed_lag() {
    let mut s = PublicationSchedule::default();
    let t = Instant::now();
    s.accepted(t);
    assert!(!s.begin(t, Mode::Enabled));
    assert!(s.begin(t + Duration::from_secs(1), Mode::Enabled));
    assert!(!s.begin(t + Duration::from_secs(2), Mode::Enabled));
    s.accepted(t);
    s.complete(1, false, t);
    assert_eq!(s.lag(), 2);
    assert!(s.begin(t + Duration::from_secs(1), Mode::Enabled));
    s.complete(1, true, t);
    assert_eq!(s.lag(), 1);
}
#[test]
fn offer_parser_enforces_lengths_and_cumulative_limits() {
    let f = Fixture::new();
    let m = f.members(&[]);
    let cert = f.certificate(&m);
    let p = dir();
    let mut cache = Cache::open(&p).unwrap();
    let blob = cache.put(&cert.encode(&f.context)).unwrap();
    let b = Offer {
        blob,
        tail: vec![],
        floor_proofs: vec![],
    }
    .encode();
    assert_eq!(Offer::decode(&b, &Limits::default()).unwrap().blob, blob);
    let byte_only = Limits {
        offer_bytes: b.len() - 1,
        ..Limits::default()
    };
    assert!(
        Offer::decode(&b, &byte_only).is_err(),
        "valid offer must be refused solely by byte cap"
    );
    let mut malformed = b.clone();
    malformed[32..36].copy_from_slice(&u32::MAX.to_be_bytes());
    assert!(Offer::decode(&malformed, &Limits::default()).is_err());
    let limits = Limits {
        total_bytes: 1,
        ..Limits::default()
    };
    assert_eq!(
        prepare_open(
            &mut cache,
            &[b],
            &f.context,
            &f.keys,
            None,
            0,
            Mode::Enabled,
            &limits
        )
        .unwrap_err(),
        Error::Budget
    );
    fs::remove_dir_all(p).unwrap();
}

#[test]
fn every_persistence_boundary_recovers_one_complete_generation_and_fences_writers() {
    for point in [
        PersistFault::BeforeWrite,
        PersistFault::AfterWrite,
        PersistFault::AfterSync,
        PersistFault::AfterRename,
        PersistFault::AfterDirectorySync,
    ] {
        let f = Fixture::new();
        let members = f.members(&[]);
        let cert = f.certificate(&members);
        let client = crate::member::Client::from_certificate(&f.context, &cert, &f.keys).unwrap();
        let p = dir();
        let mut durable = DurableClient::create(&p, client.clone(), Mode::Enabled).unwrap();
        assert!(
            DurableClient::recover(&p, &f.context, &f.keys, Mode::Enabled).is_err(),
            "second writer must be fenced"
        );
        durable.inject_failure(point);
        assert!(durable.record_retry("attempt".into(), 7).is_err());
        assert_eq!(durable.client(), &client);
        assert_eq!(durable.generation(), 0);
        assert!(
            durable.enqueue("must-not-write".into(), vec![]).is_err(),
            "ambiguous failures stop all subsequent writes"
        );
        drop(durable);
        let recovered = DurableClient::recover(&p, &f.context, &f.keys, Mode::Enabled).unwrap();
        assert_eq!(recovered.client(), &client);
        if matches!(
            point,
            PersistFault::AfterRename | PersistFault::AfterDirectorySync
        ) {
            assert_eq!(recovered.generation(), 1);
            assert_eq!(recovered.retries().get("attempt"), Some(&7));
        } else {
            assert_eq!(recovered.generation(), 0);
            assert!(!recovered.retries().contains_key("attempt"));
        }
        drop(recovered);
        fs::remove_dir_all(p).unwrap();
    }
}

#[test]
fn concurrent_evidence_outbox_retry_and_local_edits_all_invalidate_staged_installation() {
    let f = Fixture::new();
    let members = f.members(&[]);
    let cert = f.certificate(&members);
    let base = crate::member::Client::from_certificate(&f.context, &cert, &f.keys).unwrap();
    for kind in 0..4 {
        let p = dir();
        let mut cache = Cache::open(p.join("cache")).unwrap();
        let blob = cache.put(&cert.encode(&f.context)).unwrap();
        let floor_proofs = base
            .frontier
            .iter()
            .map(|id| (id.clone(), members[0].coverage().proof(id)))
            .collect();
        let offer = Offer {
            blob,
            tail: vec![],
            floor_proofs,
        };
        let mut disk =
            DurableClient::create(p.join("client"), base.clone(), Mode::Enabled).unwrap();
        let prepared = disk
            .prepare(
                &mut cache,
                &[offer.encode()],
                &f.context,
                &f.keys,
                &Limits::default(),
            )
            .unwrap();
        match kind {
            0 => disk.enqueue("queued".into(), b"pending".to_vec()).unwrap(),
            1 => disk.record_retry("queued".into(), 2).unwrap(),
            2 => disk
                .retain_evidence(f.target_open.clone(), &f.keys)
                .unwrap(),
            _ => {
                let m = f.write("local", 1, &[], "@m1");
                let step = members[0].step(&m).unwrap();
                disk.admit(&step, &f.context, &f.keys).unwrap();
            }
        }
        let current = disk.client().clone();
        assert_eq!(disk.install(prepared).unwrap_err(), Error::Concurrent);
        assert_eq!(disk.client(), &current);
        drop(disk);
        let restored =
            DurableClient::recover(p.join("client"), &f.context, &f.keys, Mode::Enabled).unwrap();
        assert_eq!(restored.client(), &current);
        drop(restored);
        fs::remove_dir_all(p).unwrap();
    }
}

#[test]
fn shadow_requires_independent_replay_and_does_not_install() {
    let f = Fixture::new();
    let members = f.members(&[]);
    let cert = f.certificate(&members);
    let p = dir();
    let mut cache = Cache::open(p.join("cache")).unwrap();
    let blob = cache.put(&cert.encode(&f.context)).unwrap();
    let base = crate::member::Client::from_certificate(&f.context, &cert, &f.keys).unwrap();
    let proof = base
        .frontier
        .iter()
        .map(|id| (id.clone(), members[0].coverage().proof(id)))
        .collect();
    let offer = Offer {
        blob,
        tail: vec![],
        floor_proofs: proof,
    };
    let mut disk = DurableClient::create(p.join("client"), base.clone(), Mode::Shadow).unwrap();
    let mut prepared = disk
        .prepare(
            &mut cache,
            &[offer.encode()],
            &f.context,
            &f.keys,
            &Limits::default(),
        )
        .unwrap();
    assert!(disk.install(prepared.clone()).is_err());
    assert!(compare_shadow(&mut prepared, &[], &f.context, &f.keys).is_err());
    compare_shadow(
        &mut prepared,
        std::slice::from_ref(&f.target_open),
        &f.context,
        &f.keys,
    )
    .unwrap();
    disk.install(prepared).unwrap();
    assert_eq!(disk.generation(), 0);
    assert_eq!(disk.client(), &base);
    disk.set_mode(Mode::Off);
    assert_eq!(disk.mode(), Mode::Off);
    assert_eq!(disk.client(), &base);
    drop(disk);
    fs::remove_dir_all(p).unwrap();
}

#[test]
fn managed_key_custody_rejects_generic_endorsement_signing() {
    let managed = crate::certificate::ManagedSigner::new(Keys);
    let unsigned = parse("(lang checkpoint (endorse @m0 :sender @m0 :thread \"t\"))");
    assert!(managed.sign_native(unsigned, "@m0").is_err());
}

#[test]
fn prepared_install_cannot_substitute_another_stores_floor_or_evidence_snapshot() {
    let f = Fixture::new();
    let members = f.members(&[]);
    let cert = f.certificate(&members);
    let base = crate::member::Client::from_certificate(&f.context, &cert, &f.keys).unwrap();
    let p = dir();
    let mut cache = Cache::open(p.join("cache")).unwrap();
    let blob = cache.put(&cert.encode(&f.context)).unwrap();
    let floor_proofs = base
        .frontier
        .iter()
        .map(|id| (id.clone(), members[0].coverage().proof(id)))
        .collect();
    let offer = Offer {
        blob,
        tail: vec![],
        floor_proofs,
    };
    let mut a = DurableClient::create(p.join("a"), base.clone(), Mode::Enabled).unwrap();
    let mut b = DurableClient::create(p.join("b"), base.clone(), Mode::Enabled).unwrap();
    a.record_retry("queued".into(), 1).unwrap();
    let receipt = f.write("held-evidence", 1, &[], "@m1");
    b.retain_evidence(receipt, &f.keys).unwrap();
    assert_eq!(a.generation(), b.generation());
    assert_eq!(a.client().floor(), b.client().floor());
    let staged = a
        .prepare(
            &mut cache,
            &[offer.encode()],
            &f.context,
            &f.keys,
            &Limits::default(),
        )
        .unwrap();
    let before = b.client().clone();
    assert!(b.install(staged).is_err());
    assert_eq!(b.client(), &before);
    let stale_public = prepare_open(
        &mut cache,
        &[offer.encode()],
        &f.context,
        &f.keys,
        Some(&base),
        b.generation(),
        Mode::Enabled,
        &Limits::default(),
    )
    .unwrap();
    assert!(b.install(stale_public).is_err());
    assert_eq!(b.client(), &before);
    drop((a, b));
    fs::remove_dir_all(p).unwrap();
}

#[test]
fn failed_fetches_consume_their_allowance_and_orphan_temporary_files_do_not_block_recovery() {
    use std::sync::atomic::AtomicUsize;
    use std::sync::Arc;
    struct Failed {
        calls: Arc<AtomicUsize>,
    }
    impl Provider for Failed {
        fn get(&mut self, _: Hash, _: usize, _: Instant) -> Result<Vec<u8>> {
            self.calls.fetch_add(1, Ordering::Relaxed);
            Err(Error::Invalid("corrupt partial download"))
        }
    }
    let f = Fixture::new();
    let members = f.members(&[]);
    let cert = f.certificate(&members);
    let raw = Offer {
        blob: [1; 32],
        tail: vec![],
        floor_proofs: vec![],
    }
    .encode();
    let calls = Arc::new(AtomicUsize::new(0));
    let limits = Limits {
        certificate_bytes: 512,
        total_bytes: 900,
        ..Limits::default()
    };
    assert_eq!(
        prepare_open(
            &mut Failed {
                calls: calls.clone()
            },
            &[raw.clone(), raw.clone(), raw],
            &f.context,
            &f.keys,
            None,
            0,
            Mode::Enabled,
            &limits
        )
        .unwrap_err(),
        Error::Budget
    );
    assert_eq!(calls.load(Ordering::Relaxed), 2);
    let p = dir();
    let base = crate::member::Client::from_certificate(&f.context, &cert, &f.keys).unwrap();
    let store = DurableClient::create(&p, base, Mode::Enabled).unwrap();
    drop(store);
    fs::write(p.join("generation.pending-0"), b"orphan").unwrap();
    let mut store = DurableClient::recover(&p, &f.context, &f.keys, Mode::Enabled).unwrap();
    store.record_retry("after-crash".into(), 1).unwrap();
    drop(store);
    fs::remove_dir_all(p).unwrap();
}

#[test]
fn bounded_validation_returns_during_stalled_fetch_or_signature_checks() {
    use std::sync::Arc;
    let f = Fixture::new();
    let members = f.members(&[]);
    let cert = f.certificate(&members);
    let blob = cert.blob_id(&f.context);
    let offer = Offer {
        blob,
        tail: vec![],
        floor_proofs: vec![],
    }
    .encode();
    struct Delayed {
        bytes: Vec<u8>,
        pause: bool,
    }
    impl Provider for Delayed {
        fn get(&mut self, _: Hash, _: usize, _: Instant) -> Result<Vec<u8>> {
            if self.pause {
                std::thread::sleep(Duration::from_millis(150));
            }
            Ok(self.bytes.clone())
        }
    }
    struct SlowCrypto;
    impl crate::certificate::KeyVerifier for SlowCrypto {
        fn verify(&self, key: &str, p: &[u8], s: &[u8]) -> bool {
            std::thread::sleep(Duration::from_millis(150));
            crate::certificate::KeyVerifier::verify(&Keys, key, p, s)
        }
    }
    for slow_crypto in [false, true] {
        let keys: Arc<dyn crate::certificate::KeyVerifier + Send + Sync> = if slow_crypto {
            Arc::new(SlowCrypto)
        } else {
            Arc::new(Keys)
        };
        let limits = Limits {
            timeout: Duration::from_millis(20),
            ..Limits::default()
        };
        let start = Instant::now();
        let result = prepare_open_bounded(
            Box::new(Delayed {
                bytes: cert.encode(&f.context),
                pause: !slow_crypto,
            }),
            vec![offer.clone()],
            Arc::new(f.context.clone()),
            keys,
            None,
            0,
            Mode::Enabled,
            limits,
        );
        assert!(matches!(result, Err(Error::Cancelled) | Err(Error::Budget)));
        assert!(start.elapsed() < Duration::from_millis(120));
    }
}

#[test]
fn stalled_commit_returns_uncertain_handle_and_keeps_exclusive_writer_fenced() {
    let f = Fixture::new();
    let members = f.members(&[]);
    let cert = f.certificate(&members);
    let base = crate::member::Client::from_certificate(&f.context, &cert, &f.keys).unwrap();
    let p = dir();
    let mut cache = Cache::open(p.join("cache")).unwrap();
    let blob = cache.put(&cert.encode(&f.context)).unwrap();
    let proofs = base
        .frontier
        .iter()
        .map(|id| (id.clone(), members[0].coverage().proof(id)))
        .collect();
    let offer = Offer {
        blob,
        tail: vec![],
        floor_proofs: proofs,
    };
    let mut disk = DurableClient::create(p.join("client"), base.clone(), Mode::Enabled).unwrap();
    let prepared = disk
        .prepare(
            &mut cache,
            &[offer.encode()],
            &f.context,
            &f.keys,
            &Limits::default(),
        )
        .unwrap();
    disk.inject_failure(PersistFault::Pause(Duration::from_millis(100)));
    let pending = crate::runtime::start_install(disk, prepared).unwrap();
    let crate::runtime::CommitOutcome::Uncertain(pending) = pending.wait(Duration::from_millis(10))
    else {
        panic!("stalled commit must return uncertainty, never false rollback")
    };
    assert_eq!(pending.previous(), &base);
    assert!(DurableClient::recover(p.join("client"), &f.context, &f.keys, Mode::Enabled).is_err());
    match pending.wait(Duration::from_secs(2)) {
        crate::runtime::CommitOutcome::Complete { store, result } => {
            result.unwrap();
            assert_eq!(store.generation(), 1);
            drop(store)
        }
        _ => panic!("commit completion must become observable"),
    };
    fs::remove_dir_all(p).unwrap();
}

#[test]
fn same_companion_dialect_serves_distinct_target_dialects_and_profiles() {
    let drawing = Fixture::new();
    let checklist = Fixture::with_target(installed(
        r#"(define checklist-checkpoint (cbcl) @anuna
      (:roles ((* member)))
      (extend open (to title) :from member :to member (tell to :title title))
      (extend check (to item done) :from member :to member (tell to :item item :done done))
      (shape open (require :title string)) (shape check (require :item string) (require :done bool))
      (protocol (then begin open) (then open check))
      (state (title (initial open :title)) (items (multi-value-map check :item :done))))"#,
    ));
    assert_ne!(drawing.context.hash(), checklist.context.hash());
    assert_ne!(drawing.context.profile(), checklist.context.profile());
    let a = drawing.certificate(&drawing.members(&[]));
    let b = checklist.certificate(&checklist.members(&[]));
    a.verify(&drawing.context, &drawing.keys).unwrap();
    b.verify(&checklist.context, &checklist.keys).unwrap();
    assert!(a.verify(&checklist.context, &checklist.keys).is_err());
    assert!(b.verify(&drawing.context, &drawing.keys).is_err());
    assert_eq!(
        drawing.context.companion_root().message(),
        checklist.context.companion_root().message()
    );
}

#[test]
fn unknown_profile_can_have_verified_attestations_but_cannot_install_state() {
    use crate::certificate::{Context, SignedMessage};
    use cbcl_core::{
        message::Message,
        sexpr::{Atom, SExpr},
    };
    let f = Fixture::new();
    let known = f.certificate(&f.members(&[]));
    let c = Context::new(
        f.context.target().clone(),
        f.context.target_root().clone(),
        f.context.companion_root().clone(),
        f.context.policy().clone(),
        [99; 32],
        &f.keys,
    )
    .unwrap();
    let manifest = c
        .manifest(
            known.manifest.coverage,
            known.manifest.summary,
            known.manifest.frontier.clone(),
        )
        .unwrap();
    let rescope = |m: &SignedMessage, key: &str, parent: Option<&str>| {
        let Message::Wrapped { content, .. } = m.message() else {
            panic!("signed")
        };
        let mut unsigned = content.as_ref().clone();
        let Message::Dialect { inner, .. } = &mut unsigned else {
            panic!("language")
        };
        let Message::Simple {
            params, caused_by, ..
        } = inner.as_mut()
        else {
            panic!("simple")
        };
        for p in params.chunks_exact_mut(2) {
            if let SExpr::Atom(Atom::Keyword(k)) = &p[0] {
                let replacement = match k.as_str() {
                    "context" => Some(hex(&c.hash())),
                    "profile" => Some(hex(&c.profile())),
                    "manifest" if parent.is_some() => Some(hex(&manifest.hash())),
                    _ => None,
                };
                if let Some(v) = replacement {
                    p[1] = SExpr::Atom(Atom::Str(v));
                }
            }
        }
        if let Some(parent) = parent {
            *caused_by = Some(cbcl_core::message::CausedBy::Single(parent.into()));
        }
        SignedMessage::sign(unsigned, key, &f.keys).unwrap()
    };
    let opener = rescope(&known.opener, "@init", None);
    let opener_id = opener.id().unwrap();
    let cert = Certificate {
        manifest: manifest.clone(),
        summary: known.summary,
        opener,
        endorsements: known
            .endorsements
            .iter()
            .enumerate()
            .map(|(i, m)| rescope(m, &format!("@m{i}"), Some(opener_id.as_str())))
            .collect(),
    };
    assert_eq!(cert.verify(&c, &f.keys).unwrap().len(), 3);
    assert_eq!(
        crate::member::Client::from_certificate(&c, &cert, &f.keys).unwrap_err(),
        Error::Unsupported
    );
    assert!(Member::new(&c, "@m0", &f.keys).is_err());
}

#[test]
fn disabling_preserves_state_and_reports_missing_replay_archive_without_publication() {
    let f = Fixture::new();
    let members = f.members(&[]);
    let cert = f.certificate(&members);
    let base = crate::member::Client::from_certificate(&f.context, &cert, &f.keys).unwrap();
    let p = dir();
    let cache = Cache::open(p.join("cache")).unwrap();
    let mut disk = DurableClient::create(p.join("client"), base.clone(), Mode::Off).unwrap();
    assert!(
        matches!(disk.replay_retained(&f.context,&f.keys),Err(Error::Missing(ids))if ids.contains(&f.target_open.id().unwrap()))
    );
    assert_eq!(disk.client(), &base);
    let mut advertised = false;
    assert_eq!(
        disk.publish(&cache, &cert, &f.context, &f.keys, |_| {
            advertised = true;
            Ok(())
        })
        .unwrap_err(),
        Error::Disabled
    );
    assert!(!advertised);
    disk.set_mode(Mode::Shadow);
    assert_eq!(
        disk.publish(&cache, &cert, &f.context, &f.keys, |_| Ok(()))
            .unwrap_err(),
        Error::Disabled
    );
    disk.retain_evidence(f.target_open.clone(), &f.keys)
        .unwrap();
    let before = disk.client().clone();
    let generation = disk.generation();
    assert_eq!(
        disk.replay_retained(&f.context, &f.keys).unwrap(),
        before.summary.render()
    );
    assert_eq!(disk.generation(), generation);
    assert_eq!(disk.client(), &before);
    drop(disk);
    fs::remove_dir_all(p).unwrap();
}

#[test]
fn caller_target_coverage_is_proved_explicitly_and_never_promoted_from_hints() {
    let f = Fixture::new();
    let members = f.members(&[]);
    let cert = f.certificate(&members);
    let p = dir();
    let mut cache = Cache::open(&p).unwrap();
    let blob = cache.put(&cert.encode(&f.context)).unwrap();
    let offer = Offer {
        blob,
        tail: vec![],
        floor_proofs: vec![],
    };
    let mut prepared = prepare_open(
        &mut cache,
        &[offer.encode()],
        &f.context,
        &f.keys,
        None,
        0,
        Mode::Enabled,
        &Limits::default(),
    )
    .unwrap();
    assert!(prepared.requested_target().is_none());
    let unknown = format!("f1220{}", "0".repeat(64));
    let absent = members[0].coverage().proof(&unknown);
    assert!(prepared
        .verify_requested_target(std::slice::from_ref(&unknown), &[(unknown.clone(), absent)])
        .is_err());
    assert!(!prepared.metrics().requested_target_covered);
    let id = f.target_open.id().unwrap();
    let proof = members[0].coverage().proof(&id);
    prepared
        .verify_requested_target(std::slice::from_ref(&id), &[(id.clone(), proof)])
        .unwrap();
    assert_eq!(prepared.requested_target(), Some(std::slice::from_ref(&id)));
    assert!(prepared.metrics().requested_target_covered);
    fs::remove_dir_all(p).unwrap();
}

#[test]
fn structured_observations_order_floor_durability_and_commit_without_payloads() {
    use std::sync::{Arc, Mutex};
    use tracing::{
        span::{Attributes, Id, Record},
        Event, Metadata, Subscriber,
    };
    #[derive(Clone, Debug, Default)]
    struct Seen {
        message: String,
        instance: String,
        generation: Option<u64>,
    }
    impl tracing::field::Visit for Seen {
        fn record_u64(&mut self, field: &tracing::field::Field, value: u64) {
            if field.name() == "generation" {
                self.generation = Some(value)
            }
        }
        fn record_debug(&mut self, field: &tracing::field::Field, value: &dyn std::fmt::Debug) {
            match field.name() {
                "message" => self.message = format!("{value:?}"),
                "instance" => self.instance = format!("{value:?}"),
                _ => {}
            }
        }
    }
    #[derive(Clone)]
    struct Capture(Arc<Mutex<Vec<Seen>>>, std::thread::ThreadId);
    impl Subscriber for Capture {
        fn enabled(&self, _: &Metadata<'_>) -> bool {
            true
        }
        fn new_span(&self, _: &Attributes<'_>) -> Id {
            Id::from_u64(1)
        }
        fn record(&self, _: &Id, _: &Record<'_>) {}
        fn record_follows_from(&self, _: &Id, _: &Id) {}
        fn event(&self, e: &Event<'_>) {
            if std::thread::current().id() != self.1 {
                return;
            }
            let mut event = Seen::default();
            e.record(&mut event);
            self.0.lock().unwrap().push(event);
        }
        fn enter(&self, _: &Id) {}
        fn exit(&self, _: &Id) {}
    }
    let events = Arc::new(Mutex::new(Vec::new()));
    let captured = Capture(events.clone(), std::thread::current().id());
    tracing::subscriber::set_global_default(captured.clone()).unwrap();
    tracing::subscriber::with_default(captured, || {
        let f = Fixture::new();
        let members = f.members(&[]);
        let cert = f.certificate(&members);
        let p = dir();
        let mut cache = Cache::open(p.join("cache")).unwrap();
        let blob = cache.put(&cert.encode(&f.context)).unwrap();
        let base = crate::member::Client::from_certificate(&f.context, &cert, &f.keys).unwrap();
        let mut store = DurableClient::create(p.join("client"), base, Mode::Enabled).unwrap();
        let floor_proofs = store
            .client()
            .frontier
            .iter()
            .map(|id| (id.clone(), members[0].coverage().proof(id)))
            .collect();
        let offer = Offer {
            blob,
            tail: vec![],
            floor_proofs,
        };
        let prepared = store
            .prepare(
                &mut cache,
                &[offer.encode()],
                &f.context,
                &f.keys,
                &Limits::default(),
            )
            .unwrap();
        store.install(prepared).unwrap();
        drop(store);
        fs::remove_dir_all(p).unwrap();
    });
    let events = events.lock().unwrap();
    let commit = events
        .iter()
        .position(|e| e.message == "checkpoint_install_committed")
        .expect("commit exported");
    let g = events[commit].generation;
    let instance = &events[commit].instance;
    assert!(!instance.is_empty());
    let floor = events[..commit]
        .iter()
        .position(|e| {
            e.message == "checkpoint_store_floor_checked"
                && e.generation == g
                && &e.instance == instance
        })
        .unwrap_or_else(|| panic!("matching store floor checked: {events:?}"));
    let durable = events[..commit]
        .iter()
        .position(|e| {
            e.message == "checkpoint_durable_generation"
                && e.generation == g
                && &e.instance == instance
        })
        .expect("matching generation durable");
    assert!(floor < durable && durable < commit);
    assert!(!format!("{events:?}").contains("signature"));
    assert!(!format!("{events:?}").contains("Drawing"));
}
