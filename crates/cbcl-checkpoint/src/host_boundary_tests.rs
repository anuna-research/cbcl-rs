//! Public-API regressions for archive durability and generation framing.
use crate::{
    host::{Cache, DurableClient, Mode},
    member::Client,
    test_support::Fixture,
    Error,
};
use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

struct TestDir(PathBuf);
impl TestDir {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "cbcl-host-boundary-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
}
impl Drop for TestDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn client(f: &Fixture) -> Client {
    let members = f.members(&[]);
    Client::from_certificate(&f.context, &f.certificate(&members), &f.keys).unwrap()
}

#[test]
fn large_installed_snapshots_and_pending_old_view_share_storage_and_stay_immutable() {
    use crate::host::{Limits, Offer};
    use crate::runtime::{start_install, CommitOutcome};
    use std::{sync::Arc, time::Duration};
    let f = Fixture::new();
    // Real, independently admitted concurrent contributions: both the summary
    // and frontier are substantial, rather than padding an unrelated allocation.
    let history: Vec<_> = (0..64)
        .map(|i| f.write(&format!("{i:02}{}", "x".repeat(2046)), i + 1, &[], "@m0"))
        .collect();
    let members = f.members(&history);
    let cert = f.certificate(&members);
    assert!(cert.summary.len() > 256 * 1024);
    let dir = TestDir::new();
    let mut store = DurableClient::create(
        dir.0.join("store"),
        client_from_cert(&f, &cert),
        Mode::Enabled,
    )
    .unwrap();
    let old = store.snapshot();
    let second = store.snapshot();
    assert!(Arc::ptr_eq(&old, &second));
    assert!(std::ptr::eq(store.client(), old.as_ref()));
    assert_eq!(old.frontier.len(), 64);
    let old_render = old.summary.render();
    let old_frontier = old.frontier.clone();
    let mut cache = Cache::open(dir.0.join("cache")).unwrap();
    let blob = cache.put(&cert.encode(&f.context)).unwrap();
    let offer = Offer {
        blob,
        tail: vec![],
        floor_proofs: old
            .frontier
            .iter()
            .map(|id| (id.clone(), members[0].coverage().proof(id)))
            .collect(),
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
    let pending = start_install(store, prepared).unwrap();
    // This checks the actual commit API's retained view, not just Arc::clone.
    assert!(std::ptr::eq(pending.previous(), old.as_ref()));
    let CommitOutcome::Complete {
        store: complete,
        result,
    } = pending.wait(Duration::from_secs(30))
    else {
        panic!("local commit must complete");
    };
    result.unwrap();
    store = *complete;
    assert!(!Arc::ptr_eq(&old, &store.snapshot()));
    let before_admit = store.snapshot();
    let message = f.write("new live state", 100, &[], "@m0");
    let step = members[0].step(&message).unwrap();
    store.admit(&step, &f.context, &f.keys).unwrap();
    assert!(!Arc::ptr_eq(&before_admit, &store.snapshot()));
    assert_eq!(old.summary.render(), old_render);
    assert_eq!(old.frontier, old_frontier);
    assert_eq!(before_admit.summary.render(), old_render);
    assert_ne!(store.client().summary.render(), old_render);
    let before_evidence = store.snapshot();
    let evidence = f.write("retained only", 101, &[], "@m1");
    let evidence_key = (
        evidence.id().unwrap(),
        crate::hash(b"cbcl/checkpoint/evidence/v1", &evidence.encode()),
    );
    store.retain_evidence(evidence.clone(), &f.keys).unwrap();
    assert!(before_evidence.evidence.get(&evidence_key).is_none());
    assert_eq!(store.client().evidence.get(&evidence_key), Some(&evidence));
}

fn client_from_cert(f: &Fixture, cert: &crate::certificate::Certificate) -> Client {
    Client::from_certificate(&f.context, cert, &f.keys).unwrap()
}

#[test]
fn selected_blob_link_fault_is_one_shot_and_cache_local() {
    let dir = TestDir::new();
    let a = Cache::open(dir.0.join("a")).unwrap();
    let b = Cache::open(dir.0.join("b")).unwrap();
    let bytes = b"selected post-link fault";
    let id = crate::hash(b"cbcl/checkpoint/blob/v1", bytes);
    a.fail_after_link_for(id);
    // Other blobs and other cache instances must not consume or trigger it.
    a.put(b"unrelated blob").unwrap();
    assert_eq!(b.put(bytes).unwrap(), id);
    let clone = a.clone();
    assert!(matches!(clone.put(bytes), Err(Error::Io(_))));
    assert_eq!(a.read_once(id, bytes.len()).unwrap(), bytes);
    fs::remove_file(a.path(id)).unwrap();
    // Relink, rather than take the existing-entry branch, to prove one-shot use.
    assert_eq!(a.put(bytes).unwrap(), id);
}

#[test]
fn final_evidence_root_link_fault_cannot_acknowledge_an_unsynced_generation() {
    let f = Fixture::new();
    let dir = TestDir::new();
    let store_path = dir.0.join("store");
    let base = client(&f);
    let message = f.write("new retained evidence", 1, &[], "@m1");
    let key = (
        message.id().unwrap(),
        crate::hash(b"cbcl/checkpoint/evidence/v1", &message.encode()),
    );
    let mut expected = base.evidence.clone();
    expected.insert(key.clone(), message.clone());
    let scratch = Cache::open(dir.0.join("scratch")).unwrap();
    let root = expected.persist(&scratch).unwrap().unwrap();
    let mut store = DurableClient::create(&store_path, base, Mode::Enabled).unwrap();
    let generation = store.generation();
    let previous = fs::read(store_path.join("generation")).unwrap();
    let root_path = store.archive_for_test().path(root);
    assert!(!root_path.exists());
    store.archive_for_test().fail_after_link_for(root);
    assert_eq!(
        store.retain_evidence(message.clone(), &f.keys),
        Err(Error::Io("injected archive post-link failure".into()))
    );
    assert!(
        root_path.is_file(),
        "the failure must leave the final root visible"
    );
    assert_eq!(
        fs::read(&root_path).unwrap(),
        scratch.read_once(root, 1024).unwrap()
    );
    assert_eq!(store.generation(), generation);
    assert_eq!(fs::read(store_path.join("generation")).unwrap(), previous);
    assert!(store.client().evidence.get(&key).is_none());
    assert!(store.record_retry("fail-stopped".into(), 1).is_err());
    drop(store);

    // Restart sees the old generation, but the failed attempt's root still exists.
    let mut recovered =
        DurableClient::recover(&store_path, &f.context, &f.keys, Mode::Enabled).unwrap();
    assert_eq!(recovered.generation(), generation);
    assert!(recovered.client().evidence.get(&key).is_none());
    recovered.archive_for_test().fail_next_directory_sync();
    assert_eq!(
        recovered.retain_evidence(message.clone(), &f.keys),
        Err(Error::Io("injected archive directory sync failure".into()))
    );
    let work = recovered.last_persist_work();
    assert_eq!(work.trusted_checks, 1, "retry must reuse the visible root");
    assert_eq!(work.new_nodes + work.value_encodes, 0);
    assert_eq!(recovered.generation(), generation);
    assert_eq!(fs::read(store_path.join("generation")).unwrap(), previous);
    assert!(recovered.record_retry("still-fenced".into(), 2).is_err());
    drop(recovered);

    // Model power loss discarding the uncommitted directory entry. No acknowledged
    // generation may depend on it; the old generation must remain recoverable.
    fs::remove_file(&root_path).unwrap();
    let mut recovered =
        DurableClient::recover(&store_path, &f.context, &f.keys, Mode::Enabled).unwrap();
    assert_eq!(recovered.generation(), generation);
    assert!(recovered.client().evidence.get(&key).is_none());
    recovered.retain_evidence(message.clone(), &f.keys).unwrap();
    assert_eq!(recovered.generation(), generation + 1);
    assert!(root_path.is_file());
    let frame = fs::read(store_path.join("generation")).unwrap();
    let record: serde_json::Value = serde_json::from_slice(&frame[32..]).unwrap();
    assert_eq!(record["evidence_root"], serde_json::to_value(root).unwrap());
    drop(recovered);
    let recovered =
        DurableClient::recover(&store_path, &f.context, &f.keys, Mode::Enabled).unwrap();
    assert_eq!(recovered.generation(), generation + 1);
    assert_eq!(recovered.client().evidence.get(&key), Some(&message));
}

#[cfg(unix)]
struct RestorePermissions {
    path: PathBuf,
    permissions: fs::Permissions,
}
#[cfg(unix)]
impl RestorePermissions {
    fn search_only(path: PathBuf) -> Self {
        use std::os::unix::fs::PermissionsExt;
        let permissions = fs::metadata(&path).unwrap().permissions();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o111)).unwrap();
        Self { path, permissions }
    }
    fn enforced(&self) -> bool {
        match fs::File::open(&self.path) {
            Err(e) if e.kind() == std::io::ErrorKind::PermissionDenied => true,
            Ok(_) => {
                eprintln!("directory permission fault unavailable for this effective user");
                false
            }
            Err(e) => panic!("unexpected directory-open failure: {e}"),
        }
    }
}
#[cfg(unix)]
impl Drop for RestorePermissions {
    fn drop(&mut self) {
        fs::set_permissions(&self.path, self.permissions.clone()).unwrap();
    }
}

#[cfg(unix)]
#[test]
fn existing_cache_put_must_retry_directory_durability() {
    let dir = TestDir::new();
    let cache = Cache::open(dir.0.join("cache")).unwrap();
    let bytes = b"already linked immutable blob";
    let id = cache.put(bytes).unwrap();
    let permissions = RestorePermissions::search_only(dir.0.join("cache"));
    if !permissions.enforced() {
        return;
    }
    // Search permission permits both lookup and the existing-file comparison;
    // only opening the directory for its durability barrier must fail.
    assert_eq!(cache.read_once(id, bytes.len()).unwrap(), bytes);
    assert!(matches!(cache.put(bytes), Err(Error::Io(_))));
    drop(permissions);
    assert_eq!(cache.put(bytes).unwrap(), id);
}

#[cfg(unix)]
#[test]
fn cache_and_store_creation_require_durable_parent_links_even_on_retry() {
    let f = Fixture::new();
    let dir = TestDir::new();
    let parent = dir.0.join("parent");
    let cache_path = parent.join("nested/cache");
    let store_path = parent.join("nested/store");
    Cache::open(&cache_path).unwrap();
    // Model visible directories left behind by an interrupted create.
    fs::create_dir_all(&store_path).unwrap();
    let permissions = RestorePermissions::search_only(parent);
    if !permissions.enforced() {
        return;
    }
    assert!(matches!(Cache::open(&cache_path), Err(Error::Io(_))));
    assert!(matches!(
        DurableClient::create(&store_path, client(&f), Mode::Enabled),
        Err(Error::Io(_))
    ));
    // Parent barriers must precede creating even the writer lock or generation.
    assert!(!store_path.join("writer.lock").exists());
    assert!(!store_path.join("generation").exists());
    drop(permissions);
    let cache = Cache::open(&cache_path).unwrap();
    let id = cache.put(b"reachable after retry").unwrap();
    assert_eq!(cache.read_once(id, 64).unwrap(), b"reachable after retry");
    let store = DurableClient::create(&store_path, client(&f), Mode::Enabled).unwrap();
    drop(store);
    DurableClient::recover(&store_path, &f.context, &f.keys, Mode::Enabled).unwrap();
}

#[test]
fn candidate_failure_observations_never_export_provider_error_payloads() {
    use crate::host::{prepare_open, Limits, Offer, Provider};
    use std::sync::{Arc, Mutex};
    use std::time::Instant;
    use tracing::{
        span::{Attributes, Id, Record},
        Event, Metadata, Subscriber,
    };
    const PAYLOAD: &str = "PRIVATE_PROVIDER_PAYLOAD_72913";
    #[derive(Clone)]
    struct Capture(Arc<Mutex<Vec<String>>>);
    impl Subscriber for Capture {
        fn enabled(&self, _: &Metadata<'_>) -> bool {
            true
        }
        fn new_span(&self, _: &Attributes<'_>) -> Id {
            Id::from_u64(1)
        }
        fn record(&self, _: &Id, _: &Record<'_>) {}
        fn record_follows_from(&self, _: &Id, _: &Id) {}
        fn event(&self, event: &Event<'_>) {
            struct Fields(String);
            impl tracing::field::Visit for Fields {
                fn record_debug(
                    &mut self,
                    field: &tracing::field::Field,
                    value: &dyn std::fmt::Debug,
                ) {
                    use std::fmt::Write;
                    write!(&mut self.0, "{}={value:?};", field.name()).unwrap();
                }
            }
            let mut fields = Fields(String::new());
            event.record(&mut fields);
            self.0.lock().unwrap().push(fields.0);
        }
        fn enter(&self, _: &Id) {}
        fn exit(&self, _: &Id) {}
    }
    struct Fallback {
        blob: crate::Hash,
        bytes: Vec<u8>,
    }
    impl Provider for Fallback {
        fn get(&mut self, id: crate::Hash, _: usize, _: Instant) -> crate::Result<Vec<u8>> {
            if id == self.blob {
                Ok(self.bytes.clone())
            } else {
                Err(Error::Io(PAYLOAD.into()))
            }
        }
    }
    let f = Fixture::new();
    let cert = f.certificate(&f.members(&[]));
    let blob = cert.blob_id(&f.context);
    let offers = [[0; 32], blob].map(|blob| {
        Offer {
            blob,
            tail: vec![],
            floor_proofs: vec![],
        }
        .encode()
    });
    let events = Arc::new(Mutex::new(Vec::new()));
    let prepared = tracing::subscriber::with_default(Capture(events.clone()), || {
        prepare_open(
            &mut Fallback {
                blob,
                bytes: cert.encode(&f.context),
            },
            &offers,
            &f.context,
            &f.keys,
            None,
            0,
            Mode::Enabled,
            &Limits::default(),
        )
        .unwrap()
    });
    assert_eq!(prepared.metrics().rejected, ["io"]);
    let events = events.lock().unwrap();
    assert!(
        events
            .iter()
            .any(|event| event.contains("checkpoint_candidate_failed")
                && event.contains("reason=\"io\"")),
        "failure reason exported: {events:?}"
    );
    assert!(!events.iter().any(|event| event.contains(PAYLOAD)));
}

#[cfg(unix)]
#[test]
fn reused_evidence_root_requires_archive_barrier_before_generation_commit() {
    let f = Fixture::new();
    let dir = TestDir::new();
    let mut store = DurableClient::create(&dir.0, client(&f), Mode::Enabled).unwrap();
    let generation = store.generation();
    let previous = fs::read(dir.0.join("generation")).unwrap();
    let permissions = RestorePermissions::search_only(dir.0.join("evidence"));
    if !permissions.enforced() {
        return;
    }
    assert!(matches!(
        store.record_retry("must-not-commit".into(), 1),
        Err(Error::Io(_))
    ));
    let work = store.last_persist_work();
    assert_eq!(work.trusted_checks, 1, "exercise the cached-root shortcut");
    assert_eq!(work.new_nodes, 0);
    assert_eq!(work.value_encodes, 0);
    assert_eq!(store.generation(), generation);
    assert!(store.retries().is_empty());
    assert_eq!(fs::read(dir.0.join("generation")).unwrap(), previous);
    drop(permissions);
    assert!(store.record_retry("fail-stopped".into(), 2).is_err());
    drop(store);
    let mut recovered = DurableClient::recover(&dir.0, &f.context, &f.keys, Mode::Enabled).unwrap();
    assert_eq!(recovered.generation(), generation);
    assert!(recovered.retries().is_empty());
    recovered.record_retry("after-recovery".into(), 3).unwrap();
    drop(recovered);
    let recovered = DurableClient::recover(&dir.0, &f.context, &f.keys, Mode::Enabled).unwrap();
    assert_eq!(recovered.retries().get("after-recovery"), Some(&3));
}

#[test]
fn complete_generation_at_limit_recovers_and_one_byte_over_is_rejected() {
    // Keep this independent of the writer's private constant: this is the public
    // 64 MiB complete-record boundary, including its 32-byte checksum.
    const FRAME_BYTES: usize = 64 * 1024 * 1024;
    const CHECKSUM_BYTES: usize = 32;
    let f = Fixture::new();
    let dir = TestDir::new();
    let mut store = DurableClient::create(&dir.0, client(&f), Mode::Enabled).unwrap();
    let original = fs::metadata(dir.0.join("generation")).unwrap().len() as usize;
    // The empty outbox gains `"<key>":[0]`: key length + six JSON bytes.
    // Generation 0 -> 1 has the same encoded width.
    let key_len = FRAME_BYTES - CHECKSUM_BYTES - (original - CHECKSUM_BYTES) - 6;
    store.enqueue("x".repeat(key_len), vec![0]).unwrap();
    assert_eq!(
        fs::metadata(dir.0.join("generation")).unwrap().len(),
        FRAME_BYTES as u64
    );
    drop(store);
    let mut recovered = DurableClient::recover(&dir.0, &f.context, &f.keys, Mode::Enabled).unwrap();
    assert_eq!(recovered.generation(), 1);
    assert_eq!(recovered.outbox().len(), 1);
    let (key, value) = recovered.outbox().iter().next().unwrap();
    assert_eq!(key.len(), key_len);
    assert_eq!(value, &[0]);
    let key = key.clone();
    // [10] adds exactly one byte over [0]; generation 1 -> 2 is still one digit.
    assert_eq!(recovered.enqueue(key, vec![10]), Err(Error::Budget));
    assert_eq!(recovered.generation(), 1);
    assert_eq!(recovered.outbox().values().next().unwrap(), &[0]);
    assert_eq!(
        fs::metadata(dir.0.join("generation")).unwrap().len(),
        FRAME_BYTES as u64
    );
    drop(recovered);
    let recovered = DurableClient::recover(&dir.0, &f.context, &f.keys, Mode::Enabled).unwrap();
    assert_eq!(recovered.generation(), 1);
    assert_eq!(recovered.outbox().values().next().unwrap(), &[0]);
}
