//! Effectful bounded retrieval and atomic durable client generations.
use crate::{
    certificate::{Certificate, Context, KeyVerifier, SignedMessage},
    codec::{put_bytes, put_string, put_u32, Reader},
    coverage::Proof,
    hash, hex,
    member::{Client, Floor, Step},
    Error, Hash, Result,
};
use fs2::FileExt;
use serde::{Deserialize, Serialize};
use std::{
    collections::BTreeMap,
    fs::{self, File, OpenOptions},
    io::{Read, Write},
    path::{Path, PathBuf},
    sync::{
        atomic::{AtomicU64, AtomicUsize, Ordering},
        Arc,
    },
    time::{Duration, Instant},
};

#[derive(Clone, Debug)]
pub struct Limits {
    pub candidates: usize,
    pub certificate_bytes: usize,
    pub offer_bytes: usize,
    pub tail_steps: usize,
    pub total_bytes: usize,
    pub total_steps: usize,
    pub proof_paths: usize,
    pub timeout: Duration,
}
impl Default for Limits {
    fn default() -> Self {
        Self {
            candidates: 8,
            certificate_bytes: 16 * 1024 * 1024,
            offer_bytes: 4 * 1024 * 1024,
            tail_steps: 2048,
            total_bytes: 32 * 1024 * 1024,
            total_steps: 4096,
            proof_paths: 65536,
            timeout: Duration::from_millis(5000),
        }
    }
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Offer {
    pub blob: Hash,
    pub tail: Vec<Step>,
    pub floor_proofs: Vec<(String, Proof)>,
}
fn put_proof(out: &mut Vec<u8>, p: &Proof) {
    put_u32(out, usize::from(p.present));
    put_u32(out, p.siblings.len());
    for h in &p.siblings {
        out.extend(h)
    }
}
fn read_proof(r: &mut Reader<'_>) -> Result<Proof> {
    let p = r.u32()?;
    if p > 1 {
        return Err(Error::Invalid("proof tag"));
    }
    let n = r.count(256)?;
    if n != 256 {
        return Err(Error::Invalid("proof path length"));
    }
    let mut siblings = Vec::with_capacity(n);
    for _ in 0..n {
        siblings.push(r.hash()?)
    }
    Ok(Proof {
        present: p == 1,
        siblings,
    })
}
impl Offer {
    pub fn encode(&self) -> Vec<u8> {
        let mut b = self.blob.to_vec();
        put_u32(&mut b, self.tail.len());
        for s in &self.tail {
            put_bytes(&mut b, &s.message.encode());
            put_u32(&mut b, s.ancestry.len());
            for (m, p) in &s.ancestry {
                put_bytes(&mut b, &m.encode());
                put_proof(&mut b, p)
            }
            put_proof(&mut b, &s.identity);
            put_u32(&mut b, s.replacements.len());
            for (id, p) in &s.replacements {
                put_string(&mut b, id);
                put_proof(&mut b, p)
            }
        }
        put_u32(&mut b, self.floor_proofs.len());
        for (id, p) in &self.floor_proofs {
            put_string(&mut b, id);
            put_proof(&mut b, p)
        }
        b
    }
    pub fn decode(bytes: &[u8], limits: &Limits) -> Result<Self> {
        let mut r = Reader::new(bytes, limits.offer_bytes)?;
        let blob = r.hash()?;
        let n = r.count(limits.tail_steps)?;
        let mut tail = Vec::new();
        for _ in 0..n {
            let message = SignedMessage::decode(r.bytes(256 * 1024)?)?;
            let n = r.count(256)?;
            let mut ancestry = Vec::new();
            for _ in 0..n {
                ancestry.push((
                    SignedMessage::decode(r.bytes(256 * 1024)?)?,
                    read_proof(&mut r)?,
                ))
            }
            let identity = read_proof(&mut r)?;
            let n = r.count(256)?;
            let mut replacements = Vec::new();
            for _ in 0..n {
                replacements.push((r.string(71)?, read_proof(&mut r)?))
            }
            tail.push(Step {
                message,
                ancestry,
                identity,
                replacements,
            })
        }
        let n = r.count(4096)?;
        let mut floor_proofs = Vec::new();
        for _ in 0..n {
            floor_proofs.push((r.string(71)?, read_proof(&mut r)?))
        }
        r.finish()?;
        Ok(Self {
            blob,
            tail,
            floor_proofs,
        })
    }
    fn paths(&self) -> usize {
        self.floor_proofs.len()
            + self
                .tail
                .iter()
                .map(|s| 1 + s.ancestry.len() + s.replacements.len())
                .sum::<usize>()
    }
}

/// Providers must implement bounded, cancelable reads; untrusted locators are not callbacks.
pub trait Provider {
    fn get(&mut self, id: Hash, max: usize, deadline: Instant) -> Result<Vec<u8>>;
}
const GENERATION_BYTES: usize = 64 * 1024 * 1024;
static SERIAL: AtomicU64 = AtomicU64::new(0);
static READERS: AtomicUsize = AtomicUsize::new(0);
fn micros(start: Instant) -> u64 {
    start.elapsed().as_micros().min(u64::MAX as u128) as u64
}
fn error_code(error: &Error) -> &'static str {
    match error {
        Error::Invalid(_) => "invalid",
        Error::Missing(_) => "missing_dependencies",
        Error::Unsupported => "unsupported_profile",
        Error::Budget => "budget_exceeded",
        Error::Concurrent => "concurrent_local_update",
        Error::Io(_) => "io",
        Error::Disabled => "disabled",
        Error::Cancelled => "cancelled",
    }
}
/// Persist directory contents and every parent link, including links left visible
/// by a prior failed creation. This runs only when opening/creating a store, not
/// on each admission. Existing ancestors are not assumed to have been synced.
fn create_durable_directory(path: &Path) -> Result<()> {
    fs::create_dir_all(path)?;
    if fs::symlink_metadata(path)?.file_type().is_symlink() {
        return Err(Error::Invalid("store directory symlink"));
    }
    let canonical = fs::canonicalize(path)?;
    // Sync children before the directory entries that make them reachable. Walk
    // to the root so a retry also repairs an interrupted multi-directory create.
    for directory in canonical.ancestors() {
        File::open(directory)?.sync_all()?;
    }
    Ok(())
}
#[derive(Clone, Debug)]
pub struct Cache {
    root: Arc<PathBuf>,
    #[cfg(test)]
    faults: Arc<std::sync::Mutex<CacheFaults>>,
}
#[cfg(test)]
#[derive(Debug, Default)]
struct CacheFaults {
    after_link: Option<Hash>,
    directory_sync: bool,
}
impl Cache {
    pub fn open(path: impl AsRef<Path>) -> Result<Self> {
        create_durable_directory(path.as_ref())?;
        Ok(Self {
            root: Arc::new(fs::canonicalize(path)?),
            #[cfg(test)]
            faults: Default::default(),
        })
    }
    pub fn put(&self, bytes: &[u8]) -> Result<Hash> {
        if bytes.len() > 16 * 1024 * 1024 {
            return Err(Error::Budget);
        }
        let id = hash(b"cbcl/checkpoint/blob/v1", bytes);
        let dest = self.root.join(hex(&id));
        if dest.exists() {
            let old = read_regular(&dest, 16 * 1024 * 1024)?;
            if old != bytes {
                return Err(Error::Invalid("immutable cache collision"));
            }
            self.sync_directory()?;
            return Ok(id);
        }
        let temp = self.root.join(format!(
            ".pending-{}-{}",
            std::process::id(),
            SERIAL.fetch_add(1, Ordering::Relaxed)
        ));
        let mut f = OpenOptions::new()
            .create_new(true)
            .write(true)
            .open(&temp)?;
        let result = (|| -> Result<()> {
            f.write_all(bytes)?;
            f.sync_all()?;
            match fs::hard_link(&temp, &dest) {
                Ok(()) => {
                    #[cfg(test)]
                    {
                        let mut faults = self.faults.lock().expect("cache fault lock");
                        if faults.after_link == Some(id) {
                            faults.after_link = None;
                            return Err(Error::Io("injected archive post-link failure".into()));
                        }
                    }
                }
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {
                    if read_regular(&dest, 16 * 1024 * 1024)? != bytes {
                        return Err(Error::Invalid("cache collision"));
                    }
                }
                Err(e) => return Err(e.into()),
            };
            File::open(self.root.as_ref())?.sync_all()?;
            Ok(())
        })();
        let _ = fs::remove_file(temp);
        result?;
        Ok(id)
    }
    /// Durability barrier for reused entries as well as newly linked blobs.
    pub fn sync_directory(&self) -> Result<()> {
        #[cfg(test)]
        {
            let mut faults = self.faults.lock().expect("cache fault lock");
            if faults.directory_sync {
                faults.directory_sync = false;
                return Err(Error::Io("injected archive directory sync failure".into()));
            }
        }
        File::open(self.root.as_ref())?.sync_all()?;
        Ok(())
    }
    #[cfg(test)]
    pub(crate) fn fail_after_link_for(&self, id: Hash) {
        self.faults.lock().expect("cache fault lock").after_link = Some(id);
    }
    #[cfg(test)]
    pub(crate) fn fail_next_directory_sync(&self) {
        self.faults.lock().expect("cache fault lock").directory_sync = true;
    }
    pub fn path(&self, id: Hash) -> PathBuf {
        self.root.join(hex(&id))
    }
    /// Metadata-only lookup in an OS-fenced immutable local archive, not remote evidence.
    pub fn contains_trusted(&self, id: Hash) -> Result<bool> {
        match fs::symlink_metadata(self.path(id)) {
            Ok(m) if m.is_file() && !m.file_type().is_symlink() => Ok(true),
            Ok(_) => Err(Error::Invalid("archive entry not regular")),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(false),
            Err(e) => Err(e.into()),
        }
    }
    pub fn read_once(&self, id: Hash, max: usize) -> Result<Vec<u8>> {
        let bytes = read_regular(&self.path(id), max)?;
        if hash(b"cbcl/checkpoint/blob/v1", &bytes) != id {
            return Err(Error::Invalid("archive address"));
        }
        Ok(bytes)
    }
}
fn store_instance(path: &Path) -> Hash {
    let identity = format!(
        "{}:{}:{}:{:?}",
        path.display(),
        std::process::id(),
        SERIAL.fetch_add(1, Ordering::Relaxed),
        std::time::SystemTime::now()
    );
    hash(
        b"cbcl/checkpoint/local-store-instance/v1",
        identity.as_bytes(),
    )
}
fn read_regular(path: &Path, max: usize) -> Result<Vec<u8>> {
    let mut opts = OpenOptions::new();
    opts.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        opts.custom_flags(libc::O_NONBLOCK | libc::O_NOFOLLOW);
    }
    let mut file = opts.open(path)?;
    let meta = file.metadata()?;
    if !meta.is_file() {
        return Err(Error::Invalid("cache entry not regular"));
    }
    if meta.len() > max as u64 {
        return Err(Error::Budget);
    }
    let mut b = Vec::new();
    Read::by_ref(&mut file)
        .take(max as u64 + 1)
        .read_to_end(&mut b)?;
    if b.len() > max {
        return Err(Error::Budget);
    }
    Ok(b)
}
impl Provider for Cache {
    // `AtomicUsize::try_update` is unavailable at the workspace's Rust 1.75
    // MSRV, while newer compilers deprecate its former name.
    #[allow(deprecated)]
    fn get(&mut self, id: Hash, max: usize, deadline: Instant) -> Result<Vec<u8>> {
        if Instant::now() >= deadline {
            return Err(Error::Cancelled);
        }
        if READERS
            .fetch_update(Ordering::AcqRel, Ordering::Relaxed, |n| {
                if n < 2 {
                    Some(n + 1)
                } else {
                    None
                }
            })
            .is_err()
        {
            return Err(Error::Budget);
        }
        let path = self.path(id);
        let (tx, rx) = std::sync::mpsc::sync_channel(1);
        let spawn = std::thread::Builder::new()
            .name("checkpoint-cache-read".into())
            .spawn(move || {
                let result = read_regular(&path, max).and_then(|b| {
                    if hash(b"cbcl/checkpoint/blob/v1", &b) == id {
                        Ok(b)
                    } else {
                        Err(Error::Invalid("cache address"))
                    }
                });
                READERS.fetch_sub(1, Ordering::AcqRel);
                let _ = tx.send(result);
            });
        if let Err(e) = spawn {
            READERS.fetch_sub(1, Ordering::AcqRel);
            return Err(e.into());
        }
        rx.recv_timeout(deadline.saturating_duration_since(Instant::now()))
            .map_err(|_| Error::Cancelled)?
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub enum Mode {
    #[default]
    Off,
    Shadow,
    Enabled,
}
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct OpenMetrics {
    pub candidates: usize,
    pub bytes: usize,
    pub offer_bytes: usize,
    pub certificate_bytes: usize,
    pub tail_message_bytes: usize,
    pub ancestry_message_bytes: usize,
    pub floor_proof_bytes: usize,
    pub tail_steps: usize,
    pub proof_paths: usize,
    pub signatures_checked: usize,
    pub signature_preimage_bytes: usize,
    pub rejected: Vec<String>,
    pub elapsed_micros: u64,
    pub companion_history_reads: usize,
    pub prefix_replay: usize,
    pub decode_micros: u64,
    pub verify_and_summary_decode_micros: u64,
    pub fetch_micros: u64,
    pub tail_micros: u64,
    pub floor_micros: u64,
    pub retain_micros: u64,
    pub commit_micros: u64,
    pub requested_target_covered: bool,
}
#[derive(Clone, Debug)]
pub struct PreparedInstall {
    client: Client,
    expected_generation: u64,
    manifest: crate::certificate::Manifest,
    metrics: OpenMetrics,
    local_floor_preserved: bool,
    shadow_compared: bool,
    captured_floor: Option<Floor>,
    store_binding: Option<Hash>,
    deadline: Instant,
    started: Instant,
    requested_target: Option<Vec<String>>,
    limits: Limits,
}
impl PreparedInstall {
    pub fn client(&self) -> &Client {
        &self.client
    }
    pub fn manifest(&self) -> &crate::certificate::Manifest {
        &self.manifest
    }
    pub fn metrics(&self) -> &OpenMetrics {
        &self.metrics
    }
    pub fn deadline(&self) -> Instant {
        self.deadline
    }
    pub fn requested_target(&self) -> Option<&[String]> {
        self.requested_target.as_deref()
    }
    /// This establishes coverage of caller-named IDs, never global freshness.
    pub fn verify_requested_target(
        &mut self,
        ids: &[String],
        proofs: &[(String, Proof)],
    ) -> Result<()> {
        if ids.is_empty()
            || ids.len() > 4096
            || ids.windows(2).any(|w| w[0] >= w[1])
            || proofs.len() != ids.len()
        {
            return Err(Error::Invalid("requested target footprint"));
        }
        let mut bytes = 0usize;
        for (id, p) in proofs {
            crate::certificate::native_id(id)?;
            if p.siblings.len() != 256 {
                return Err(Error::Invalid("target proof length"));
            }
            bytes = bytes
                .checked_add(4 + id.len() + 8 + 32 * 256)
                .ok_or(Error::Budget)?;
        }
        self.metrics.bytes = self.metrics.bytes.checked_add(bytes).ok_or(Error::Budget)?;
        self.metrics.proof_paths = self
            .metrics
            .proof_paths
            .checked_add(proofs.len())
            .ok_or(Error::Budget)?;
        if self.metrics.bytes > self.limits.total_bytes
            || self.metrics.proof_paths > self.limits.proof_paths
        {
            return Err(Error::Budget);
        }
        for (expected, (id, p)) in ids.iter().zip(proofs) {
            if Instant::now() >= self.deadline {
                return Err(Error::Cancelled);
            }
            if expected != id {
                return Err(Error::Invalid("target proof identity"));
            }
            p.verify(self.client.coverage, id)?;
            if !p.present {
                return Err(Error::Missing(vec![id.clone()]));
            }
        }
        self.requested_target = Some(ids.to_vec());
        self.metrics.requested_target_covered = true;
        Ok(())
    }
}
// Explicit trust, generation, mode and budget inputs mirror CON-3503.
#[allow(clippy::too_many_arguments)]
pub fn prepare_open(
    provider: &mut dyn Provider,
    offers: &[Vec<u8>],
    c: &Context,
    keys: &dyn KeyVerifier,
    previous: Option<&Client>,
    generation: u64,
    mode: Mode,
    limits: &Limits,
) -> Result<PreparedInstall> {
    if mode == Mode::Off {
        return Err(Error::Disabled);
    }
    if offers.len() > limits.candidates {
        return Err(Error::Budget);
    }
    struct CountKeys<'a> {
        inner: &'a dyn KeyVerifier,
        calls: std::cell::Cell<usize>,
        bytes: std::cell::Cell<usize>,
    }
    impl KeyVerifier for CountKeys<'_> {
        fn verify(&self, key: &str, preimage: &[u8], signature: &[u8]) -> bool {
            self.calls.set(self.calls.get().saturating_add(1));
            self.bytes
                .set(self.bytes.get().saturating_add(preimage.len()));
            self.inner.verify(key, preimage, signature)
        }
    }
    let counted = CountKeys {
        inner: keys,
        calls: Default::default(),
        bytes: Default::default(),
    };
    let keys: &dyn KeyVerifier = &counted;
    let start = Instant::now();
    let deadline = start.checked_add(limits.timeout).ok_or(Error::Budget)?;
    let mut metrics = OpenMetrics::default();
    let operation = SERIAL.fetch_add(1, Ordering::Relaxed);
    tracing::info!(operation,generation,mode=?mode,"checkpoint_open_started");
    let mut missing = std::collections::BTreeSet::new();
    for bytes in offers {
        if Instant::now() >= deadline {
            return Err(Error::Cancelled);
        }
        metrics.candidates += 1;
        metrics.offer_bytes = metrics
            .offer_bytes
            .checked_add(bytes.len())
            .ok_or(Error::Budget)?;
        metrics.bytes = metrics
            .bytes
            .checked_add(bytes.len())
            .ok_or(Error::Budget)?;
        if metrics.bytes > limits.total_bytes {
            return Err(Error::Budget);
        }
        let result = (|| -> Result<(Client, crate::certificate::Manifest)> {
            let clock = Instant::now();
            let offer = Offer::decode(bytes, limits)?;
            metrics.decode_micros += micros(clock);
            metrics.tail_message_bytes += offer
                .tail
                .iter()
                .map(|s| s.message.encode().len())
                .sum::<usize>();
            metrics.ancestry_message_bytes += offer
                .tail
                .iter()
                .flat_map(|s| &s.ancestry)
                .map(|(m, _)| m.encode().len())
                .sum::<usize>();
            metrics.floor_proof_bytes += offer
                .floor_proofs
                .iter()
                .map(|(id, _)| 4 + id.len() + 8 + 256 * 32)
                .sum::<usize>();
            metrics.tail_steps = metrics
                .tail_steps
                .checked_add(offer.tail.len())
                .ok_or(Error::Budget)?;
            metrics.proof_paths = metrics
                .proof_paths
                .checked_add(offer.paths())
                .ok_or(Error::Budget)?;
            if metrics.tail_steps > limits.total_steps || metrics.proof_paths > limits.proof_paths {
                return Err(Error::Budget);
            }
            let remaining = limits.total_bytes - metrics.bytes;
            let reserved = limits.certificate_bytes.min(remaining);
            if reserved == 0 {
                return Err(Error::Budget);
            }
            // A failed/partial fetch can consume its full allowance. Reserve
            // that allowance before the callback, refund only known success.
            metrics.bytes = metrics.bytes.checked_add(reserved).ok_or(Error::Budget)?;
            let clock = Instant::now();
            let blob = provider.get(offer.blob, reserved, deadline)?;
            metrics.fetch_micros += micros(clock);
            if blob.len() > reserved {
                return Err(Error::Budget);
            }
            metrics.bytes -= reserved - blob.len();
            metrics.certificate_bytes += blob.len();
            if metrics.bytes > limits.total_bytes || blob.len() > limits.certificate_bytes {
                return Err(Error::Budget);
            }
            if hash(b"cbcl/checkpoint/blob/v1", &blob) != offer.blob {
                return Err(Error::Invalid("provider content address"));
            }
            let clock = Instant::now();
            let cert = Certificate::decode(&blob, c)?;
            metrics.decode_micros += micros(clock);
            let clock = Instant::now();
            let mut client = Client::from_certificate(c, &cert, keys)?;
            metrics.verify_and_summary_decode_micros += micros(clock);
            let clock = Instant::now();
            for step in &offer.tail {
                if Instant::now() >= deadline {
                    return Err(Error::Cancelled);
                }
                client.apply(step, c, keys)?;
            }
            metrics.tail_micros += micros(clock);
            if let Some(old) = previous {
                let clock = Instant::now();
                client.check_floor(&old.floor(), &offer.floor_proofs)?;
                metrics.floor_micros += micros(clock);
                tracing::info!(
                    operation,
                    generation = generation.saturating_add(1),
                    heads = old.frontier.len(),
                    "checkpoint_floor_checked"
                );
                let clock = Instant::now();
                client.retain_from(old)?;
                metrics.retain_micros += micros(clock);
            } else if !offer.floor_proofs.is_empty() {
                return Err(Error::Invalid("unexpected floor proofs"));
            }
            if Instant::now() >= deadline {
                return Err(Error::Cancelled);
            }
            Ok((client, cert.manifest))
        })();
        metrics.signatures_checked = counted.calls.get();
        metrics.signature_preimage_bytes = counted.bytes.get();
        match result {
            Ok((client, manifest)) => {
                metrics.elapsed_micros = start.elapsed().as_micros().min(u64::MAX as u128) as u64;
                tracing::info!(
                    operation,
                    candidates = metrics.candidates,
                    bytes = metrics.bytes,
                    tail_steps = metrics.tail_steps,
                    proof_paths = metrics.proof_paths,
                    elapsed_micros = metrics.elapsed_micros,
                    "checkpoint_open_prepared"
                );
                return Ok(PreparedInstall {
                    client,
                    expected_generation: generation,
                    manifest,
                    metrics,
                    local_floor_preserved: previous.is_some(),
                    shadow_compared: false,
                    captured_floor: previous.map(Client::floor),
                    store_binding: None,
                    deadline,
                    started: start,
                    requested_target: None,
                    limits: limits.clone(),
                });
            }
            Err(Error::Cancelled) => return Err(Error::Cancelled),
            Err(Error::Budget)
                if metrics.bytes >= limits.total_bytes
                    || metrics.tail_steps > limits.total_steps
                    || metrics.proof_paths > limits.proof_paths =>
            {
                return Err(Error::Budget)
            }
            Err(Error::Missing(ids)) => {
                metrics
                    .rejected
                    .push("missing authenticated dependencies".into());
                missing.extend(ids);
            }
            Err(e) => {
                let reason = error_code(&e);
                tracing::info!(operation, reason, "checkpoint_candidate_failed");
                metrics.rejected.push(reason.into());
            }
        }
    }
    if metrics.bytes >= limits.total_bytes
        || metrics.tail_steps > limits.total_steps
        || metrics.proof_paths > limits.proof_paths
    {
        return Err(Error::Budget);
    }
    if !missing.is_empty() {
        return Err(Error::Missing(missing.into_iter().collect()));
    }
    Err(Error::Invalid("no usable checkpoint candidate"))
}

/// Native/UI entry point bounding fetch, decode, cryptography and proof work,
/// including trusted adapters which unexpectedly stall. Worker count is bounded.
#[allow(clippy::too_many_arguments)]
pub fn prepare_open_bounded(
    mut provider: Box<dyn Provider + Send>,
    offers: Vec<Vec<u8>>,
    c: Arc<Context>,
    keys: Arc<dyn KeyVerifier + Send + Sync>,
    previous: Option<Arc<Client>>,
    generation: u64,
    mode: Mode,
    limits: Limits,
) -> Result<PreparedInstall> {
    let started = Instant::now();
    let deadline = started.checked_add(limits.timeout).ok_or(Error::Budget)?;
    crate::runtime::validation(
        move || {
            let mut prepared = prepare_open(
                provider.as_mut(),
                &offers,
                &c,
                keys.as_ref(),
                previous.as_deref(),
                generation,
                mode,
                &limits,
            )?;
            prepared.deadline = deadline;
            prepared.started = started;
            Ok(prepared)
        },
        deadline,
    )
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct DiskGeneration {
    version: u32,
    generation: u64,
    context: Hash,
    coverage: Hash,
    summary: Vec<u8>,
    frontier: Vec<String>,
    evidence_root: Option<Hash>,
    outbox: BTreeMap<String, Vec<u8>>,
    retry: BTreeMap<String, u64>,
}
/// Single OS-fenced writer. Every durable mutation shares the install CAS generation.
pub struct DurableClient {
    client: Arc<Client>,
    generation: u64,
    outbox: BTreeMap<String, Vec<u8>>,
    retry: BTreeMap<String, u64>,
    root: PathBuf,
    archive: Cache,
    _lock: File,
    mode: Mode,
    stopped: bool,
    instance: Hash,
    last_persist_work: crate::evidence::PersistWork,
    #[cfg(test)]
    fault: Option<PersistFault>,
}
impl DurableClient {
    pub fn create(path: impl AsRef<Path>, client: Client, mode: Mode) -> Result<Self> {
        let root = path.as_ref().to_path_buf();
        create_durable_directory(&root)?;
        let lock = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(root.join("writer.lock"))?;
        FileExt::try_lock_exclusive(&lock)?;
        if root.join("generation").exists() {
            return Err(Error::Invalid("generation exists; recover instead"));
        }
        let archive = Cache::open(root.join("evidence"))?;
        let instance = store_instance(&root);
        let mut s = Self {
            client: Arc::new(client),
            generation: 0,
            outbox: BTreeMap::new(),
            retry: BTreeMap::new(),
            root,
            archive,
            _lock: lock,
            mode,
            stopped: false,
            instance,
            last_persist_work: Default::default(),
            #[cfg(test)]
            fault: None,
        };
        tracing::info!(instance=%hex(&s.instance),generation=0u64,"checkpoint_store_floor_checked");
        s.persist()?;
        Ok(s)
    }
    pub fn recover(
        path: impl AsRef<Path>,
        c: &Context,
        keys: &dyn KeyVerifier,
        mode: Mode,
    ) -> Result<Self> {
        c.validate(keys)?;
        crate::member::validate_profile(c)?;
        let root = path.as_ref().to_path_buf();
        let lock = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(root.join("writer.lock"))?;
        FileExt::try_lock_exclusive(&lock)?;
        let bytes = read_regular(&root.join("generation"), GENERATION_BYTES)?;
        if bytes.len() < 32 || hash(b"cbcl/checkpoint/generation/v1", &bytes[32..]) != bytes[..32] {
            return Err(Error::Invalid("torn generation"));
        }
        let d: DiskGeneration = serde_json::from_slice(&bytes[32..])
            .map_err(|_| Error::Invalid("generation grammar"))?;
        if serde_json::to_vec(&d).map_err(|_| Error::Invalid("generation encoding"))? != bytes[32..]
        {
            return Err(Error::Invalid("noncanonical generation record"));
        }
        if d.version != 1 || d.context != c.hash() {
            return Err(Error::Invalid("generation context"));
        }
        let summary = crate::summary::Summary::decode_for(
            &d.summary,
            c.target.state.as_ref().ok_or(Error::Unsupported)?,
            c.target.causal_protocol.as_ref(),
        )?;
        let archive = Cache::open(root.join("evidence"))?;
        let evidence = crate::evidence::Evidence::recover(&archive, d.evidence_root, keys)?;
        let client = Client {
            context: d.context,
            coverage: d.coverage,
            summary,
            frontier: d.frontier,
            evidence,
        };
        let floor = client.floor();
        if floor.frontier.is_empty() || floor.frontier.windows(2).any(|w| w[0] >= w[1]) {
            return Err(Error::Invalid("recovered frontier"));
        }
        for id in &floor.frontier {
            crate::certificate::native_id(id)?
        }
        let instance = store_instance(&root);
        tracing::info!(instance=%hex(&instance),generation=d.generation,mode=?mode,evidence_records=client.evidence.len(),outbox_records=d.outbox.len(),"checkpoint_recovered");
        Ok(Self {
            client: Arc::new(client),
            generation: d.generation,
            outbox: d.outbox,
            retry: d.retry,
            root,
            archive,
            _lock: lock,
            mode,
            stopped: false,
            instance,
            last_persist_work: Default::default(),
            #[cfg(test)]
            fault: None,
        })
    }
    fn persist(&mut self) -> Result<()> {
        #[cfg(test)]
        if let Some(PersistFault::Pause(duration)) = self.fault {
            self.fault = None;
            std::thread::sleep(duration);
        }
        #[cfg(test)]
        self.fail_at(PersistFault::BeforeWrite)?;
        let mut work = crate::evidence::PersistWork::default();
        let evidence_root = self
            .client
            .evidence
            .persist_counted(&self.archive, &mut work)?;
        self.last_persist_work = work;
        // A prior failed directory sync may leave a visible root. Visibility is
        // insufficient: flush all archive links before referencing any root.
        self.archive.sync_directory()?;
        let d = DiskGeneration {
            version: 1,
            generation: self.generation,
            context: self.client.context,
            coverage: self.client.coverage,
            summary: self.client.summary.encode(),
            frontier: self.client.frontier.clone(),
            evidence_root,
            outbox: self.outbox.clone(),
            retry: self.retry.clone(),
        };
        let body =
            serde_json::to_vec(&d).map_err(|_| Error::Invalid("generation serialization"))?;
        if body.len() > GENERATION_BYTES - 32 {
            return Err(Error::Budget);
        }
        let (temp, mut f) = loop {
            let temp = self.root.join(format!(
                "generation.pending-{}-{}",
                std::process::id(),
                SERIAL.fetch_add(1, Ordering::Relaxed)
            ));
            match OpenOptions::new().write(true).create_new(true).open(&temp) {
                Ok(f) => break (temp, f),
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => return Err(e.into()),
            }
        };
        f.write_all(&hash(b"cbcl/checkpoint/generation/v1", &body))?;
        f.write_all(&body)?;
        #[cfg(test)]
        self.fail_at(PersistFault::AfterWrite)?;
        f.sync_all()?;
        #[cfg(test)]
        self.fail_at(PersistFault::AfterSync)?;
        fs::rename(temp, self.root.join("generation"))?;
        #[cfg(test)]
        self.fail_at(PersistFault::AfterRename)?;
        File::open(&self.root)?.sync_all()?;
        #[cfg(test)]
        self.fail_at(PersistFault::AfterDirectorySync)?;
        tracing::info!(instance=%hex(&self.instance),generation=self.generation,evidence_records=self.client.evidence.len(),floor_heads=self.client.frontier.len(),"checkpoint_durable_generation");
        Ok(())
    }
    /// Work performed by the most recent persistence attempt.
    pub fn last_persist_work(&self) -> &crate::evidence::PersistWork {
        &self.last_persist_work
    }
    pub fn generation(&self) -> u64 {
        self.generation
    }
    pub fn client(&self) -> &Client {
        &self.client
    }
    /// Share the installed immutable state without copying summary or frontier.
    /// Holding this view also keeps its allocations alive across installation.
    pub fn snapshot(&self) -> Arc<Client> {
        Arc::clone(&self.client)
    }
    pub fn prepare(
        &self,
        provider: &mut dyn Provider,
        offers: &[Vec<u8>],
        c: &Context,
        keys: &dyn KeyVerifier,
        limits: &Limits,
    ) -> Result<PreparedInstall> {
        self.ensure_live()?;
        let mut prepared = prepare_open(
            provider,
            offers,
            c,
            keys,
            Some(&self.client),
            self.generation,
            self.mode,
            limits,
        )?;
        prepared.store_binding = Some(self.instance);
        tracing::info!(instance=%hex(&self.instance),generation=self.generation.saturating_add(1),"checkpoint_store_floor_checked");
        Ok(prepared)
    }
    pub fn prepare_bounded(
        &self,
        mut provider: Box<dyn Provider + Send>,
        offers: Vec<Vec<u8>>,
        c: Arc<Context>,
        keys: Arc<dyn KeyVerifier + Send + Sync>,
        limits: Limits,
    ) -> Result<PreparedInstall> {
        let started = Instant::now();
        let deadline = started.checked_add(limits.timeout).ok_or(Error::Budget)?;
        self.ensure_live()?;
        let previous = self.snapshot();
        let generation = self.generation;
        let mode = self.mode;
        let binding = self.instance;
        crate::runtime::validation(
            move || {
                let mut p = prepare_open(
                    provider.as_mut(),
                    &offers,
                    &c,
                    keys.as_ref(),
                    Some(&previous),
                    generation,
                    mode,
                    &limits,
                )?;
                p.store_binding = Some(binding);
                tracing::info!(instance=%hex(&binding),generation=generation.saturating_add(1),"checkpoint_store_floor_checked");
                p.deadline = deadline;
                p.started = started;
                Ok(p)
            },
            deadline,
        )
    }
    pub fn admit(&mut self, step: &Step, c: &Context, keys: &dyn KeyVerifier) -> Result<()> {
        self.ensure_live()?;
        let next = self.generation.checked_add(1).ok_or(Error::Budget)?;
        // Ordinary synchronous admission stages its mutable state explicitly;
        // foreground bounded opening only captures an Arc snapshot.
        let mut staged = self.client.as_ref().clone();
        staged.apply(step, c, keys)?;
        let old = std::mem::replace(&mut self.client, Arc::new(staged));
        self.generation = next;
        if let Err(e) = self.persist() {
            self.client = old;
            self.generation -= 1;
            self.stopped = true;
            return Err(e);
        }
        Ok(())
    }
    pub fn mode(&self) -> Mode {
        self.mode
    }
    pub fn set_mode(&mut self, m: Mode) {
        self.mode = m
    }
    pub fn publish(
        &self,
        cache: &Cache,
        cert: &Certificate,
        c: &Context,
        keys: &dyn KeyVerifier,
        advertise: impl FnOnce(Hash) -> Result<()>,
    ) -> Result<Hash> {
        self.ensure_live()?;
        if self.mode != Mode::Enabled {
            return Err(Error::Disabled);
        }
        publish(cache, cert, c, keys, advertise)
    }
    pub fn outbox(&self) -> &BTreeMap<String, Vec<u8>> {
        &self.outbox
    }
    pub fn retries(&self) -> &BTreeMap<String, u64> {
        &self.retry
    }
    /// Explicit read-only fallback. It may traverse history; opening never calls it.
    /// Missing retained ancestors are reported rather than discarding the floor.
    pub fn replay_retained(
        &self,
        c: &Context,
        keys: &dyn KeyVerifier,
    ) -> Result<Vec<(String, cbcl_core::state::Value)>> {
        if self.client.context != c.hash() {
            return Err(Error::Invalid("replay context"));
        }
        let root = c.target_root.id()?;
        let mut by_id: BTreeMap<&str, Vec<&SignedMessage>> = BTreeMap::new();
        for ((id, _), m) in self.client.evidence.iter() {
            by_id.entry(id.as_str()).or_default().push(m);
        }
        let mut todo: Vec<_> = self
            .client
            .frontier
            .iter()
            .cloned()
            .map(|id| (id, false))
            .collect();
        let mut seen = std::collections::BTreeSet::new();
        let mut visiting = std::collections::BTreeSet::new();
        let mut selected = BTreeMap::new();
        let mut history = Vec::new();
        let mut missing = std::collections::BTreeSet::new();
        while let Some((id, expanded)) = todo.pop() {
            if seen.contains(&id) || id == root {
                continue;
            }
            if expanded {
                visiting.remove(&id);
                seen.insert(id.clone());
                history.push(
                    selected
                        .remove(&id)
                        .ok_or(Error::Invalid("archive traversal"))?,
                );
                continue;
            }
            if !visiting.insert(id.clone()) {
                return Err(Error::Invalid("cyclic retained history"));
            }
            let candidate = by_id
                .get(id.as_str())
                .and_then(|ms| {
                    ms.iter()
                        .find(|m| crate::member::authenticate_target(m, c, keys).is_ok())
                })
                .copied();
            let Some(message) = candidate else {
                visiting.remove(&id);
                missing.insert(id);
                continue;
            };
            let act = crate::member::authenticate_target(message, c, keys)?;
            selected.insert(id.clone(), message.clone());
            todo.push((id, true));
            todo.extend(act.predecessors.into_iter().map(|id| (id, false)));
        }
        if !missing.is_empty() {
            return Err(Error::Missing(missing.into_iter().collect()));
        }
        let started = Instant::now();
        let limits = Limits::default();
        let mut p = PreparedInstall {
            client: self.client.as_ref().clone(),
            expected_generation: self.generation,
            manifest: c.manifest(
                self.client.coverage,
                self.client.summary.hash(),
                self.client.frontier.clone(),
            )?,
            metrics: OpenMetrics::default(),
            local_floor_preserved: true,
            shadow_compared: false,
            captured_floor: Some(self.client.floor()),
            store_binding: Some(self.instance),
            deadline: started + limits.timeout,
            started,
            requested_target: None,
            limits,
        };
        compare_shadow(&mut p, &history, c, keys)?;
        Ok(p.client.summary.render())
    }
    pub fn install(&mut self, p: PreparedInstall) -> Result<OpenMetrics> {
        self.ensure_live()?;
        if Instant::now() >= p.deadline {
            return Err(Error::Cancelled);
        }
        if self.mode == Mode::Off {
            return Err(Error::Disabled);
        }
        if p.expected_generation != self.generation {
            tracing::info!(instance=%hex(&self.instance),captured=p.expected_generation,current=self.generation,"checkpoint_install_conflict");
            return Err(Error::Concurrent);
        }
        if p.store_binding != Some(self.instance)
            || p.captured_floor.as_ref() != Some(&self.client.floor())
        {
            return Err(Error::Invalid(
                "installation requires this store's captured floor",
            ));
        }
        if p.client.context != self.client.context || !p.local_floor_preserved {
            return Err(Error::Invalid("warm installation requires floor check"));
        }
        if self.mode == Mode::Shadow {
            if !p.shadow_compared {
                return Err(Error::Invalid("shadow requires ordinary replay comparison"));
            }
            return Ok(p.metrics);
        }
        let next = self.generation.checked_add(1).ok_or(Error::Budget)?;
        let clock = Instant::now();
        let started = p.started;
        let mut metrics = p.metrics;
        let old = std::mem::replace(&mut self.client, Arc::new(p.client));
        self.generation = next;
        if let Err(e) = self.persist() {
            self.client = old;
            self.generation -= 1;
            self.stopped = true;
            return Err(e);
        }
        metrics.commit_micros = micros(clock);
        metrics.elapsed_micros = micros(started);
        tracing::info!(instance=%hex(&self.instance),generation=self.generation,commit_micros=metrics.commit_micros,elapsed_micros=metrics.elapsed_micros,"checkpoint_install_committed");
        Ok(metrics)
    }
    pub fn enqueue(&mut self, id: String, bytes: Vec<u8>) -> Result<()> {
        self.ensure_live()?;
        if bytes.len() > 256 * 1024 {
            return Err(Error::Budget);
        }
        let next = self.generation.checked_add(1).ok_or(Error::Budget)?;
        let old = self.outbox.insert(id.clone(), bytes);
        self.generation = next;
        if let Err(e) = self.persist() {
            match old {
                Some(b) => {
                    self.outbox.insert(id, b);
                }
                None => {
                    self.outbox.remove(&id);
                }
            }
            self.generation -= 1;
            self.stopped = true;
            return Err(e);
        }
        Ok(())
    }
    pub fn record_retry(&mut self, id: String, status: u64) -> Result<()> {
        self.ensure_live()?;
        let next = self.generation.checked_add(1).ok_or(Error::Budget)?;
        let old = self.retry.insert(id.clone(), status);
        self.generation = next;
        if let Err(e) = self.persist() {
            match old {
                Some(s) => {
                    self.retry.insert(id, s);
                }
                None => {
                    self.retry.remove(&id);
                }
            }
            self.generation -= 1;
            self.stopped = true;
            return Err(e);
        }
        Ok(())
    }
    pub fn retain_evidence(&mut self, m: SignedMessage, keys: &dyn KeyVerifier) -> Result<()> {
        self.ensure_live()?;
        m.authenticate(keys)?;
        let next = self.generation.checked_add(1).ok_or(Error::Budget)?;
        let id = (m.id()?, hash(b"cbcl/checkpoint/evidence/v1", &m.encode()));
        let old = self.client.evidence.clone();
        Arc::make_mut(&mut self.client).evidence.insert(id, m);
        self.generation = next;
        if let Err(e) = self.persist() {
            Arc::make_mut(&mut self.client).evidence = old;
            self.generation -= 1;
            self.stopped = true;
            return Err(e);
        }
        Ok(())
    }
    fn ensure_live(&self) -> Result<()> {
        if self.stopped {
            Err(Error::Invalid(
                "ambiguous persistence failure; recover before writing",
            ))
        } else {
            Ok(())
        }
    }
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PersistFault {
    BeforeWrite,
    AfterWrite,
    AfterSync,
    AfterRename,
    AfterDirectorySync,
    Pause(Duration),
}
#[cfg(test)]
impl DurableClient {
    pub(crate) fn inject_failure(&mut self, fault: PersistFault) {
        self.fault = Some(fault);
    }
    pub(crate) fn archive_for_test(&self) -> &Cache {
        &self.archive
    }
    fn fail_at(&mut self, point: PersistFault) -> Result<()> {
        if self.fault == Some(point) {
            self.fault = None;
            Err(Error::Io("injected durable write failure".into()))
        } else {
            Ok(())
        }
    }
}

/// Compare a shadow candidate with an independently admitted native history.
/// This operation intentionally replays history; it is never on the enabled path.
pub fn compare_shadow(
    prepared: &mut PreparedInstall,
    history: &[SignedMessage],
    c: &Context,
    keys: &dyn KeyVerifier,
) -> Result<()> {
    use cbcl_core::{
        admission::{AdmissionGate, AdmissionMonitor, AdmissionState},
        message::{Message, WrapperType},
        role::{parse_wrapper_cast, AgentKey, Endpoint},
        store::ContentHash,
    };
    struct Gate<'a> {
        messages: &'a BTreeMap<Vec<u8>, SignedMessage>,
        keys: &'a dyn KeyVerifier,
        context: &'a Context,
    }
    impl AdmissionGate for Gate<'_> {
        fn authenticate(&self, m: &Message) -> std::result::Result<ContentHash, String> {
            let signed = self
                .messages
                .get(&crate::codec::message_bytes(m))
                .ok_or("unregistered signed attempt")?;
            crate::member::authenticate_target(signed, self.context, self.keys)
                .map_err(|e| e.to_string())?;
            Ok(ContentHash(signed.id().map_err(|e| e.to_string())?))
        }
    }
    let Message::Wrapped {
        wrapper: WrapperType::WithRoles,
        params,
        ..
    } = c.target_root.message()
    else {
        return Err(Error::Invalid("target cast"));
    };
    let cast =
        parse_wrapper_cast(params, &c.target.roles).map_err(|_| Error::Invalid("target cast"))?;
    let endpoint = if let Some((role, _)) = cast.singleton.iter().next() {
        Endpoint {
            role: role.clone(),
            occupant: None,
        }
    } else {
        let (role, keys) = cast.indexed.iter().next().ok_or(Error::Unsupported)?;
        Endpoint {
            role: role.clone(),
            occupant: Some(AgentKey(keys.first().ok_or(Error::Unsupported)?.0.clone())),
        }
    };
    let messages = std::iter::once(&c.target_root)
        .chain(history)
        .map(|m| (m.encode(), m.clone()))
        .collect::<BTreeMap<_, _>>();
    let mut monitor = AdmissionMonitor::new(
        c.target.clone(),
        endpoint,
        c.target_root.message().clone(),
        Gate {
            messages: &messages,
            keys,
            context: c,
        },
    )
    .map_err(|_| Error::Invalid("shadow admission context"))?;
    monitor.drain_ready();
    for m in history {
        monitor
            .receive(m.message().clone())
            .map_err(|_| Error::Invalid("shadow message receipt"))?;
    }
    monitor.drain_ready();
    let mut index = crate::coverage::Coverage::default();
    let mut acts = Vec::new();
    let mut frontier = std::collections::BTreeSet::new();
    for m in std::iter::once(&c.target_root).chain(history) {
        let id = m.id()?;
        if monitor.state(&ContentHash(id.clone())) != Some(&AdmissionState::Accepted) {
            return Err(Error::Invalid("shadow history not accepted"));
        }
        let act = m.authenticate(keys)?;
        if !index.contains(&id) {
            index.insert(&id);
            frontier.insert(id);
            acts.push(act);
        }
    }
    for a in &acts {
        for p in &a.predecessors {
            frontier.remove(p);
        }
    }
    let expected = cbcl_core::state::fold(
        c.target.state.as_ref().ok_or(Error::Unsupported)?,
        c.target.causal_protocol.as_ref(),
        &acts,
    );
    if prepared.client.context != c.hash()
        || prepared.client.coverage != index.root()
        || prepared.client.frontier != frontier.into_iter().collect::<Vec<_>>()
        || prepared.client.summary.render() != expected
    {
        return Err(Error::Invalid("shadow checkpoint/replay mismatch"));
    }
    prepared.shadow_compared = true;
    Ok(())
}

/// Coalescing publication trigger; only actual successful durable publication clears lag.
pub struct PublicationSchedule {
    pub threshold: usize,
    pub interval: Duration,
    pending: usize,
    since: Option<Instant>,
    in_flight: bool,
}
impl Default for PublicationSchedule {
    fn default() -> Self {
        Self {
            threshold: 32,
            interval: Duration::from_millis(1000),
            pending: 0,
            since: None,
            in_flight: false,
        }
    }
}
impl PublicationSchedule {
    pub fn accepted(&mut self, now: Instant) {
        self.pending = self.pending.saturating_add(1);
        self.since.get_or_insert(now);
    }
    pub fn begin(&mut self, now: Instant, mode: Mode) -> bool {
        if mode != Mode::Enabled {
            return false;
        }
        if self.in_flight || self.pending == 0 {
            return false;
        }
        if self.pending >= self.threshold
            || self
                .since
                .is_some_and(|s| now.saturating_duration_since(s) >= self.interval)
        {
            self.in_flight = true;
            tracing::info!(
                pending = self.pending,
                pending_age_micros = self
                    .since
                    .map(|s| now.saturating_duration_since(s).as_micros() as u64),
                "checkpoint_publication_started"
            );
            true
        } else {
            false
        }
    }
    pub fn complete(&mut self, covered: usize, success: bool, now: Instant) {
        self.in_flight = false;
        tracing::info!(
            success,
            covered,
            pending = self.pending,
            "checkpoint_publication_completed"
        );
        if success {
            self.pending = self.pending.saturating_sub(covered);
            self.since = if self.pending == 0 { None } else { Some(now) }
        }
    }
    pub fn lag(&self) -> usize {
        self.pending
    }
}
pub fn publish(
    cache: &Cache,
    cert: &Certificate,
    c: &Context,
    keys: &dyn KeyVerifier,
    advertise: impl FnOnce(Hash) -> Result<()>,
) -> Result<Hash> {
    cert.verify(c, keys)?;
    tracing::info!(target=%cert.manifest.target,companion=%cert.manifest.companion,endorsements=cert.endorsements.len(),"checkpoint_certificate_verified");
    let bytes = cert.encode(c);
    let id = cache.put(&bytes)?;
    tracing::info!(
        certificate_bytes = bytes.len(),
        endorsements = cert.endorsements.len(),
        "checkpoint_certificate_stored"
    );
    advertise(id)?;
    tracing::info!(blob=%hex(&id),"checkpoint_certificate_advertised");
    Ok(id)
}
