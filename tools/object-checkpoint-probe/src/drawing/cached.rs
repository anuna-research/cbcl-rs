//! Cached checkpoint lifecycle experiment; no production API or global freshness.
use super::*;
use std::{
    fs,
    io::{Read, Write},
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

const DOMAIN: &str = "cbcl-experimental-drawing-cached-certificate-v2";
const MAX_BLOB: usize = 16 * 1024 * 1024;
const MAX_OFFERS: usize = 8;
const MAX_TAIL_STEPS: usize = 2048;
const MAX_OFFER_BYTES: usize = 4 * 1024 * 1024;
const MAX_FRONTIER: usize = 4096;

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Manifest {
    context: Hash,
    coverage: Hash,
    summary: Hash,
    frontier: Vec<String>,
}
impl Manifest {
    fn cut(&self) -> Cut {
        Cut {
            context: self.context,
            coverage: self.coverage,
            summary: self.summary,
        }
    }
    fn preimage(&self) -> Vec<u8> {
        encoded(&(DOMAIN, self))
    }
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Certificate {
    manifest: Manifest,
    state: Summary,
    votes: Vec<Vote>,
}
impl Certificate {
    fn open(&self, config: &Config<'_>) -> Result<Client> {
        if self.manifest.context != config.context || config.roster.len() != 4 {
            return Err("foreign context or roster".into());
        }
        canonical(&self.manifest.frontier)?;
        if self.votes.len() < 3 || self.votes.len() > 4 {
            return Err("cached checkpoint requires three of four".into());
        }
        let mut seen = BTreeSet::new();
        for v in &self.votes {
            if !seen.insert(v.member) {
                return Err("duplicate endorsement".into());
            }
            let key = config.roster.get(v.member).ok_or("untrusted member")?;
            let sig =
                Signature::from_slice(&v.signature).map_err(|_| "bad endorsement encoding")?;
            key.verify_strict(&self.manifest.preimage(), &sig)
                .map_err(|_| "invalid cached endorsement")?;
        }
        Client::new(self.state.clone(), &self.manifest.cut(), config)
    }
}
fn canonical(frontier: &[String]) -> Result<()> {
    if frontier.is_empty()
        || frontier.len() > MAX_FRONTIER
        || frontier.windows(2).any(|p| p[0] >= p[1])
    {
        return Err("frontier must be nonempty, sorted and unique".into());
    }
    if frontier.iter().any(|s| {
        !s.strip_prefix("sha256:").is_some_and(|h| {
            h.len() == 64
                && h.bytes()
                    .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
        })
    }) {
        return Err("invalid native frontier identity".into());
    }
    Ok(())
}
fn frontier(wires: impl IntoIterator<Item = Wire>) -> Vec<String> {
    let wires: Vec<_> = wires.into_iter().collect();
    let mut heads: BTreeSet<_> = wires.iter().map(Wire::id).collect();
    for w in wires {
        for p in predecessors(&w.message) {
            heads.remove(&p);
        }
    }
    heads.into_iter().collect()
}

/// Each member's accepted view is established independently by the real monitor.
struct Member {
    index: usize,
    context: Hash,
    accepted: BTreeMap<String, Wire>,
}
impl Member {
    fn new(index: usize, f: &Fixture, received: &[Wire]) -> Result<Self> {
        if index >= 4 {
            return Err("unknown member index".into());
        }
        let monitor = replay(f, received)?;
        let accepted = std::iter::once(&f.root)
            .chain(received)
            .filter(|w| monitor.state(&ContentHash(w.id())) == Some(&AdmissionState::Accepted))
            .map(|w| (w.id(), w.clone()))
            .collect();
        Ok(Self {
            index,
            context: Config::new(f).context,
            accepted,
        })
    }
    fn heads(&self) -> Vec<String> {
        frontier(self.accepted.values().cloned())
    }
    fn derive(&self, heads: &[String], config: &Config<'_>) -> Result<Producer> {
        if self.context != config.context {
            return Err("member history belongs to another context".into());
        }
        canonical(heads)?;
        let mut todo = heads.to_vec();
        let mut selected = BTreeSet::new();
        while let Some(id) = todo.pop() {
            if !selected.insert(id.clone()) {
                continue;
            }
            let w = self
                .accepted
                .get(&id)
                .ok_or("proposed cut has an unknown/unaccepted branch")?;
            todo.extend(predecessors(&w.message));
        }
        if !selected.contains(&config.fixture.root.id()) {
            return Err("cut is not rooted in this object".into());
        }
        let wires: Vec<_> = selected
            .iter()
            .map(|id| self.accepted[id].clone())
            .collect();
        if frontier(wires.clone()) != heads {
            return Err("redundant/noncanonical cut frontier".into());
        }
        let mut p = Producer::new(config.fixture);
        let mut processed = BTreeSet::from([config.fixture.root.id()]);
        let mut pending: Vec<_> = wires
            .iter()
            .filter(|w| w.id() != config.fixture.root.id())
            .cloned()
            .collect();
        while !pending.is_empty() {
            let i = pending
                .iter()
                .position(|w| {
                    predecessors(&w.message)
                        .iter()
                        .all(|id| processed.contains(id))
                })
                .ok_or("cut is not causally closed")?;
            let w = pending.remove(i);
            let id = w.act().address;
            p.coverage.insert(&id);
            if let Some(op) = projection(&w)? {
                let refs = op
                    .replaces
                    .iter()
                    .map(|r| p.coverage.proof(r))
                    .collect::<Vec<_>>();
                p.state.apply(&op, &refs, p.coverage.root())?;
            }
            processed.insert(w.id());
        }
        let acts: Vec<_> = wires
            .iter()
            .filter(|w| w.id() != config.fixture.root.id())
            .map(Wire::act)
            .collect();
        let expected = state::render_json(&state::fold(
            config.fixture.dialect.state.as_ref().unwrap(),
            config.fixture.dialect.causal_protocol.as_ref(),
            &acts,
        ));
        if render_state(&p.state, &config.fixture.dialect) != expected {
            return Err("summary differs from full fold".into());
        }
        Ok(p)
    }
    fn propose(&self, config: &Config<'_>) -> Result<(Manifest, Producer)> {
        let heads = self.heads();
        let p = self.derive(&heads, config)?;
        Ok((
            Manifest {
                context: config.context,
                coverage: p.coverage.root(),
                summary: p.state.hash(),
                frontier: heads,
            },
            p,
        ))
    }
    fn endorse(&self, manifest: &Manifest, config: &Config<'_>, key: &SigningKey) -> Result<Vote> {
        if manifest.context != config.context
            || config.roster.get(self.index) != Some(&key.verifying_key())
        {
            return Err("wrong context or endorsement key".into());
        }
        let p = self.derive(&manifest.frontier, config)?;
        if p.coverage.root() != manifest.coverage || p.state.hash() != manifest.summary {
            return Err("proposal does not match independently derived state".into());
        }
        Ok(Vote {
            member: self.index,
            signature: key.sign(&manifest.preimage()).to_bytes().to_vec(),
        })
    }
}
fn certify(
    manifest: Manifest,
    state: Summary,
    members: &[Member],
    config: &Config<'_>,
) -> Result<Certificate> {
    let votes = members
        .iter()
        .filter_map(|m| {
            m.endorse(&manifest, config, &config.fixture.keys[m.index])
                .ok()
        })
        .collect();
    let cert = Certificate {
        manifest,
        state,
        votes,
    };
    cert.open(config)?;
    Ok(cert)
}

static NEXT: AtomicU64 = AtomicU64::new(0);
/// Real temporary filesystem cache. Only public experiment data is written.
struct Cache {
    dir: PathBuf,
    reads: Cell<usize>,
    bytes: Cell<usize>,
}
impl Cache {
    fn new() -> Self {
        let dir = std::env::temp_dir().join(format!(
            "cbcl-cached-probe-{}-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&dir).unwrap();
        Self {
            dir,
            reads: Cell::new(0),
            bytes: Cell::new(0),
        }
    }
    fn path(&self, id: Hash) -> PathBuf {
        self.dir
            .join(id.iter().map(|b| format!("{b:02x}")).collect::<String>())
    }
    fn publish(&self, cert: &Certificate) -> Result<Hash> {
        let bytes = encoded(cert);
        if bytes.len() > MAX_BLOB {
            return Err("snapshot exceeds experimental byte limit".into());
        }
        let id = digest(b"cached-checkpoint-file-v1", &bytes);
        let tmp = self
            .dir
            .join(format!("upload-{}", NEXT.fetch_add(1, Ordering::Relaxed)));
        let mut file = fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&tmp)
            .map_err(|e| e.to_string())?;
        file.write_all(&bytes).map_err(|e| e.to_string())?;
        file.sync_all().map_err(|e| e.to_string())?;
        fs::rename(tmp, self.path(id)).map_err(|e| e.to_string())?;
        Ok(id)
    }
    fn read(&self, id: Hash) -> Result<Certificate> {
        self.reads.set(self.reads.get() + 1);
        let mut options = fs::OpenOptions::new();
        options.read(true);
        #[cfg(unix)]
        {
            use std::os::unix::fs::OpenOptionsExt;
            options.custom_flags(libc::O_NONBLOCK | libc::O_NOFOLLOW);
        }
        let file = options.open(self.path(id)).map_err(|e| e.to_string())?;
        if !file.metadata().map_err(|e| e.to_string())?.is_file() {
            return Err("cache entry is not a regular file".into());
        }
        let mut bytes = Vec::new();
        file.take(MAX_BLOB as u64 + 1)
            .read_to_end(&mut bytes)
            .map_err(|e| e.to_string())?;
        self.bytes.set(self.bytes.get() + bytes.len());
        if bytes.len() > MAX_BLOB || digest(b"cached-checkpoint-file-v1", &bytes) != id {
            return Err("cache bytes do not match advertised content address".into());
        }
        serde_json::from_slice(&bytes).map_err(|e| e.to_string())
    }
    fn reset(&self) {
        self.reads.set(0);
        self.bytes.set(0);
    }
}
impl Drop for Cache {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.dir);
    }
}

/// Local trusted read-your-history fence, not evidence of globally newest state.
#[derive(Clone, Debug)]
struct Floor {
    context: Hash,
    coverage: Hash,
    frontier: Vec<String>,
}
impl Floor {
    fn at(cert: &Certificate) -> Self {
        Self {
            context: cert.manifest.context,
            coverage: cert.manifest.coverage,
            frontier: cert.manifest.frontier.clone(),
        }
    }
    fn advance(&mut self, step: &Step, client: &Client) {
        let mut heads: BTreeSet<_> = self.frontier.iter().cloned().collect();
        if !step.identity.present {
            for p in predecessors(&step.wire.message) {
                heads.remove(&p);
            }
            heads.insert(step.wire.id());
        }
        self.frontier = heads.into_iter().collect();
        self.coverage = client.coverage;
    }
}
#[derive(Clone)]
struct Offer {
    blob: Hash,
    tail: Vec<Step>,
    floor_proofs: Vec<(String, Proof)>,
}
/// Bound serialized evidence without allocating an attacker-sized JSON buffer.
struct ByteBudget {
    used: usize,
}
impl Write for ByteBudget {
    fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
        if bytes.len() > MAX_OFFER_BYTES - self.used {
            return Err(std::io::Error::other("offer byte budget exceeded"));
        }
        self.used += bytes.len();
        Ok(bytes.len())
    }
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}
fn check_offer(response: &Offer) -> Result<()> {
    if response.tail.len() > MAX_TAIL_STEPS {
        return Err("tail work budget exceeded".into());
    }
    serde_json::to_writer(
        &mut ByteBudget { used: 0 },
        &(&response.tail, &response.floor_proofs),
    )
    .map_err(|e| e.to_string())
}
fn offer(
    blob: Hash,
    mut p: Producer,
    tail: &[Wire],
    archive: &Archive,
    config: &Config<'_>,
    floor: Option<&Floor>,
) -> Result<Offer> {
    let mut known = BTreeSet::new();
    let mut steps = Vec::new();
    for wire in tail {
        steps.push(p.step(wire, archive, &mut known, &config.fixture.root.id())?);
    }
    let floor_proofs = floor.map_or(vec![], |f| {
        f.frontier
            .iter()
            .map(|id| (id.clone(), p.coverage.proof(&address(id))))
            .collect()
    });
    Ok(Offer {
        blob,
        tail: steps,
        floor_proofs,
    })
}
struct Installed {
    client: Client,
    floor: Floor,
    blob: Hash,
    rejected: Vec<String>,
}
fn load(
    cache: &Cache,
    offers: &[Offer],
    config: &Config<'_>,
    floor: Option<&Floor>,
    previous: Option<&Client>,
) -> Result<Installed> {
    if offers.is_empty() || offers.len() > MAX_OFFERS {
        return Err("invalid advertisement count".into());
    }
    if floor.is_some_and(|f| f.context != config.context) {
        return Err("foreign local floor".into());
    }
    if previous.is_some_and(|p| floor.map(|f| f.coverage) != Some(p.coverage)) {
        return Err("previous state needs its matching local floor".into());
    }
    if previous.is_some_and(|p| p.context != config.context) {
        return Err("previous client belongs to another context".into());
    }
    let mut rejected = Vec::new();
    for response in offers {
        let attempt = (|| {
            check_offer(response)?;
            let cert = cache.read(response.blob)?;
            let mut client = cert.open(config)?;
            let mut next = Floor::at(&cert);
            for step in &response.tail {
                if client.admit(step, config)? != VerificationResult::Valid {
                    return Err("tail is unresolved or rejected".into());
                }
                next.advance(step, &client);
            }
            if let Some(floor) = floor {
                if response
                    .floor_proofs
                    .iter()
                    .map(|(id, _)| id)
                    .collect::<Vec<_>>()
                    != floor.frontier.iter().collect::<Vec<_>>()
                {
                    return Err("missing local-floor coverage".into());
                }
                for (id, p) in &response.floor_proofs {
                    if !p.present {
                        return Err("checkpoint plus tail rolls back local history".into());
                    }
                    p.check(client.coverage, &address(id))?;
                }
            } else if !response.floor_proofs.is_empty() {
                return Err("unexpected floor proofs".into());
            }
            // Install atomically only after the fence. Preserve already supplied
            // signed bodies for accountability; these do not refold state.
            if let Some(old) = previous {
                for (id, wire) in &old.signed_bodies {
                    client.store.append(
                        ContentHash(id.clone()),
                        config.thread(),
                        wire.message.clone(),
                    );
                    client.signed_bodies.insert(id.clone(), wire.clone());
                }
            }
            Ok((client, next))
        })();
        match attempt {
            Ok((client, floor)) => {
                return Ok(Installed {
                    client,
                    floor,
                    blob: response.blob,
                    rejected,
                })
            }
            Err(e) => rejected.push(e),
        }
    }
    Err(format!(
        "all cached candidates failed: {}",
        rejected.join("; ")
    ))
}

pub(crate) fn run() {
    let mut rows = Vec::new();
    for n in [120, 600] {
        let f = Fixture::new(n, 8, n - 32);
        let config = Config::new(&f);
        let archive = Archive::new(&f);
        let cache = Cache::new();
        let start = Instant::now();
        let members: Vec<_> = (0..4)
            .map(|i| Member::new(i, &f, if i == 3 { &f.edits[..33] } else { &f.edits }).unwrap())
            .collect();
        let member_build_us = start.elapsed().as_micros();
        let start = Instant::now();
        let (manifest, p) = members[0].propose(&config).unwrap();
        let cert = certify(manifest, p.state.clone(), &members, &config).unwrap();
        let publication_us = start.elapsed().as_micros();
        let start = Instant::now();
        let latest = cache.publish(&cert).unwrap();
        let cache_write_us = start.elapsed().as_micros();
        // Older cached cut is endorsed independently, including by ahead members.
        let old_member = Member::new(0, &f, &f.edits[..33]).unwrap();
        let (old_manifest, old_p) = old_member.propose(&config).unwrap();
        let old_cert = certify(old_manifest, old_p.state.clone(), &members, &config).unwrap();
        let older = cache.publish(&old_cert).unwrap();
        let recent_count = f.edits.len() - 32;
        let recent_member = Member::new(0, &f, &f.edits[..recent_count]).unwrap();
        let (recent_manifest, recent_p) = recent_member.propose(&config).unwrap();
        let recent_cert =
            certify(recent_manifest, recent_p.state.clone(), &members, &config).unwrap();
        let recent = cache.publish(&recent_cert).unwrap();
        let tails = super::tail(&f, n - 32);
        let fast = offer(latest, p.clone(), &tails, &archive, &config, None).unwrap();
        let floor = Floor::at(&cert);
        let mut catchup = f.edits[33..].to_vec();
        catchup.extend(tails.clone());
        let fallback = offer(older, old_p, &catchup, &archive, &config, Some(&floor)).unwrap();
        let mut recent_tail = f.edits[recent_count..].to_vec();
        recent_tail.extend(tails.clone());
        let recent_fallback = offer(
            recent,
            recent_p,
            &recent_tail,
            &archive,
            &config,
            Some(&floor),
        )
        .unwrap();
        let mut all = f.edits.clone();
        all.extend(tails);
        let monitor = replay(&f, &all).unwrap();
        let expected = folded(&f, &monitor, &all);
        for (scenario, offers, fence) in [
            ("latest", vec![fast.clone()], None),
            (
                "latest-missing-recent-fallback",
                vec![
                    Offer {
                        blob: latest,
                        tail: vec![],
                        floor_proofs: vec![],
                    },
                    recent_fallback,
                ],
                Some(&floor),
            ),
            (
                "latest-missing-stale-fallback",
                vec![
                    Offer {
                        blob: latest,
                        tail: vec![],
                        floor_proofs: vec![],
                    },
                    fallback.clone(),
                ],
                Some(&floor),
            ),
        ] {
            if scenario != "latest" && cache.path(latest).exists() {
                fs::remove_file(cache.path(latest)).unwrap();
            }
            let mut times = Vec::new();
            let mut stats = None;
            for _ in 0..3 {
                cache.reset();
                let start = Instant::now();
                let loaded = load(&cache, &offers, &config, fence, None).unwrap();
                let elapsed = start.elapsed().as_micros();
                assert_eq!(render_state(&loaded.client.state, &f.dialect), expected);
                times.push(elapsed);
                stats = Some((
                    loaded.rejected.len(),
                    loaded.client.retained_body_stats(),
                    loaded.floor.frontier.len(),
                    loaded.blob,
                ));
            }
            times.sort();
            let (rejected, retained, heads, used) = stats.unwrap();
            let response = offers.iter().find(|o| o.blob == used).unwrap();
            let loaded_cert = if used == latest {
                &cert
            } else if used == recent {
                &recent_cert
            } else {
                &old_cert
            };
            rows.push(serde_json::json!({"history_edits":n,"scenario":scenario,"latest_certificate_endorsements":cert.votes.len(),"loaded_certificate_endorsements":loaded_cert.votes.len(),"offline_member_lag":n-32,"independent_member_build_us":member_build_us,"proposal_and_independent_endorsements_us":publication_us,"latest_cache_write_sync_us":cache_write_us,"cached_certificate_json_bytes":encoded(loaded_cert).len(),"tail_and_floor_json_bytes":encoded(&(&response.tail,&response.floor_proofs)).len(),"open_median_us":times[1],"cache_read_attempts":cache.reads.get(),"cache_bytes_read":cache.bytes.get(),"rejected_cache_candidates":rejected,"catchup_messages":response.tail.len(),"installed_floor_heads":heads,"retained_signed_bodies":retained.0}));
        }
    }
    println!("{}",serde_json::to_string_pretty(&serde_json::json!({"status":"experimental cached-certificate lifecycle; fixed four-member roster f=1", "timing":"local medians of three certificate filesystem read/decode, verify and already-typed tail admission runs; rendering/assertions excluded; tail decoding, public context and offer preparation excluded; publication costs separately measured", "rows":rows})).unwrap());
}

#[cfg(test)]
mod tests;
