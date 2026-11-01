use crate::{
    metrics::{self, Outcome},
    model::*,
    node::{write_json, write_new},
    transport::{self, DelayedSender, Request, Response, WireMessage},
};
use cbcl_core::quorum::{Certificate, VoteKind};
use ed25519_dalek::SigningKey;
use rand_core::OsRng;
use serde::Serialize;
use serde_json::{json, Value};
use std::{
    collections::{BTreeMap, VecDeque},
    fs::{self, File},
    net::TcpStream,
    path::PathBuf,
    process::{Child, Command, Stdio},
    sync::mpsc,
    thread,
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};

#[derive(Serialize)]
struct Config {
    transactions: usize,
    rate: f64,
    delay_ms: u64,
    timeout_ms: u64,
    max_inflight: usize,
    silent_validators: usize,
    byzantine_mode: ByzantineMode,
    journal_batch_size: usize,
    journal_batch_wait_ms: u64,
    out: PathBuf,
    allow_debug: bool,
}
impl Config {
    fn parse(args: &[String]) -> Result<Option<Self>> {
        let stamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_err(|e| e.to_string())?
            .as_nanos();
        let mut c = Self {
            transactions: 200,
            rate: 100.0,
            delay_ms: 0,
            timeout_ms: 5000,
            max_inflight: 1024,
            silent_validators: 0,
            byzantine_mode: ByzantineMode::None,
            journal_batch_size: 64,
            journal_batch_wait_ms: 1,
            out: std::env::temp_dir()
                .join(format!("cbcl-quorum-e2e-{}-{stamp}", std::process::id())),
            allow_debug: false,
        };
        let mut it = args.iter();
        while let Some(flag) = it.next() {
            if flag == "--help" {
                println!("cbcl-quorum-e2e [--transactions N] [--rate TPS] [--delay-ms ONE_WAY] [--timeout-ms MS] [--max-inflight N] [--silent-validators 0..4] [--byzantine-mode none|withhold|equivocate|invalid-flood] [--journal-batch-size 1..128] [--journal-batch-wait-ms 0..10] [--out NEW_DIRECTORY] [--allow-debug]");
                return Ok(None);
            }
            if flag == "--allow-debug" {
                c.allow_debug = true;
                continue;
            }
            let value = it
                .next()
                .ok_or_else(|| format!("missing value for {flag}"))?;
            let integer = || {
                value
                    .parse::<usize>()
                    .map_err(|_| format!("invalid integer for {flag}"))
            };
            match flag.as_str() {
                "--transactions" => c.transactions = integer()?,
                "--rate" => c.rate = value.parse().map_err(|_| "invalid rate")?,
                "--delay-ms" => c.delay_ms = integer()? as u64,
                "--timeout-ms" => c.timeout_ms = integer()? as u64,
                "--max-inflight" => c.max_inflight = integer()?,
                "--silent-validators" => c.silent_validators = integer()?,
                "--byzantine-mode" => {
                    c.byzantine_mode = match value.as_str() {
                        "none" => ByzantineMode::None,
                        "withhold" => ByzantineMode::Withhold,
                        "equivocate" => ByzantineMode::Equivocate,
                        "invalid-flood" => ByzantineMode::InvalidFlood,
                        _ => return Err("unknown Byzantine mode".into()),
                    }
                }
                "--journal-batch-size" => c.journal_batch_size = integer()?,
                "--journal-batch-wait-ms" => c.journal_batch_wait_ms = integer()? as u64,
                "--out" => c.out = value.into(),
                _ => return Err(format!("unknown option {flag}")),
            }
        }
        if c.transactions == 0
            || c.transactions > 100_000
            || !c.rate.is_finite()
            || c.rate <= 0.0
            || c.transactions as f64 / c.rate > 86400.0
            || !(1000..=60000).contains(&c.timeout_ms)
            || c.delay_ms > 10000
            || c.max_inflight == 0
            || c.max_inflight > 100_000
            || c.silent_validators > 4
            || !(1..=128).contains(&c.journal_batch_size)
            || c.journal_batch_wait_ms > 10
        {
            return Err("require 1..100000 transactions/inflight, finite positive rate, <=24h offered duration, timeout 1000..60000ms, delay <=10000ms, and 0..4 silent validators".into());
        }
        if cfg!(debug_assertions) && !c.allow_debug {
            return Err(
                "use --release for measurements, or --allow-debug for harness checks".into(),
            );
        }
        if c.byzantine_mode != ByzantineMode::None && c.silent_validators != 0 {
            return Err("Byzantine mode and silent validators cannot be combined".into());
        }
        Ok(Some(c))
    }
}
struct Children(Vec<Child>);
impl Drop for Children {
    fn drop(&mut self) {
        for child in &mut self.0 {
            if !matches!(child.try_wait(), Ok(Some(_))) {
                let _ = child.kill();
            }
            let _ = child.wait();
        }
    }
}
struct Pending {
    sequence: usize,
    started: Instant,
    submitted_ms: f64,
    lateness_ms: f64,
    operation: BTreeMap<String, VerifiedVote>,
    effects: BTreeMap<String, VerifiedVote>,
    effects_requested: bool,
    effects_started: Option<Instant>,
    errors: usize,
}
// Fixed timeout + monotonic submissions means deadlines arrive in FIFO order.
// Completed entries are discarded lazily. The sequence binds a timer to the
// exact submission, so an old timer cannot expire a reused transaction ID.
struct Expiration {
    deadline: Instant,
    id: String,
    sequence: usize,
}
#[derive(Default)]
struct Deadlines(VecDeque<Expiration>);
impl Deadlines {
    fn insert(&mut self, deadline: Instant, id: String, sequence: usize) {
        debug_assert!(self.0.back().map_or(true, |old| old.deadline <= deadline));
        self.0.push_back(Expiration {
            deadline,
            id,
            sequence,
        });
    }
    fn pop_due(&mut self, now: Instant) -> Option<Expiration> {
        if self.0.front().is_some_and(|entry| entry.deadline <= now) {
            self.0.pop_front()
        } else {
            None
        }
    }
}
fn collect_expired(
    pending: &mut BTreeMap<String, Pending>,
    deadlines: &mut Deadlines,
    rows: &mut Vec<Outcome>,
    now: Instant,
) {
    while let Some(entry) = deadlines.pop_due(now) {
        if pending
            .get(&entry.id)
            .is_some_and(|p| p.sequence == entry.sequence)
        {
            let p = pending.remove(&entry.id).expect("matching pending timeout");
            rows.push(outcome(entry.id, p, None, None));
        }
    }
}
fn elapsed_ms(t: Instant) -> f64 {
    t.elapsed().as_secs_f64() * 1000.0
}
fn send_all(senders: &[DelayedSender], request: &Request) -> usize {
    senders.iter().filter(|s| s.send(request).is_err()).count()
}
fn outcome(
    id: String,
    pending: Pending,
    finality_ms: Option<f64>,
    certificate: Option<Certificate>,
) -> Outcome {
    Outcome {
        sequence: pending.sequence,
        id,
        status: if finality_ms.is_some() {
            "finalized"
        } else {
            "stalled"
        }
        .into(),
        submitted_ms: Some(pending.submitted_ms),
        finality_ms,
        scheduler_lateness_ms: pending.lateness_ms,
        errors: pending.errors,
        effects_certificate: certificate,
    }
}
pub fn run(args: &[String]) -> Result<()> {
    let Some(mut config) = Config::parse(args)? else {
        return Ok(());
    };
    let mut builder = fs::DirBuilder::new();
    #[cfg(unix)]
    {
        use std::os::unix::fs::DirBuilderExt;
        builder.mode(0o700);
    }
    builder
        .create(&config.out)
        .map_err(|e| format!("output directory must be new: {e}"))?;
    config.out = config.out.canonicalize().map_err(|e| e.to_string())?;
    let executable = std::env::current_exe().map_err(|e| e.to_string())?;
    let treasury = SigningKey::generate(&mut OsRng);
    let alice = SigningKey::generate(&mut OsRng);
    let bob = SigningKey::generate(&mut OsRng);
    let validator_keys: Vec<_> = (0..4).map(|_| SigningKey::generate(&mut OsRng)).collect();
    let mut public_keys = BTreeMap::new();
    for (id, key) in [("@treasury", &treasury), ("@alice", &alice), ("@bob", &bob)] {
        public_keys.insert(id.into(), key.verifying_key().to_bytes());
    }
    for (id, key) in VALIDATORS.iter().zip(&validator_keys) {
        public_keys.insert((*id).into(), key.verifying_key().to_bytes());
    }
    let root=sign_act(parse_act(&format!("(with-roles ((organizer @treasury) (seller @alice @bob)) (signed @treasury (hello :thread \"{THREAD}\" :caused-by begin)))"),"@treasury")?,&treasury);
    let open=sign_act(parse_act(&format!("(signed @treasury (lang collective-tickets (open (@alice @bob @treasury) :available 1000000000 :from @treasury :thread \"{THREAD}\" :caused-by {})))",root.act.address),"@treasury")?,&treasury);
    let setup = Setup {
        public_keys,
        genesis: vec![root, open],
        transactions: config.transactions,
        delay_ms: config.delay_ms,
        silent_validators: config.silent_validators,
        byzantine_mode: config.byzantine_mode,
        queue_capacity: config.max_inflight * 4 + 16,
        journal_batch_size: config.journal_batch_size,
        journal_batch_wait_ms: config.journal_batch_wait_ms,
    };
    write_json(&config.out.join("public-setup.json"), &setup)?;
    let auth = Auth::new(&setup)?;
    let ctx = context(&setup, &auth)?;
    let mut children = Children(vec![]);
    let mut ready = Vec::new();
    let mut paths = Vec::new();
    for (index, key) in validator_keys.iter().enumerate() {
        let dir = config.out.join(format!("v{index}"));
        fs::create_dir(&dir).map_err(|e| e.to_string())?;
        let path = dir.join("config.json");
        write_json(
            &path,
            &NodeConfig {
                setup: setup.clone(),
                index,
                secret: key.to_bytes(),
            },
        )?;
        let log = File::create(dir.join("process.log")).map_err(|e| e.to_string())?;
        let child = Command::new(&executable)
            .arg("validator")
            .arg("--config")
            .arg(&path)
            .stdout(Stdio::from(log.try_clone().map_err(|e| e.to_string())?))
            .stderr(Stdio::from(log))
            .spawn()
            .map_err(|e| e.to_string())?;
        children.0.push(child);
        paths.push(path);
    }
    let boot = Instant::now();
    for (index, child) in children.0.iter_mut().enumerate() {
        let path = config.out.join(format!("v{index}/ready.json"));
        while !path.exists() {
            if let Some(status) = child.try_wait().map_err(|e| e.to_string())? {
                return Err(format!(
                    "validator {index} exited during startup: {status}; see {}",
                    config.out.display()
                ));
            }
            if boot.elapsed() > Duration::from_secs(20) {
                return Err("validator startup timed out".into());
            }
            thread::sleep(Duration::from_millis(10));
        }
        let value: Value = serde_json::from_slice(&fs::read(path).map_err(|e| e.to_string())?)
            .map_err(|e| e.to_string())?;
        if value["context"] != ctx.id() {
            return Err("validator context mismatch".into());
        }
        ready.push(value);
    }
    let (events_tx, events_rx) = mpsc::channel();
    let mut senders = Vec::new();
    let mut writers = Vec::new();
    let mut readers = Vec::new();
    let mut transport_metrics = Vec::new();
    for (index, value) in ready.iter().enumerate() {
        let mut stream =
            TcpStream::connect(value["address"].as_str().ok_or("missing ready address")?)
                .map_err(|e| e.to_string())?;
        stream.set_nodelay(true).map_err(|e| e.to_string())?;
        let (sender, writer) = transport::writer(
            stream.try_clone().map_err(|e| e.to_string())?,
            Duration::from_millis(config.delay_ms),
            setup.queue_capacity,
        )?;
        transport_metrics.push(sender.metrics());
        senders.push(sender);
        writers.push(writer);
        let tx = events_tx.clone();
        readers.push(thread::spawn(move || loop {
            let response = transport::read_profiled::<Response>(&mut stream);
            let done = matches!(
                &response,
                Err(_)
                    | Ok(transport::Received {
                        value: Response::Stopped { .. },
                        ..
                    })
            );
            if tx.send((index, response)).is_err() || done {
                break;
            }
        }));
    }
    drop(events_tx);
    let start = Instant::now();
    let mut first_submission = None;
    let timeout = Duration::from_millis(config.timeout_ms);
    let mut next = 0;
    let mut pending: BTreeMap<String, Pending> = BTreeMap::new();
    let mut deadlines = Deadlines::default();
    let mut rows = Vec::new();
    let mut stopped = BTreeMap::new();
    let mut invalid_votes = 0;
    let mut verified_cancel_votes_ignored = 0;
    let mut transport_errors = 0;
    let mut error_samples = Vec::new();
    let mut offered_end = start;
    let mut response_queues = crate::profile::QueueCosts::default();
    let event_service = std::cell::RefCell::new(crate::profile::PhaseService::default());
    let mut timeout_collection = crate::profile::Samples::default();
    let mut submit_service = crate::profile::Samples::default();
    let mut operation_round = crate::profile::Samples::default();
    let mut effects_round = crate::profile::Samples::default();
    while rows.len() < config.transactions {
        let due = start + Duration::from_secs_f64(next as f64 / config.rate);
        if next < config.transactions && Instant::now() >= due {
            let sequence = next;
            next += 1;
            let lateness = Instant::now().duration_since(due).as_secs_f64() * 1000.0;
            if pending.len() >= config.max_inflight {
                rows.push(Outcome {
                    sequence,
                    id: String::new(),
                    status: "client_overload".into(),
                    submitted_ms: None,
                    finality_ms: None,
                    scheduler_lateness_ms: lateness,
                    errors: 0,
                    effects_certificate: None,
                });
            } else {
                let generation = crate::profile::QUEUE_DIAGNOSTICS.then(Instant::now);
                let signed = transaction(&setup, &ctx, sequence, &alice)?;
                let id = signed.act.address.clone();
                let submitted = Instant::now();
                first_submission.get_or_insert(submitted);
                let failures = send_all(&senders, &Request::Operation { signed });
                transport_errors += failures;
                deadlines.insert(submitted + timeout, id.clone(), sequence);
                pending.insert(
                    id,
                    Pending {
                        sequence,
                        started: submitted,
                        submitted_ms: submitted.duration_since(start).as_secs_f64() * 1000.0,
                        lateness_ms: lateness,
                        operation: BTreeMap::new(),
                        effects: BTreeMap::new(),
                        effects_requested: false,
                        effects_started: None,
                        errors: failures,
                    },
                );
                if let Some(start) = generation {
                    submit_service.record(start)
                }
            }
            if next == config.transactions {
                offered_end = Instant::now();
            }
        }
        let scan_start = crate::profile::QUEUE_DIAGNOSTICS.then(Instant::now);
        collect_expired(&mut pending, &mut deadlines, &mut rows, Instant::now());
        if let Some(start) = scan_start {
            timeout_collection.record(start)
        }
        if rows.len() == config.transactions {
            break;
        }
        let wait = if next < config.transactions {
            (start + Duration::from_secs_f64(next as f64 / config.rate))
                .saturating_duration_since(Instant::now())
                .min(Duration::from_millis(2))
        } else {
            Duration::from_millis(2)
        };
        let (index, event) = match events_rx.recv_timeout(wait) {
            Ok(event) => event,
            Err(std::sync::mpsc::RecvTimeoutError::Timeout) => continue,
            Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => {
                thread::sleep(Duration::from_millis(1));
                continue;
            }
        };
        let event = event.map(|m| {
            if let Some(decoded) = m.decoded_at {
                response_queues.receive(m.value.phase(), decoded, m.decode_ms);
            }
            m.value
        });
        let phase = event.as_ref().map(|m| m.phase()).unwrap_or("read_error");
        let _event_service = crate::profile::QUEUE_DIAGNOSTICS
            .then(|| crate::profile::PhaseScope::new(&event_service, phase));
        match event {
            Ok(Response::Vote { vote }) => {
                let id = vote.payload.clone();
                let mut final_certificate = None;
                if let Some(p) = pending.get_mut(&id) {
                    if p.started.elapsed() >= timeout {
                        continue;
                    }
                    if vote.signer != VALIDATORS[index] {
                        invalid_votes += 1;
                        continue;
                    }
                    let kind = vote.kind;
                    let signer = vote.signer.clone();
                    let verified = match VerifiedVote::verify(&auth, &ctx, vote, kind, &id) {
                        Ok(vote) => vote,
                        Err(_) => {
                            invalid_votes += 1;
                            continue;
                        }
                    };
                    if kind == VoteKind::Cancel {
                        verified_cancel_votes_ignored += 1;
                    }
                    match kind {
                        VoteKind::Operation if !p.effects_requested => {
                            p.operation.insert(signer, verified);
                            if p.operation.len() >= ctx.committee().quorum {
                                let cert = certificate_from_verified(
                                    &auth,
                                    &ctx,
                                    VoteKind::Operation,
                                    &id,
                                    &p.operation,
                                )?;
                                if crate::profile::QUEUE_DIAGNOSTICS {
                                    operation_round.record(p.started);
                                    p.effects_started = Some(Instant::now());
                                }
                                let errors =
                                    send_all(&senders, &Request::Effects { certificate: cert });
                                p.errors += errors;
                                transport_errors += errors;
                                p.effects_requested = true;
                            }
                        }
                        VoteKind::Effects if p.effects_requested => {
                            p.effects.insert(signer, verified);
                            if p.effects.len() >= ctx.committee().quorum {
                                let cert = certificate_from_verified(
                                    &auth,
                                    &ctx,
                                    VoteKind::Effects,
                                    &id,
                                    &p.effects,
                                )?;
                                if let Some(t) = p.effects_started {
                                    effects_round.record(t);
                                }
                                let latency = elapsed_ms(p.started);
                                if latency <= config.timeout_ms as f64 {
                                    final_certificate = Some((latency, cert));
                                }
                            }
                        }
                        _ => (),
                    }
                }
                if let Some((latency, certificate)) = final_certificate {
                    let p = pending.remove(&id).expect("completed transaction");
                    rows.push(outcome(id, p, Some(latency), Some(certificate.clone())));
                    transport_errors += send_all(&senders, &Request::Final { certificate });
                }
            }
            Ok(Response::Error { id, message }) => {
                if let Some(p) = pending.get_mut(&id) {
                    p.errors += 1;
                }
                if error_samples.len() < 16 {
                    error_samples.push(json!({"validator":index,"id":id,"message":message}));
                }
            }
            Ok(Response::Stopped {
                pid,
                finalized,
                value,
                events,
                syncs,
                profile,
            }) => {
                stopped.insert(index,json!({"pid":pid,"finalized":finalized,"value":value,"events":events,"syncs":syncs,"profile":profile}));
            }
            Err(error) => {
                transport_errors += 1;
                if error_samples.len() < 16 {
                    error_samples.push(json!({"validator":index,"message":error}));
                }
            }
        }
    }
    let measurement_seconds = first_submission.unwrap_or(start).elapsed().as_secs_f64();
    let offering_seconds = offered_end.duration_since(start).as_secs_f64();
    for sender in &senders {
        let _ = sender.send(&Request::Stop);
    }
    let drain = Instant::now();
    let grace = Duration::from_millis(config.timeout_ms + 2 * config.delay_ms + 3000);
    while stopped.len() < 4 && drain.elapsed() < grace {
        if let Ok((
            i,
            Ok(transport::Received {
                value:
                    Response::Stopped {
                        pid,
                        finalized,
                        value,
                        events,
                        syncs,
                        profile,
                    },
                ..
            }),
        )) = events_rx.recv_timeout(Duration::from_millis(10))
        {
            stopped.insert(i,json!({"pid":pid,"finalized":finalized,"value":value,"events":events,"syncs":syncs,"profile":profile}));
        }
    }
    drop(senders);
    // Stop acknowledgements precede child exit by at most transport cleanup.
    let exit_wait = Instant::now();
    for child in &mut children.0 {
        while child.try_wait().map_err(|e| e.to_string())?.is_none() && exit_wait.elapsed() < grace
        {
            thread::sleep(Duration::from_millis(5));
        }
        if child.try_wait().map_err(|e| e.to_string())?.is_none() {
            let _ = child.kill();
        }
        let _ = child.wait();
    }
    for reader in readers {
        let _ = reader.join();
    }
    for writer in writers {
        let _ = writer.join();
    }
    let mut recovery = Vec::new();
    let mut recovery_ok = true;
    for (i, path) in paths.iter().enumerate() {
        let result = Command::new(&executable)
            .arg("recover")
            .arg("--config")
            .arg(path)
            .output()
            .map_err(|e| e.to_string())?;
        let value = serde_json::from_slice::<Value>(&result.stdout).unwrap_or(Value::Null);
        let matches = stopped.get(&i).is_some_and(|old| {
            ["finalized", "value", "events"]
                .iter()
                .all(|k| old[*k] == value[*k])
        });
        let passed = result.status.success() && matches;
        recovery_ok &= passed;
        recovery.push(json!({"validator":i,"passed":passed,"state":value,"error":if passed{String::new()}else{String::from_utf8_lossy(&result.stderr).into_owned()}}));
    }
    rows.sort_by_key(|r| r.sequence);
    let mut traces = Vec::new();
    for row in &rows {
        serde_json::to_writer(&mut traces, row).map_err(|e| e.to_string())?;
        traces.push(b'\n');
    }
    write_new(&config.out.join("transactions.jsonl"), &traces)?;
    let git = Command::new("git")
        .arg("-C")
        .arg(env!("CARGO_MANIFEST_DIR"))
        .args(["rev-parse", "HEAD"])
        .output()
        .ok();
    let dirty = Command::new("git")
        .arg("-C")
        .arg(env!("CARGO_MANIFEST_DIR"))
        .args(["status", "--porcelain"])
        .output()
        .ok()
        .map(|o| !o.stdout.is_empty());
    let report = json!({"schema":"cbcl-quorum-e2e/v1","config":config,"client_pid":std::process::id(),"validators":ready,
        "context":ctx.id(),"quorum":ctx.committee().quorum,
        "build":{"profile":env!("BENCH_PROFILE"),"opt_level":env!("BENCH_OPT_LEVEL"),"target":env!("BENCH_TARGET"),"rustc":env!("BENCH_RUSTC"),"debug_assertions":cfg!(debug_assertions),"git_commit":git.map(|o|String::from_utf8_lossy(&o.stdout).trim().to_owned()),"working_tree_dirty":dirty},
        "host":{"os":std::env::consts::OS,"arch":std::env::consts::ARCH,"logical_cpus":thread::available_parallelism().map(|n|n.get()).ok()},
        "metrics":metrics::summarize(&rows,config.timeout_ms,measurement_seconds),
        "client_signature_verification":auth.costs.borrow().verify.report(),
        "client_certificate_policy":"construct_from_strictly_verified_votes",
        "client_profile":{"queue_diagnostics_enabled":crate::profile::QUEUE_DIAGNOSTICS,"response_queues":response_queues.report(),"event_service_ms":event_service.borrow().report(),"timeout_collection_ms":timeout_collection.report(),"submit_service_ms":submit_service.report(),"operation_round_ms":operation_round.report(),"effects_round_ms":effects_round.report(),"request_transports":transport_metrics.iter().map(|m|m.report()).collect::<Vec<_>>()},
        "offering_window_seconds":offering_seconds,"invalid_votes":invalid_votes,"verified_cancel_votes_ignored":verified_cancel_votes_ignored,"transport_errors":transport_errors,"error_samples":error_samples,
        "validator_observations":stopped,"recovery":recovery,"recovery_passed":recovery_ok,
        "measurement_definition":"Signed transaction submission before transport enqueue to client receipt and effects QC verification from strict Ed25519-verified immutable votes and quorum/domain/key-binding checks; client generation/signing excluded; network queues, fixed per-direction delay, validator validation/signing and group sync_all before votes included.",
        "limits":"One host, loopback TCP, fixed one-way delay without packet-loss/bandwidth modelling; one hot collective pool; bounded journal group commit; filesystem/device sync_all guarantees assumed. Finalized latency percentiles are conditional; all-submitted quantiles include right-censored stalls."});
    write_json(&config.out.join("report.json"), &report)?;
    println!(
        "{}",
        serde_json::to_string_pretty(&report).map_err(|e| e.to_string())?
    );
    if !recovery_ok {
        return Err(format!(
            "recovery audit failed; inspect {}",
            config.out.display()
        ));
    }
    Ok(())
}

#[cfg(test)]
mod deadline_tests {
    use super::*;
    fn pending(sequence: usize, started: Instant) -> Pending {
        Pending {
            sequence,
            started,
            submitted_ms: 0.,
            lateness_ms: 0.,
            operation: BTreeMap::new(),
            effects: BTreeMap::new(),
            effects_requested: false,
            effects_started: None,
            errors: 0,
        }
    }
    #[test]
    fn deadlines_expire_at_boundary_and_ignore_completed_or_reused_ids() {
        let now = Instant::now();
        let mut timers = Deadlines::default();
        let mut active = BTreeMap::new();
        let mut rows = Vec::new();
        timers.insert(now + Duration::from_millis(10), "reused".into(), 1);
        timers.insert(now + Duration::from_millis(11), "completed".into(), 2);
        timers.insert(now + Duration::from_millis(12), "due".into(), 3);
        timers.insert(now + Duration::from_millis(20), "reused".into(), 4);
        active.insert("due".into(), pending(3, now + Duration::from_millis(2)));
        active.insert("reused".into(), pending(4, now + Duration::from_millis(10)));
        collect_expired(
            &mut active,
            &mut timers,
            &mut rows,
            now + Duration::from_millis(12) - Duration::from_nanos(1),
        );
        assert!(rows.is_empty());
        assert_eq!(active.len(), 2);
        collect_expired(
            &mut active,
            &mut timers,
            &mut rows,
            now + Duration::from_millis(12),
        );
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].sequence, 3);
        assert_eq!(rows[0].status, "stalled");
        assert!(rows[0].effects_certificate.is_none());
        assert!(active.contains_key("reused"));
        collect_expired(
            &mut active,
            &mut timers,
            &mut rows,
            now + Duration::from_millis(20),
        );
        assert!(active.is_empty());
        assert_eq!(rows[1].sequence, 4);
        assert!(timers.0.is_empty());
    }
    #[test]
    fn ordered_expiration_matches_original_scan_with_completions_and_id_reuse() {
        let start = Instant::now();
        let timeout = Duration::from_millis(10);
        let mut timers = Deadlines::default();
        let mut actual = BTreeMap::new();
        let mut reference = BTreeMap::new();
        let mut rows = Vec::new();
        for tick in 0..50 {
            let now = start + Duration::from_millis(tick);
            if tick < 20 && tick % 2 == 0 {
                let id = format!("id-{}", tick % 6);
                let sequence = tick as usize;
                // Superseding an ID removes its earlier pending submission.
                actual.insert(id.clone(), pending(sequence, now));
                reference.insert(id.clone(), (sequence, now));
                timers.insert(now + timeout, id, sequence);
            }
            if tick == 7 || tick == 13 {
                actual.remove("id-2");
                reference.remove("id-2");
            }
            let old_rows = rows.len();
            collect_expired(&mut actual, &mut timers, &mut rows, now);
            let expected: Vec<_> = reference
                .iter()
                .filter(|(_, (_, submitted))| now.duration_since(*submitted) >= timeout)
                .map(|(id, (sequence, _))| (id.clone(), *sequence))
                .collect();
            let mut expected_sequences: Vec<_> =
                expected.iter().map(|(_, sequence)| *sequence).collect();
            expected_sequences.sort_unstable();
            for (id, _) in expected {
                reference.remove(&id);
            }
            let mut observed: Vec<_> = rows[old_rows..].iter().map(|r| r.sequence).collect();
            observed.sort_unstable();
            assert_eq!(observed, expected_sequences, "tick {tick}");
            assert_eq!(
                actual.keys().collect::<Vec<_>>(),
                reference.keys().collect::<Vec<_>>(),
                "tick {tick}"
            );
        }
        assert!(actual.is_empty() && timers.0.is_empty());
    }
}
