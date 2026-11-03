use crate::{
    journal::DurableJournal,
    model::*,
    transport::{self, Request, Response, WireMessage},
};
use cbcl_core::quorum::{Event, Journal, Replica, VoteKind};
use ed25519_dalek::{Signer, SigningKey};
use serde_json::{json, Value};
use std::{
    fs::{self, File, OpenOptions},
    io::Write,
    net::TcpListener,
    path::Path,
    time::{Duration, Instant},
};

pub fn write_new(path: &Path, bytes: &[u8]) -> Result<()> {
    let mut options = OpenOptions::new();
    options.create_new(true).write(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    let mut file = options.open(path).map_err(|e| e.to_string())?;
    file.write_all(bytes)
        .and_then(|_| file.sync_all())
        .map_err(|e| e.to_string())
}
pub fn write_json(path: &Path, value: &impl serde::Serialize) -> Result<()> {
    write_new(
        path,
        &serde_json::to_vec_pretty(value).map_err(|e| e.to_string())?,
    )
}
pub fn run(path: &Path, recover_only: bool) -> Result<Value> {
    let config: NodeConfig = serde_json::from_slice(&fs::read(path).map_err(|e| e.to_string())?)
        .map_err(|e| e.to_string())?;
    let id = *VALIDATORS
        .get(config.index)
        .ok_or("invalid validator index")?;
    let key = SigningKey::from_bytes(&config.secret);
    if config.setup.public_keys.get(id) != Some(&key.verifying_key().to_bytes()) {
        return Err("validator key mismatch".into());
    }
    let mut auth = Auth::new(&config.setup)?;
    let ctx = context(&config.setup, &auth)?;
    let dir = path.parent().ok_or("missing node directory")?;
    let (mut journal, records) = DurableJournal::open(&dir.join("journal.jsonl"), ctx.id(), id)?;
    for record in records {
        if let Event::Candidate(act) = record.event {
            auth.remember(&SignedAct {
                act,
                signature: record
                    .actor_signature
                    .ok_or("missing persisted actor signature")?,
            });
        }
    }
    let existing = journal.load(ctx.id(), id)?.is_some();
    if recover_only && !existing {
        return Err("missing recovery journal".into());
    }
    let mut replica = if existing {
        Replica::recover(ctx.clone(), id, limits(&config.setup), &journal, &auth)?
    } else {
        Replica::initialize(ctx.clone(), id, limits(&config.setup), &mut journal)?
    };
    let stats = |replica: &Replica, journal: &DurableJournal| -> Result<Value> {
        let view = replica.finalized_view()?;
        Ok(
            json!({"pid":std::process::id(),"validator":id,"finalized":view.finalized.len(),"value":view.value,"events":journal.count(),"syncs":journal.syncs}),
        )
    };
    if recover_only {
        return stats(&replica, &journal);
    }
    let listener = TcpListener::bind("127.0.0.1:0").map_err(|e| e.to_string())?;
    let ready = json!({"pid":std::process::id(),"address":listener.local_addr().map_err(|e|e.to_string())?.to_string(),"context":ctx.id()});
    write_json(&dir.join("ready.tmp"), &ready)?;
    fs::rename(dir.join("ready.tmp"), dir.join("ready.json")).map_err(|e| e.to_string())?;
    #[cfg(unix)]
    File::open(dir)
        .and_then(|d| d.sync_all())
        .map_err(|e| e.to_string())?;
    let (mut incoming, _) = listener.accept().map_err(|e| e.to_string())?;
    incoming.set_nodelay(true).map_err(|e| e.to_string())?;
    let (sender, writer) = transport::writer(
        incoming.try_clone().map_err(|e| e.to_string())?,
        Duration::from_millis(config.setup.delay_ms),
        config.setup.queue_capacity,
    )?;
    journal.costs = Default::default();
    *auth.costs.borrow_mut() = Default::default();
    let handlers = std::cell::RefCell::new(crate::profile::Samples::default());
    let signing = std::cell::RefCell::new(crate::profile::Samples::default());
    let mut queue_costs = crate::profile::QueueCosts::default();
    let mut batches = crate::profile::BatchCosts::default();
    let mut faults = crate::faults::Faults::default();
    let faulty = config.index == 0 && config.setup.byzantine_mode != ByzantineMode::None;
    let (requests_tx, requests_rx) = std::sync::mpsc::sync_channel(config.setup.queue_capacity);
    std::thread::spawn(move || loop {
        let request = transport::read_profiled::<Request>(&mut incoming);
        let done = matches!(
            &request,
            Err(_)
                | Ok(transport::Received {
                    value: Request::Stop,
                    ..
                })
        );
        if requests_tx.send(request).is_err() || done {
            break;
        }
    });
    'requests: loop {
        let first = requests_rx.recv().map_err(|_| "request reader stopped")??;
        let mut ready = Vec::new();
        if let Some(decoded) = first.decoded_at {
            let phase = first.value.phase();
            ready.push((phase, queue_costs.receive(phase, decoded, first.decode_ms)));
        }
        let mut requests = vec![first.value];
        if config.setup.journal_batch_size > 1 && !matches!(requests[0], Request::Stop) {
            let deadline =
                Instant::now() + Duration::from_millis(config.setup.journal_batch_wait_ms);
            while requests.len() < config.setup.journal_batch_size {
                match requests_rx.recv_timeout(deadline.saturating_duration_since(Instant::now())) {
                    Ok(Ok(received)) => {
                        if let Some(decoded) = received.decoded_at {
                            let phase = received.value.phase();
                            ready.push((
                                phase,
                                queue_costs.receive(phase, decoded, received.decode_ms),
                            ));
                        }
                        let request = received.value;
                        let stop = matches!(request, Request::Stop);
                        requests.push(request);
                        if stop {
                            break;
                        }
                    }
                    Ok(Err(error)) => return Err(error),
                    Err(std::sync::mpsc::RecvTimeoutError::Timeout) => break,
                    Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => break,
                }
            }
        }
        for (phase, dequeued) in ready {
            queue_costs.hold(phase, dequeued)
        }
        if faulty {
            for request in &requests {
                for vote in faults.respond(config.setup.byzantine_mode, request, ctx.id(), id, &key)
                {
                    sender.send(&Response::Vote { vote })?;
                }
            }
            requests.retain(|request| matches!(request, Request::Stop));
            if requests.is_empty() {
                continue;
            }
        }
        if !faulty
            && config.setup.journal_batch_size > 1
            && config.index >= config.setup.silent_validators
        {
            let _service = crate::profile::Scope::new(&handlers);
            let batch_start = crate::profile::QUEUE_DIAGNOSTICS.then(Instant::now);
            let before = crate::profile::QUEUE_DIAGNOSTICS
                .then(|| crate::profile::Checkpoint::new(&journal, &auth));
            let result = group(&requests, &mut replica, &mut journal, &mut auth);
            journal.pending_acts.clear();
            if let Ok(signing_requests) = result {
                for request in signing_requests {
                    let start = Instant::now();
                    let signature = key.sign(&request.preimage()).to_bytes().to_vec();
                    signing.borrow_mut().record(start);
                    if let Err(error) = sender.send(&Response::Vote {
                        vote: request.attach(signature),
                    }) {
                        eprintln!("response delivery failed: {error}");
                    }
                }
                if let (Some(batch_start), Some(before)) = (batch_start, before) {
                    batches.record(
                        &requests,
                        batch_start,
                        before,
                        crate::profile::Checkpoint::new(&journal, &auth),
                        true,
                    );
                }
                if !requests.iter().any(|r| matches!(r, Request::Stop)) {
                    continue;
                }
                requests.retain(|r| matches!(r, Request::Stop));
            } else {
                if let (Some(batch_start), Some(before)) = (batch_start, before) {
                    batches.record(
                        &requests,
                        batch_start,
                        before,
                        crate::profile::Checkpoint::new(&journal, &auth),
                        false,
                    );
                }
            }
            // Rejected groups release no signing requests. Isolate bad requests
            // with the unchanged serial API, retaining its partial-progress rules.
        }
        for request in requests {
            if matches!(request, Request::Stop) {
                let view = replica.finalized_view()?;
                sender.send(&Response::Stopped {
                pid: std::process::id(),
                finalized: view.finalized.len(),
                value: i64::try_from(view.value)
                    .map_err(|_| "benchmark value exceeds wire range")?,
                events: journal.count(),
                syncs: journal.syncs,
                profile:json!({"request_service":handlers.borrow().report(),"vote_signing":signing.borrow().report(),
                    "authentication":auth.costs.borrow().report(),"journal":journal.costs.report(),"byzantine":faults,"queue_diagnostics_enabled":crate::profile::QUEUE_DIAGNOSTICS,"queue_phases":queue_costs.report(),"batches":batches.report(),"response_transport":sender.metrics().report()}),
            })?;
                break 'requests;
            }
            if config.index < config.setup.silent_validators {
                continue;
            }
            let _service = crate::profile::Scope::new(&handlers);
            let (payload, response) = match request {
                Request::Operation { signed } => {
                    let payload = signed.act.address.clone();
                    auth.remember(&signed);
                    journal.pending_act = Some(signed.clone());
                    let result = replica
                        .register(signed.act, &mut journal, &auth)
                        .and_then(|_| replica.prepare_operation(&payload, &mut journal, &auth));
                    journal.pending_act = None;
                    (
                        payload,
                        result.map(|request| {
                            let start = Instant::now();
                            let signature = key.sign(&request.preimage()).to_bytes().to_vec();
                            signing.borrow_mut().record(start);
                            Response::Vote {
                                vote: request.attach(signature),
                            }
                        }),
                    )
                }
                Request::Effects { certificate } => {
                    let payload = certificate.payload.clone();
                    let result = if certificate.kind != VoteKind::Operation {
                        Err("expected operation certificate".into())
                    } else {
                        replica
                            .receive(certificate, &mut journal, &auth)
                            .and_then(|_| replica.prepare_effects(&payload, &mut journal, &auth))
                    };
                    (
                        payload,
                        result.map(|request| {
                            let start = Instant::now();
                            let signature = key.sign(&request.preimage()).to_bytes().to_vec();
                            signing.borrow_mut().record(start);
                            Response::Vote {
                                vote: request.attach(signature),
                            }
                        }),
                    )
                }
                Request::Final { certificate } => {
                    let payload = certificate.payload.clone();
                    let result = if certificate.kind != VoteKind::Effects {
                        Err("expected effects certificate".into())
                    } else {
                        replica.receive(certificate, &mut journal, &auth)
                    };
                    if result.is_ok() {
                        continue;
                    }
                    (payload, result.map(|_| unreachable!()))
                }
                Request::Stop => unreachable!(),
            };
            let response = response.unwrap_or_else(|message| Response::Error {
                id: payload,
                message,
            });
            if let Err(error) = sender.send(&response) {
                eprintln!("response delivery failed: {error}");
            }
        }
    }
    drop(sender);
    writer.join().map_err(|_| "writer panicked")??;
    stats(&replica, &journal)
}

fn group(
    requests: &[Request],
    replica: &mut Replica,
    journal: &mut DurableJournal,
    auth: &mut Auth,
) -> Result<Vec<cbcl_core::quorum::SigningRequest>> {
    let mut events = Vec::new();
    for request in requests {
        match request {
            Request::Operation { signed } => {
                auth.remember(signed);
                journal
                    .pending_acts
                    .insert(signed.act.address.clone(), signed.clone());
                events.push(Event::Candidate(signed.act.clone()));
                events.push(Event::Sign(signed.act.address.clone()));
            }
            Request::Effects { certificate } => {
                if certificate.kind != VoteKind::Operation {
                    return Err("expected operation certificate".into());
                }
                events.push(Event::Certificate(certificate.clone()));
                events.push(Event::Effect(certificate.payload.clone()));
            }
            Request::Final { certificate } => {
                if certificate.kind != VoteKind::Effects {
                    return Err("expected effects certificate".into());
                }
                events.push(Event::Certificate(certificate.clone()));
            }
            Request::Stop => {}
        }
    }
    Ok(replica
        .commit_group(&events, journal, auth)?
        .into_iter()
        .flatten()
        .collect())
}
