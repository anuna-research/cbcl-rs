use crate::model::{Result, SignedAct};
use cbcl_core::quorum::{Certificate, Vote};
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use std::{
    io::{Read, Write},
    net::TcpStream,
    sync::mpsc::{self, SyncSender},
    thread,
    time::{Duration, Instant},
};
const MAX_FRAME: usize = 1 << 20;
#[derive(Serialize, Deserialize)]
#[serde(tag = "type", deny_unknown_fields)]
// Requests are deserialized and handled immediately; queues contain encoded bytes.
#[allow(clippy::large_enum_variant)]
pub enum Request {
    Operation { signed: SignedAct },
    Effects { certificate: Certificate },
    Final { certificate: Certificate },
    Stop,
}
#[derive(Serialize, Deserialize)]
#[serde(tag = "type", deny_unknown_fields)]
pub enum Response {
    Vote {
        vote: Vote,
    },
    Error {
        id: String,
        message: String,
    },
    Stopped {
        pid: u32,
        finalized: usize,
        value: i64,
        events: u64,
        syncs: u64,
        profile: serde_json::Value,
    },
}
pub trait WireMessage: Serialize {
    fn phase(&self) -> &'static str;
}
impl WireMessage for Request {
    fn phase(&self) -> &'static str {
        match self {
            Self::Operation { .. } => "operation",
            Self::Effects { .. } => "effects",
            Self::Final { .. } => "final",
            Self::Stop => "stop",
        }
    }
}
impl WireMessage for Response {
    fn phase(&self) -> &'static str {
        match self {
            Self::Vote { vote } => match vote.kind {
                cbcl_core::quorum::VoteKind::Operation => "operation",
                cbcl_core::quorum::VoteKind::Effects => "effects",
                _ => "other_vote",
            },
            Self::Error { .. } => "error",
            Self::Stopped { .. } => "stopped",
        }
    }
}
pub struct Received<T> {
    pub value: T,
    pub decoded_at: Option<Instant>,
    pub decode_ms: f64,
}
pub fn read_frame<T: DeserializeOwned>(stream: &mut TcpStream) -> Result<T> {
    read_profiled(stream).map(|m| m.value)
}
pub fn read_profiled<T: DeserializeOwned>(stream: &mut TcpStream) -> Result<Received<T>> {
    let mut header = [0; 4];
    stream.read_exact(&mut header).map_err(|e| e.to_string())?;
    let len = u32::from_be_bytes(header) as usize;
    if len == 0 || len > MAX_FRAME {
        return Err("invalid frame length".into());
    }
    let mut bytes = vec![0; len];
    stream.read_exact(&mut bytes).map_err(|e| e.to_string())?;
    let start = crate::profile::QUEUE_DIAGNOSTICS.then(Instant::now);
    let value = serde_json::from_slice(&bytes).map_err(|e| e.to_string())?;
    let decoded_at = start.map(|_| Instant::now());
    Ok(Received {
        value,
        decoded_at,
        decode_ms: match (decoded_at, start) {
            (Some(end), Some(start)) => end.duration_since(start).as_secs_f64() * 1000.0,
            _ => 0.0,
        },
    })
}
struct Scheduled {
    phase: &'static str,
    due: Instant,
    bytes: Vec<u8>,
}
#[derive(Default)]
struct TransportPhase {
    encode: crate::profile::Samples,
    overdue: crate::profile::Samples,
    write: crate::profile::Samples,
}
#[derive(Clone, Default)]
pub struct TransportMetrics(
    std::sync::Arc<std::sync::Mutex<std::collections::BTreeMap<&'static str, TransportPhase>>>,
);
impl TransportMetrics {
    pub fn report(&self) -> serde_json::Value {
        serde_json::Value::Object(self.0.lock().unwrap().iter().map(|(k,v)|((*k).into(),serde_json::json!({"encode_ms":v.encode.report(),"overdue_ms":v.overdue.report(),"socket_write_ms":v.write.report()}))).collect())
    }
}
pub struct DelayedSender {
    tx: SyncSender<Scheduled>,
    delay: Duration,
    metrics: TransportMetrics,
}
impl DelayedSender {
    pub fn metrics(&self) -> TransportMetrics {
        self.metrics.clone()
    }
    pub fn send<T: WireMessage>(&self, message: &T) -> Result<()> {
        let start = crate::profile::QUEUE_DIAGNOSTICS.then(Instant::now);
        let phase = message.phase();
        let bytes = serde_json::to_vec(message).map_err(|e| e.to_string())?;
        if bytes.is_empty() || bytes.len() > MAX_FRAME {
            return Err("oversized frame".into());
        }
        if let Some(start) = start {
            self.metrics
                .0
                .lock()
                .unwrap()
                .entry(phase)
                .or_default()
                .encode
                .record(start);
        }
        let due = Instant::now() + self.delay;
        self.tx
            .try_send(Scheduled { phase, due, bytes })
            .map_err(|e| format!("transport queue unavailable: {e}"))
    }
}
/// Constant one-way delay per frame, not a sleep that serializes all requests.
pub fn writer(
    mut stream: TcpStream,
    delay: Duration,
    capacity: usize,
) -> Result<(DelayedSender, thread::JoinHandle<Result<()>>)> {
    stream.set_nodelay(true).map_err(|e| e.to_string())?;
    let (tx, rx) = mpsc::sync_channel::<Scheduled>(capacity);
    let metrics = TransportMetrics::default();
    let worker_metrics = metrics.clone();
    let task = thread::spawn(move || {
        while let Ok(frame) = rx.recv() {
            if let Some(wait) = frame.due.checked_duration_since(Instant::now()) {
                thread::sleep(wait);
            }
            let start = crate::profile::QUEUE_DIAGNOSTICS.then(Instant::now);
            stream
                .write_all(&(frame.bytes.len() as u32).to_be_bytes())
                .map_err(|e| e.to_string())?;
            stream.write_all(&frame.bytes).map_err(|e| e.to_string())?;
            if let Some(start) = start {
                let overdue = start.saturating_duration_since(frame.due).as_secs_f64() * 1000.0;
                let mut costs = worker_metrics.0.lock().unwrap();
                let p = costs.entry(frame.phase).or_default();
                p.overdue.record_ms(overdue);
                p.write.record(start);
            }
        }
        Ok(())
    });
    Ok((DelayedSender { tx, delay, metrics }, task))
}
