//! Wall-clock service costs. Nested components must not be summed with parents.
pub const QUEUE_DIAGNOSTICS: bool = cfg!(feature = "queue-diagnostics");
use serde_json::{json, Value};
use std::{cell::RefCell, time::Instant};
#[derive(Clone, Default)]
pub struct Samples {
    values: Vec<f64>,
    total: f64,
}
impl Samples {
    pub fn record(&mut self, start: Instant) {
        self.record_ms(start.elapsed().as_secs_f64() * 1000.0);
    }
    pub fn record_ms(&mut self, ms: f64) {
        self.values.push(ms);
        self.total += ms;
    }
    pub fn total_ms(&self) -> f64 {
        self.total
    }
    pub fn report(&self) -> Value {
        let mut values = self.values.clone();
        values.sort_by(f64::total_cmp);
        let total: f64 = values.iter().sum();
        let percentile = |p: usize| {
            if values.is_empty() {
                None
            } else {
                Some(values[(values.len() * p).div_ceil(100) - 1])
            }
        };
        json!({"count":values.len(),"total_ms":total,"mean_ms":if values.is_empty(){0.0}else{total/values.len() as f64},"p50_ms":percentile(50),"p95_ms":percentile(95),"p99_ms":percentile(99)})
    }
}
pub struct Scope<'a> {
    samples: &'a RefCell<Samples>,
    start: Instant,
}
impl<'a> Scope<'a> {
    pub fn new(samples: &'a RefCell<Samples>) -> Self {
        Self {
            samples,
            start: Instant::now(),
        }
    }
}
impl Drop for Scope<'_> {
    fn drop(&mut self) {
        self.samples.borrow_mut().record(self.start)
    }
}
#[derive(Clone, Default)]
pub struct AuthCosts {
    pub admission: Samples,
    pub verify: Samples,
}
impl AuthCosts {
    pub fn report(&self) -> Value {
        json!({"admission":self.admission.report(),"signature_verification":self.verify.report()})
    }
}
#[derive(Default)]
pub struct JournalCosts {
    pub encode: Samples,
    pub write: Samples,
    pub sync: Samples,
}
impl JournalCosts {
    pub fn report(&self) -> Value {
        json!({"journal_encode":self.encode.report(),"journal_write":self.write.report(),"journal_sync":self.sync.report()})
    }
}

#[derive(Default)]
pub struct QueueCosts {
    phases: std::collections::BTreeMap<&'static str, QueuePhase>,
}
#[derive(Default)]
struct QueuePhase {
    queue: Samples,
    hold: Samples,
    decode: Samples,
}
impl QueueCosts {
    pub fn receive(&mut self, phase: &'static str, decoded: Instant, decode_ms: f64) -> Instant {
        let now = Instant::now();
        let p = self.phases.entry(phase).or_default();
        p.queue
            .record_ms(now.duration_since(decoded).as_secs_f64() * 1000.0);
        p.decode.record_ms(decode_ms);
        now
    }
    pub fn hold(&mut self, phase: &'static str, dequeued: Instant) {
        self.phases.entry(phase).or_default().hold.record(dequeued)
    }
    pub fn report(&self) -> Value {
        Value::Object(self.phases.iter().map(|(k,p)|((*k).into(),json!({"receive_queue_ms":p.queue.report(),"batch_hold_ms":p.hold.report(),"decode_ms":p.decode.report()}))).collect())
    }
}
#[derive(Default)]
pub struct PhaseService(std::collections::BTreeMap<&'static str, Samples>);
impl PhaseService {
    pub fn record(&mut self, phase: &'static str, start: Instant) {
        self.0.entry(phase).or_default().record(start)
    }
    pub fn report(&self) -> Value {
        Value::Object(
            self.0
                .iter()
                .map(|(k, v)| ((*k).into(), v.report()))
                .collect(),
        )
    }
}
pub struct PhaseScope<'a> {
    costs: &'a RefCell<PhaseService>,
    phase: &'static str,
    start: Instant,
}
impl<'a> PhaseScope<'a> {
    pub fn new(costs: &'a RefCell<PhaseService>, phase: &'static str) -> Self {
        Self {
            costs,
            phase,
            start: Instant::now(),
        }
    }
}
impl Drop for PhaseScope<'_> {
    fn drop(&mut self) {
        self.costs.borrow_mut().record(self.phase, self.start)
    }
}
#[derive(Default)]
pub struct BatchCosts(std::collections::BTreeMap<&'static str, BatchKind>);
#[derive(Default)]
struct BatchKind {
    service: Samples,
    requests: u64,
    operations: u64,
    effects: u64,
    finals: u64,
    events: u64,
    syncs: u64,
    write_ms: f64,
    sync_ms: f64,
    verify_ms: f64,
}
#[derive(Clone, Copy)]
pub struct Checkpoint {
    events: u64,
    syncs: u64,
    write: f64,
    sync: f64,
    verify: f64,
}
impl Checkpoint {
    pub fn new(j: &crate::journal::DurableJournal, a: &crate::model::Auth) -> Self {
        Self {
            events: j.count(),
            syncs: j.syncs,
            write: j.costs.write.total_ms(),
            sync: j.costs.sync.total_ms(),
            verify: a.costs.borrow().verify.total_ms(),
        }
    }
}
impl BatchCosts {
    pub fn record(
        &mut self,
        requests: &[crate::transport::Request],
        start: Instant,
        before: Checkpoint,
        after: Checkpoint,
        success: bool,
    ) {
        use crate::transport::Request;
        let o = requests
            .iter()
            .filter(|r| matches!(r, Request::Operation { .. }))
            .count() as u64;
        let e = requests
            .iter()
            .filter(|r| matches!(r, Request::Effects { .. }))
            .count() as u64;
        let f = requests
            .iter()
            .filter(|r| matches!(r, Request::Final { .. }))
            .count() as u64;
        if o + e + f == 0 {
            return;
        }
        let kind = if !success {
            "rejected"
        } else if o > 0 && e + f == 0 {
            "operation_only"
        } else if e > 0 && o + f == 0 {
            "effects_only"
        } else if f > 0 && o + e == 0 {
            "final_only"
        } else {
            "mixed"
        };
        let p = self.0.entry(kind).or_default();
        p.service.record(start);
        p.requests += o + e + f;
        p.operations += o;
        p.effects += e;
        p.finals += f;
        p.events += after.events - before.events;
        p.syncs += after.syncs - before.syncs;
        p.write_ms += after.write - before.write;
        p.sync_ms += after.sync - before.sync;
        p.verify_ms += after.verify - before.verify;
    }
    pub fn report(&self) -> Value {
        Value::Object(self.0.iter().map(|(k,p)|((*k).into(),json!({"service_ms":p.service.report(),"requests":p.requests,"operation_requests":p.operations,"effects_requests":p.effects,"final_requests":p.finals,"events":p.events,"syncs":p.syncs,"write_ms":p.write_ms,"sync_ms":p.sync_ms,"verify_ms":p.verify_ms}))).collect())
    }
}
