//! Bounded foreground scheduling. Timed-out validation cannot install; a
//! timed-out commit retains exclusive writer ownership until its outcome is known.
use crate::{
    host::{DurableClient, OpenMetrics, PreparedInstall},
    member::Client,
    Error, Result,
};
use std::{
    sync::{
        atomic::{AtomicUsize, Ordering},
        mpsc::{self, Receiver, RecvTimeoutError},
        Arc,
    },
    time::{Duration, Instant},
};
static VALIDATORS: AtomicUsize = AtomicUsize::new(0);
static COMMITS: AtomicUsize = AtomicUsize::new(0);
struct Permit(&'static AtomicUsize);
impl Permit {
    fn take(counter: &'static AtomicUsize) -> Result<Self> {
        counter
            .fetch_update(Ordering::AcqRel, Ordering::Relaxed, |n| {
                if n < 2 {
                    Some(n + 1)
                } else {
                    None
                }
            })
            .map_err(|_| Error::Budget)?;
        Ok(Self(counter))
    }
}
impl Drop for Permit {
    fn drop(&mut self) {
        self.0.fetch_sub(1, Ordering::AcqRel);
    }
}
pub(crate) fn validation(
    job: impl FnOnce() -> Result<PreparedInstall> + Send + 'static,
    deadline: Instant,
) -> Result<PreparedInstall> {
    if Instant::now() >= deadline {
        return Err(Error::Cancelled);
    }
    let permit = Permit::take(&VALIDATORS)?;
    let (tx, rx) = mpsc::sync_channel(1);
    let dispatch = tracing::dispatcher::get_default(Clone::clone);
    std::thread::Builder::new()
        .name("checkpoint-validation".into())
        .spawn(move || {
            let _permit = permit;
            let result = tracing::dispatcher::with_default(&dispatch, job);
            let _ = tx.send(result);
        })?;
    match rx.recv_timeout(deadline.saturating_duration_since(Instant::now())) {
        Ok(result) => result,
        Err(RecvTimeoutError::Timeout) => Err(Error::Cancelled),
        Err(RecvTimeoutError::Disconnected) => Err(Error::Invalid("validation worker stopped")),
    }
}
pub struct PendingInstall {
    receiver: Receiver<(DurableClient, Result<OpenMetrics>)>,
    previous: Arc<Client>,
    deadline: Instant,
}
pub enum CommitOutcome {
    Complete {
        store: Box<DurableClient>,
        result: Result<OpenMetrics>,
    },
    /// The OS write may finish. This handle preserves the single writer fence.
    Uncertain(PendingInstall),
    RecoveryRequired {
        previous: Arc<Client>,
        error: Error,
    },
}
impl PendingInstall {
    pub fn previous(&self) -> &Client {
        &self.previous
    }
    /// Initial foreground wait shares the validation operation's original deadline.
    pub fn wait_deadline(self) -> CommitOutcome {
        let remaining = self.deadline.saturating_duration_since(Instant::now());
        self.wait(remaining)
    }
    pub fn wait(self, timeout: Duration) -> CommitOutcome {
        match self.receiver.recv_timeout(timeout) {
            Ok((store, result)) => CommitOutcome::Complete {
                store: Box::new(store),
                result,
            },
            Err(RecvTimeoutError::Timeout) => CommitOutcome::Uncertain(self),
            Err(RecvTimeoutError::Disconnected) => CommitOutcome::RecoveryRequired {
                previous: self.previous,
                error: Error::Invalid("commit worker stopped; recover durable generation"),
            },
        }
    }
}
/// Moves exclusive ownership into a bounded worker. The caller cannot mutate the
/// store while an ambiguous commit remains outstanding. On start failure recover
/// the previously durable store; no unsaved changes are hidden in the handle.
pub fn start_install(
    mut store: DurableClient,
    prepared: PreparedInstall,
) -> Result<PendingInstall> {
    let deadline = prepared.deadline();
    if Instant::now() >= deadline {
        return Err(Error::Cancelled);
    }
    let permit = Permit::take(&COMMITS)?;
    let previous = store.snapshot();
    let (tx, receiver) = mpsc::sync_channel(1);
    let dispatch = tracing::dispatcher::get_default(Clone::clone);
    std::thread::Builder::new()
        .name("checkpoint-commit".into())
        .spawn(move || {
            let _permit = permit;
            let result = tracing::dispatcher::with_default(&dispatch, || store.install(prepared));
            let _ = tx.send((store, result));
        })?;
    Ok(PendingInstall {
        receiver,
        previous,
        deadline,
    })
}
