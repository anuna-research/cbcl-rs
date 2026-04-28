//! Pluggable clock abstraction for time-aware agent state (REQ-305 TTL).
//!
//! Cbcl-core is `no_std + alloc`-compatible, so the agent can't reach for
//! `std::time::SystemTime` directly. Instead, callers inject a [`Clock`]
//! that yields the current second-since-epoch when the agent needs to
//! stamp a buffered entry or run TTL eviction.
//!
//! Two implementations ship in-tree:
//!
//! - [`NoClock`] — always returns [`u64::MAX`]. Buffered entries stamped
//!   with this value never expire under
//!   [`PendingQueue::expire`](crate::policy::PendingQueue::expire), giving
//!   a "no TTL" semantic by default. This is what [`Agent::new`] uses.
//! - [`SystemClock`] (gated on the `std` feature) — wraps
//!   `SystemTime::now()` and emits seconds since the Unix epoch.
//!
//! Custom clocks are useful for tests (a mock that ticks deterministically),
//! for embedded targets that have a custom time source, or when wiring the
//! agent into a larger system that already owns a clock.

#![forbid(unsafe_code)]

/// A monotonic-ish source of "seconds since epoch" used by the agent for
/// pending-queue timestamps. Implementations must be `Debug + Send + Sync`
/// so the agent (which derives `Debug` and may move across threads) can
/// hold an `Arc<dyn Clock>`.
pub trait Clock: core::fmt::Debug + Send + Sync {
    /// Return the current time in seconds. The exact epoch is up to the
    /// implementation as long as it is consistent across calls — the agent
    /// only ever compares values from the same clock against each other
    /// (e.g. `now.saturating_sub(inserted_at) >= ttl`).
    fn now(&self) -> u64;
}

/// A clock that always reports [`u64::MAX`]. Entries stamped with this
/// value are never reaped by TTL expiry — the agent's default behaviour.
#[derive(Debug, Clone, Copy, Default)]
pub struct NoClock;

impl Clock for NoClock {
    fn now(&self) -> u64 {
        u64::MAX
    }
}

/// A clock backed by `std::time::SystemTime::now()`, returning seconds
/// since the Unix epoch. Available only when the `std` feature is on.
#[cfg(feature = "std")]
#[derive(Debug, Clone, Copy, Default)]
pub struct SystemClock;

#[cfg(feature = "std")]
impl Clock for SystemClock {
    /// Returns seconds since `UNIX_EPOCH`. If the system clock is set to a
    /// time *before* `UNIX_EPOCH` (effectively impossible on a sane host
    /// but a `Result::Err` on `duration_since`), falls back to
    /// [`u64::MAX`] — the same value [`NoClock`] uses — so a misbehaving
    /// clock errs toward "don't expire anything" rather than the
    /// alternative of "expire everything immediately".
    fn now(&self) -> u64 {
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(u64::MAX)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn no_clock_returns_u64_max() {
        assert_eq!(NoClock.now(), u64::MAX);
    }

    #[cfg(feature = "std")]
    #[test]
    fn system_clock_is_recent() {
        let now = SystemClock.now();
        // Sanity bounds — between 2020 and year 3000.
        assert!(now > 1_577_836_800, "clock before 2020: {now}");
        assert!(now < 32_503_680_000, "clock after year 3000: {now}");
    }
}
