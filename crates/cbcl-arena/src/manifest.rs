//! manifest: SPEC-011 reproducibility manifest (REQ-1151).
//!
//! The manifest is the byte-stable record of every configuration input
//! that influenced a measurement run. Per `REQ-1151`, re-running the
//! measurement protocol with the same manifest must produce byte-identical
//! reports for the deterministic cells.
//!
//! The schema (see [`ReproducibilityManifest`]) carries:
//!
//! - `schema_version` — bumped on every backwards-incompatible field change.
//! - `git_commit` — populated at build time via `build.rs` (env var
//!   `CBCL_ARENA_GIT_COMMIT`); falls back to `"unknown"` when git is
//!   unavailable.
//! - `timestamp_utc` — ISO-8601 wall-clock UTC at construction.
//! - `platform` — `OS-ARCH` from `std::env::consts`.
//! - `n_per_cell` — `N` per `REQ-1150` (default 300).
//! - `overall_seed` — the single 64-bit input from which every per-cell
//!   game seed is derived (deterministic SHA-256 expansion via
//!   [`derive_cell_seed`]).
//! - `per_cell_seeds` — one entry per
//!   `(challenge, agent, attacker, trial)` tuple, carrying the derived
//!   per-game seed.
//! - `dialect_hashes` — SHA-256 hex digest of each dialect file
//!   (`psi`, `millionaire`, `dining`).
//! - `attacker_version` — semver of this crate plus a short commit suffix.
//! - `distribution_params` — string-keyed snapshot of operator-config
//!   knobs (e.g. PSI overlap distribution, Yao wealth range).
//!
//! ## Serialisation
//!
//! [`ReproducibilityManifest::to_json`] / [`ReproducibilityManifest::from_json`]
//! round-trip via `serde_json`; the top-level field is `schema_version`.

extern crate alloc;

use alloc::collections::BTreeMap;
use alloc::string::{String, ToString};
use alloc::vec::Vec;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

/// Current manifest schema version. Bump on any backwards-incompatible
/// change to [`ReproducibilityManifest`].
pub const SCHEMA_VERSION: u32 = 1;

/// Reproducibility manifest (REQ-1151).
///
/// All fields are public and serialised in declaration order. The struct
/// derives `Eq` so two manifests built from identical configs compare
/// byte-for-byte (modulo `timestamp_utc`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReproducibilityManifest {
    /// Manifest schema version.
    pub schema_version: u32,
    /// Build-time git commit hash (or `"unknown"`).
    pub git_commit: String,
    /// ISO-8601 wall-clock UTC at construction.
    pub timestamp_utc: String,
    /// `OS-ARCH` platform identifier from `std::env::consts`.
    pub platform: String,
    /// Trials per cell.
    pub n_per_cell: u32,
    /// Master seed.
    pub overall_seed: u64,
    /// Per-cell derived seeds (one per `(challenge, agent, attacker, trial)`).
    pub per_cell_seeds: Vec<CellSeedRecord>,
    /// SHA-256 hex digest of each shipped dialect source file.
    pub dialect_hashes: BTreeMap<String, String>,
    /// Attacker library version (`crate-version+commit-short`).
    pub attacker_version: String,
    /// Operator-configuration snapshot (e.g. distribution knobs).
    pub distribution_params: BTreeMap<String, String>,
}

/// One row of the per-cell seed table.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CellSeedRecord {
    /// Challenge identifier (e.g. `"psi"`, `"millionaire"`, `"dining"`).
    pub challenge: String,
    /// Agent strategy identifier (e.g. `"cbcl"`, `"vanilla"`).
    pub agent: String,
    /// Attacker pattern identifier (`"<category>:<pattern>"`).
    pub attacker: String,
    /// Trial index within the cell, `[0, n_per_cell)`.
    pub trial: u32,
    /// Derived per-game seed.
    pub seed: u64,
}

// =============================================================================
// Per-cell seed derivation: SHA-256 over a packed key.
// =============================================================================

/// Derive a per-cell seed deterministically from `overall_seed` and the
/// cell coordinates. The derivation is `u64::from_le_bytes(SHA256(packed)[..8])`
/// over the byte-encoded inputs — flipping any input bit cascades into the
/// output, and same inputs ⇒ same seed.
pub fn derive_cell_seed(
    overall_seed: u64,
    challenge: &str,
    agent: &str,
    attacker: &str,
    trial: u32,
) -> u64 {
    let mut h = Sha256::new();
    h.update(b"cbcl-arena/seed/v1\0");
    h.update(overall_seed.to_le_bytes());
    h.update((challenge.len() as u64).to_le_bytes());
    h.update(challenge.as_bytes());
    h.update((agent.len() as u64).to_le_bytes());
    h.update(agent.as_bytes());
    h.update((attacker.len() as u64).to_le_bytes());
    h.update(attacker.as_bytes());
    h.update(trial.to_le_bytes());
    let digest = h.finalize();
    let mut out = [0u8; 8];
    out.copy_from_slice(&digest[..8]);
    u64::from_le_bytes(out)
}

// =============================================================================
// Dialect-source hashes (SHA-256, hex-encoded).
// =============================================================================

/// PSI dialect source, captured at build time.
const PSI_DIALECT_SRC: &str = include_str!("../../../demo/dialects/psi.cbcl");
/// Yao's Millionaire dialect source, captured at build time.
const MILLIONAIRE_DIALECT_SRC: &str =
    include_str!("../../../demo/dialects/millionaire.cbcl");
/// Dining Cryptographers dialect source, captured at build time.
const DINING_DIALECT_SRC: &str = include_str!("../../../demo/dialects/dining.cbcl");

/// SHA-256 hex digest of `bytes`.
fn sha256_hex(bytes: &[u8]) -> String {
    let mut h = Sha256::new();
    h.update(bytes);
    let digest = h.finalize();
    let mut out = String::with_capacity(64);
    for b in digest.iter() {
        use core::fmt::Write;
        let _ = write!(out, "{:02x}", b);
    }
    out
}

/// Compute the canonical dialect-hash table.
pub fn canonical_dialect_hashes() -> BTreeMap<String, String> {
    let mut m = BTreeMap::new();
    m.insert("psi".to_string(), sha256_hex(PSI_DIALECT_SRC.as_bytes()));
    m.insert(
        "millionaire".to_string(),
        sha256_hex(MILLIONAIRE_DIALECT_SRC.as_bytes()),
    );
    m.insert(
        "dining".to_string(),
        sha256_hex(DINING_DIALECT_SRC.as_bytes()),
    );
    m
}

// =============================================================================
// Build-time git commit + crate-version "attacker_version" string.
// =============================================================================

/// Crate version (from Cargo).
const CRATE_VERSION: &str = env!("CARGO_PKG_VERSION");

/// Build-time-resolved git commit hash, with `"unknown"` fallback. The
/// value is set by `build.rs`.
pub fn build_time_git_commit() -> String {
    option_env!("CBCL_ARENA_GIT_COMMIT")
        .unwrap_or("unknown")
        .to_string()
}

/// Compose the `attacker_version` field as `<crate-version>+<commit-short>`.
pub fn attacker_version_string() -> String {
    let commit = build_time_git_commit();
    let short = if commit == "unknown" {
        "unknown".to_string()
    } else {
        commit.chars().take(12).collect()
    };
    format!("{CRATE_VERSION}+{short}")
}

// =============================================================================
// Platform identifier.
// =============================================================================

/// Build-target platform identifier (`OS-ARCH`).
pub fn current_platform() -> String {
    format!("{}-{}", std::env::consts::OS, std::env::consts::ARCH)
}

// =============================================================================
// ISO-8601 timestamp.
// =============================================================================

/// Compute a UTC ISO-8601 timestamp using only the standard library. The
/// implementation uses Howard Hinnant's civil-from-days algorithm.
pub fn iso8601_utc_now() -> String {
    use std::time::{SystemTime, UNIX_EPOCH};
    let secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);
    format_iso8601(secs)
}

/// Format an `i64` Unix-epoch second count as `YYYY-MM-DDTHH:MM:SSZ`.
fn format_iso8601(secs: u64) -> String {
    let days = (secs / 86_400) as i64;
    let secs_of_day = (secs % 86_400) as u32;
    let h = (secs_of_day / 3600) as u8;
    let m = ((secs_of_day % 3600) / 60) as u8;
    let s = (secs_of_day % 60) as u8;
    let (y, mo, d) = civil_from_days(days);
    format!("{:04}-{:02}-{:02}T{:02}:{:02}:{:02}Z", y, mo, d, h, m, s)
}

/// Convert a count of days since the UNIX epoch (1970-01-01) to a
/// proleptic Gregorian (year, month, day) triple via Howard Hinnant's
/// algorithm.
fn civil_from_days(z: i64) -> (i32, u8, u8) {
    let z = z + 719_468;
    let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
    let doe = (z - era * 146_097) as u64;
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let y = yoe as i64 + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = (doy - (153 * mp + 2) / 5 + 1) as u8;
    let m = if mp < 10 { mp + 3 } else { mp - 9 } as u8;
    let yr = y + if m <= 2 { 1 } else { 0 };
    (yr as i32, m, d)
}

// =============================================================================
// Construction / serialisation.
// =============================================================================

impl ReproducibilityManifest {
    /// Build a manifest from a measurement configuration (`REQ-1151`).
    ///
    /// Per-cell seeds are derived deterministically from `overall_seed`
    /// via [`derive_cell_seed`]. The constructor is the load-bearing
    /// reproducibility primitive: same `MeasurementConfig` ⇒ same
    /// `per_cell_seeds`, by construction (TEST-1151).
    ///
    /// `timestamp_utc` is taken from the wall clock at construction; tests
    /// that require a stable timestamp use [`Self::new_with_timestamp`].
    pub fn new(config: &crate::measurement::MeasurementConfig) -> Self {
        Self::new_with_timestamp(config, iso8601_utc_now())
    }

    /// Test-friendly constructor: same as [`Self::new`] but accepts an
    /// explicit `timestamp_utc`, so the manifest's byte-stability tests
    /// can pin the wall-clock field.
    pub fn new_with_timestamp(
        config: &crate::measurement::MeasurementConfig,
        timestamp_utc: String,
    ) -> Self {
        let mut per_cell_seeds: Vec<CellSeedRecord> = Vec::new();
        for &challenge in &config.challenges {
            let challenge_id = challenge_short_name(challenge);
            for &agent in &config.agents {
                let agent_id = agent_short_name(agent);
                for &attack in &config.categories {
                    let attacker_id = attack_short_name(attack);
                    for trial in 0..config.n_per_cell {
                        let seed = derive_cell_seed(
                            config.overall_seed,
                            challenge_id,
                            agent_id,
                            attacker_id,
                            trial as u32,
                        );
                        per_cell_seeds.push(CellSeedRecord {
                            challenge: challenge_id.to_string(),
                            agent: agent_id.to_string(),
                            attacker: attacker_id.to_string(),
                            trial: trial as u32,
                            seed,
                        });
                    }
                }
            }
        }

        // Snapshot operator-config knobs: PSI universe size and overlap
        // distribution, Yao's wealth range. Recorded as a plain
        // string-keyed map so future knobs can be added without a schema
        // bump as long as they remain readable.
        let mut distribution_params: BTreeMap<String, String> = BTreeMap::new();
        distribution_params.insert("psi.set_size".to_string(), "4".to_string());
        distribution_params.insert(
            "psi.overlap_distribution".to_string(),
            "Uniform".to_string(),
        );
        distribution_params.insert(
            "millionaire.wealth_distribution".to_string(),
            "LogUniform".to_string(),
        );

        Self {
            schema_version: SCHEMA_VERSION,
            git_commit: build_time_git_commit(),
            timestamp_utc,
            platform: current_platform(),
            n_per_cell: config.n_per_cell as u32,
            overall_seed: config.overall_seed,
            per_cell_seeds,
            dialect_hashes: canonical_dialect_hashes(),
            attacker_version: attacker_version_string(),
            distribution_params,
        }
    }

    /// Look up the per-cell seed for a `(challenge, agent, attack, trial)`
    /// tuple, returning `None` if the matrix doesn't include it.
    pub fn lookup_seed(
        &self,
        challenge: &str,
        agent: &str,
        attacker: &str,
        trial: u32,
    ) -> Option<u64> {
        self.per_cell_seeds
            .iter()
            .find(|r| {
                r.challenge == challenge
                    && r.agent == agent
                    && r.attacker == attacker
                    && r.trial == trial
            })
            .map(|r| r.seed)
    }

    /// Serialise to a pretty-printed JSON string.
    pub fn to_json(&self) -> String {
        serde_json::to_string_pretty(self)
            .expect("ReproducibilityManifest is serde-safe; serialisation cannot fail")
    }

    /// Deserialise from JSON.
    pub fn from_json(s: &str) -> Result<Self, serde_json::Error> {
        serde_json::from_str(s)
    }

    /// Pretty-printed JSON write — `Write`-trait wrapper for [`Self::to_json`].
    pub fn write_json<W: std::io::Write>(&self, w: &mut W) -> std::io::Result<()> {
        let s = self.to_json();
        w.write_all(s.as_bytes())?;
        w.write_all(b"\n")
    }

    /// JSON read — `Read`-trait wrapper for [`Self::from_json`].
    pub fn read_json<R: std::io::Read>(r: &mut R) -> std::io::Result<Self> {
        let mut s = String::new();
        r.read_to_string(&mut s)?;
        Self::from_json(&s)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, e))
    }
}

// =============================================================================
// Stable short-name encodings for the matrix axes. These appear in the
// per-cell seed records and in `CellSeedRecord::challenge` / `.agent` /
// `.attacker`. Kept short and lowercase to keep the manifest readable.
// =============================================================================

/// Stable short name for a [`crate::operator::ChallengeKind`].
pub fn challenge_short_name(c: crate::operator::ChallengeKind) -> &'static str {
    use crate::operator::ChallengeKind;
    match c {
        ChallengeKind::Psi => "psi",
        ChallengeKind::Millionaire => "millionaire",
        ChallengeKind::Dining => "dining",
    }
}

/// Three agent strategies under measurement (REQ-1150 axis).
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize,
)]
pub enum AgentKind {
    /// CBCL-disciplined agent ([`crate::agents::cbcl::CbclAgent`]).
    Cbcl,
    /// Vanilla NL-chat comparator ([`crate::agents::vanilla::VanillaAgent`]).
    Vanilla,
}

/// Stable short name for an [`AgentKind`].
pub fn agent_short_name(a: AgentKind) -> &'static str {
    match a {
        AgentKind::Cbcl => "cbcl",
        AgentKind::Vanilla => "vanilla",
    }
}

/// Stable short name for an [`crate::attackers::AttackCategory`].
pub fn attack_short_name(a: crate::attackers::AttackCategory) -> &'static str {
    use crate::attackers::AttackCategory;
    match a {
        AttackCategory::Honest => "honest",
        AttackCategory::Published => "published",
        AttackCategory::Novel => "novel",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn schema_version_is_one() {
        assert_eq!(SCHEMA_VERSION, 1);
    }

    #[test]
    fn dialect_hashes_are_64_hex_chars() {
        let m = canonical_dialect_hashes();
        for (k, v) in &m {
            assert_eq!(v.len(), 64, "{} hash should be 64 hex chars", k);
            assert!(
                v.chars().all(|c| c.is_ascii_hexdigit()),
                "{} hash must be hex",
                k
            );
        }
        assert!(m.contains_key("psi"));
        assert!(m.contains_key("millionaire"));
        assert!(m.contains_key("dining"));
    }

    #[test]
    fn dialect_hashes_stable_across_calls() {
        let a = canonical_dialect_hashes();
        let b = canonical_dialect_hashes();
        assert_eq!(a, b);
    }

    #[test]
    fn cell_seed_deterministic() {
        let s1 = derive_cell_seed(42, "psi", "cbcl", "honest:honest", 0);
        let s2 = derive_cell_seed(42, "psi", "cbcl", "honest:honest", 0);
        assert_eq!(s1, s2);
    }

    #[test]
    fn cell_seed_differs_on_input_change() {
        let s1 = derive_cell_seed(42, "psi", "cbcl", "honest:honest", 0);
        let s2 = derive_cell_seed(42, "psi", "cbcl", "honest:honest", 1);
        let s3 = derive_cell_seed(43, "psi", "cbcl", "honest:honest", 0);
        let s4 = derive_cell_seed(42, "psi", "vanilla", "honest:honest", 0);
        assert_ne!(s1, s2);
        assert_ne!(s1, s3);
        assert_ne!(s1, s4);
    }

    #[test]
    fn manifest_roundtrip_json() {
        let mut params = BTreeMap::new();
        params.insert("psi.set_size".to_string(), "4".to_string());
        params.insert(
            "psi.overlap_distribution".to_string(),
            "Uniform".to_string(),
        );
        let m = ReproducibilityManifest {
            schema_version: SCHEMA_VERSION,
            git_commit: "abcdef0".to_string(),
            timestamp_utc: "2026-04-30T00:00:00Z".to_string(),
            platform: "linux-x86_64".to_string(),
            n_per_cell: 30,
            overall_seed: 0xdead_beef,
            per_cell_seeds: vec![CellSeedRecord {
                challenge: "psi".to_string(),
                agent: "cbcl".to_string(),
                attacker: "honest:honest-cooperative".to_string(),
                trial: 0,
                seed: 1,
            }],
            dialect_hashes: canonical_dialect_hashes(),
            attacker_version: "0.1.0+abcdef0".to_string(),
            distribution_params: params,
        };
        let json = m.to_json();
        let m2 = ReproducibilityManifest::from_json(&json).expect("parses");
        assert_eq!(m, m2);
        // Top-level field is schema_version.
        let v: serde_json::Value = serde_json::from_str(&json).unwrap();
        assert_eq!(v.get("schema_version").and_then(|x| x.as_u64()), Some(1));
    }

    #[test]
    fn iso8601_format_basic() {
        // 2020-01-01T00:00:00Z = 1577836800
        let s = format_iso8601(1_577_836_800);
        assert_eq!(s, "2020-01-01T00:00:00Z");
    }

    #[test]
    fn current_platform_nonempty() {
        let p = current_platform();
        assert!(p.contains('-'), "expected OS-ARCH format, got {}", p);
    }
}
