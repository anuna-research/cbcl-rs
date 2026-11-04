//! Checkpoint chains: sequential verification from a receiver-pinned start
//! (SPEC-035 REQ-3505, CON-3503).
use crate::{Checkpoint, Proof, Result, Verifier, MAX_PACKAGE};
use serde::{Deserialize, Serialize};

/// Most links a chain may carry (REQ-3508).
pub const MAX_LINKS: usize = 64;

/// An ordered list of proofs over one profile. Fields are private: a chain is
/// only built through `new` or `from_json`, and neither establishes validity.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Chain {
    profile: [u8; 32],
    links: Vec<Proof>,
}
impl Chain {
    /// Rejects more than `MAX_LINKS` links. Does not verify anything.
    pub fn new(profile: [u8; 32], links: Vec<Proof>) -> Result<Self> {
        let chain = Self { profile, links };
        chain.check_len()?;
        Ok(chain)
    }
    pub fn profile(&self) -> [u8; 32] {
        self.profile
    }
    pub fn links(&self) -> &[Proof] {
        &self.links
    }
    /// Rejects an over-long chain, a link with an invalid transcript size and
    /// a package over `MAX_PACKAGE` bytes.
    pub fn to_json(&self) -> Result<Vec<u8>> {
        self.check_shape()?;
        let bytes = serde_json::to_vec(self).map_err(|e| e.to_string())?;
        if bytes.len() > MAX_PACKAGE {
            return Err("chain package exceeds limit".into());
        }
        Ok(bytes)
    }
    /// Recognises against CON-3502: unknown members, trailing input, a package
    /// over `MAX_PACKAGE` bytes, more than `MAX_LINKS` links and a link with an
    /// invalid transcript size are rejected.
    pub fn from_json(bytes: &[u8]) -> Result<Self> {
        if bytes.len() > MAX_PACKAGE {
            return Err("chain package exceeds limit".into());
        }
        let chain: Self = serde_json::from_slice(bytes).map_err(|e| e.to_string())?;
        chain.check_shape()?;
        Ok(chain)
    }
    fn check_len(&self) -> Result<()> {
        if self.links.len() > MAX_LINKS {
            return Err("chain exceeds link limit".into());
        }
        Ok(())
    }
    fn check_shape(&self) -> Result<()> {
        self.check_len()?;
        self.links.iter().try_for_each(Proof::check_size)
    }
    /// Verifies every link in order from the receiver's `start` (CON-3503).
    /// Returns the last link's after checkpoint, or `start` for an empty chain.
    /// Rejects a chain or link whose profile differs from the verifier's, a
    /// first link whose before differs from `start`, a link whose before differs
    /// from the previous after, a link the verifier rejects, and a final
    /// checkpoint that differs from `expected_end` when one is given.
    pub fn verify(
        &self,
        verifier: &Verifier,
        start: Checkpoint,
        expected_end: Option<Checkpoint>,
    ) -> Result<Checkpoint> {
        self.check_len()?;
        let id = verifier.profile.id();
        if self.profile != id {
            return Err("chain profile differs from verifier profile".into());
        }
        let mut current = start;
        for (i, link) in self.links.iter().enumerate() {
            let statement = &link.statement;
            if statement.profile != id {
                return Err(format!("link {i}: foreign profile"));
            }
            if statement.before != current {
                return Err(format!("link {i}: before differs from running checkpoint"));
            }
            verifier
                .verify(link, statement)
                .map_err(|e| format!("link {i}: {e}"))?;
            current = statement.after;
        }
        if expected_end.is_some_and(|end| end != current) {
            return Err("final checkpoint differs from expected end".into());
        }
        Ok(current)
    }
}
