use crate::{
    canonical::canonical_encode,
    sexpr::{Atom, SExpr},
    state::{Act, Value},
};
use alloc::{
    collections::{BTreeMap, BTreeSet},
    format,
    string::{String, ToString},
    vec::Vec,
};
use sha2::{Digest, Sha256};
/// Financial scope for a collective pool; never an authenticated key identifier.
pub const COLLECTIVE_POOL: &str = "$collective";
pub type Result<T> = core::result::Result<T, String>;
pub(crate) fn text(s: &str) -> SExpr {
    SExpr::Atom(Atom::Str(s.into()))
}
pub(crate) fn strings(xs: &BTreeSet<String>) -> SExpr {
    SExpr::List(xs.iter().map(|s| text(s)).collect())
}
pub(crate) fn digest(xs: Vec<SExpr>) -> String {
    let bytes = canonical_encode(&SExpr::List(xs));
    let hash = Sha256::digest(&bytes);
    let mut out = String::from("sha256-");
    for b in hash {
        out.push_str(&format!("{b:02x}"));
    }
    out
}
/// Verification authenticates keys, not merely the presence of a signed wrapper.
pub trait Authentication {
    fn verify(&self, key: &str, preimage: &[u8], signature: &[u8]) -> bool;
    /// Verify the owner's actual signature AND normal CBCL protocol admission.
    /// The core additionally rebuilds the act and checks pinned shape/cast/context.
    fn authenticate_act(&self, act: &Act) -> bool;
}
/// A complete, nonforking, durable log PER (context, validator), never a shared ledger.
/// `None` expected sequence atomically creates a previously unused identity.
/// `Some(n)` appends iff the existing complete log has exactly n events.
/// An error MUST mean no append occurred. The host must fence stale processes and
/// never lose, truncate or fork an acknowledged log, including across recovery.
pub trait Journal {
    fn load(&self, context: &str, validator: &str) -> Result<Option<Vec<Event>>>;
    fn append(
        &mut self,
        context: &str,
        validator: &str,
        expected: Option<u64>,
        event: &Event,
    ) -> Result<()>;
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum VoteKind {
    Operation,
    Effects,
    Cancel,
    Seal,
    Checkpoint,
    CancelRequest,
    CheckpointRequest,
}
impl VoteKind {
    fn tag(self) -> &'static str {
        match self {
            Self::Operation => "operation",
            Self::Effects => "effects",
            Self::Cancel => "cancel",
            Self::Seal => "seal",
            Self::Checkpoint => "checkpoint",
            Self::CancelRequest => "owner-cancel",
            Self::CheckpointRequest => "owner-checkpoint",
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(deny_unknown_fields))]
pub struct Vote {
    pub context: String,
    pub kind: VoteKind,
    pub payload: String,
    pub signer: String,
    pub signature: Vec<u8>,
}
impl Vote {
    pub fn preimage(&self) -> Vec<u8> {
        canonical_encode(&SExpr::List(alloc::vec![
            text("cbcl/quorum-budget/v1"),
            text(&self.context),
            text(self.kind.tag()),
            text(&self.payload),
            text(&self.signer)
        ]))
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SigningRequest {
    pub(crate) vote: Vote,
}
impl SigningRequest {
    pub fn signer(&self) -> &str {
        &self.vote.signer
    }
    pub fn preimage(&self) -> Vec<u8> {
        self.vote.preimage()
    }
    pub fn attach(self, signature: Vec<u8>) -> Vote {
        Vote {
            signature,
            ..self.vote
        }
    }
}
/// Untrusted wire proof. Receipt always re-verifies all distinct member signatures.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(deny_unknown_fields))]
pub struct Certificate {
    pub kind: VoteKind,
    pub payload: String,
    pub votes: Vec<Vote>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(deny_unknown_fields))]
pub struct SealReport {
    pub epoch: String,
    pub signed: BTreeSet<String>,
    pub vote: Vote,
}
impl SealReport {
    pub fn payload(context: &str, epoch: &str, signed: &BTreeSet<String>) -> String {
        digest(alloc::vec![
            text("cbcl/seal/v1"),
            text(context),
            text(epoch),
            strings(signed)
        ])
    }
}
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(deny_unknown_fields))]
pub struct Resources {
    pub rights: i128,
    pub headroom: i128,
}
impl Resources {
    pub(crate) fn add(self, b: Self) -> Result<Self> {
        Ok(Self {
            rights: self.rights.checked_add(b.rights).ok_or("rights overflow")?,
            headroom: self
                .headroom
                .checked_add(b.headroom)
                .ok_or("headroom overflow")?,
        })
    }
    pub(crate) fn sub(self, b: Self) -> Result<Self> {
        Ok(Self {
            rights: self.rights.checked_sub(b.rights).ok_or("rights overflow")?,
            headroom: self
                .headroom
                .checked_sub(b.headroom)
                .ok_or("headroom overflow")?,
        })
    }
    pub(crate) fn nonnegative(self) -> bool {
        self.rights >= 0 && self.headroom >= 0
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(deny_unknown_fields))]
pub struct Manifest {
    pub account: String,
    pub parent: String,
    pub depth: u64,
    pub held: BTreeSet<String>,
    pub refunded: BTreeSet<String>,
    pub credited: BTreeSet<String>,
    pub allocation: Resources,
}
impl Manifest {
    pub fn id(&self, context: &str) -> String {
        digest(alloc::vec![
            text("cbcl/epoch/v1"),
            text(context),
            text(&self.account),
            text(&self.parent),
            text(&self.depth.to_string()),
            strings(&self.held),
            strings(&self.refunded),
            strings(&self.credited),
            text(&self.allocation.rights.to_string()),
            text(&self.allocation.headroom.to_string())
        ])
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(deny_unknown_fields))]
pub struct Proposal {
    pub manifest: Manifest,
    pub reports: Vec<SealReport>,
    pub authorization: Vote,
}
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(deny_unknown_fields))]
pub struct Checkpoint {
    pub proposal: Proposal,
    pub certificate: Certificate,
}
/// Typed persistence format. Deserializing an Event confers no trust: recovery
/// replays all semantic checks, proof signatures and decision guards.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Event {
    Initialize,
    Candidate(Act),
    Certificate(Certificate),
    Proposal(Proposal),
    Sign(String),
    Effect(String),
    Fence(Vote),
    Seal(String),
    Endorse(String),
    Checkpoint(Checkpoint),
    Release(String),
    Install(String),
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Limits {
    pub operations: usize,
    pub checkpoints: usize,
    pub events: u64,
    pub object_bytes: usize,
    pub signature_bytes: usize,
}
impl Default for Limits {
    fn default() -> Self {
        Self {
            operations: 4096,
            checkpoints: 1024,
            events: 65536,
            object_bytes: 1_048_576,
            signature_bytes: 8192,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FinalizedView {
    pub ownership: crate::escrow::Ownership,
    pub context: String,
    pub evidence_digest: String,
    pub rights: BTreeMap<String, i128>,
    pub headroom: Option<BTreeMap<String, i128>>,
    pub value: i128,
    pub finalized: BTreeSet<String>,
    pub pending: BTreeSet<String>,
}
impl FinalizedView {
    /// This is a dependency-closed local certificate view, NOT a certified latest
    /// balance snapshot. No completeness/freshness read protocol is implied.
    pub fn value(&self) -> Value {
        let t = |s: &str| Value::Str(s.into());
        let mut xs = alloc::vec![
            (t("status"), t("finalized-view")),
            (t("completeness"), t("unknown")),
            (t("context"), t(&self.context)),
            (t("evidence-digest"), t(&self.evidence_digest)),
            (t("value"), Value::Int(self.value))
        ];
        let balances = |m: &BTreeMap<String, i128>| {
            Value::Map(m.iter().map(|(k, v)| (t(k), Value::Int(*v))).collect())
        };
        if self.ownership == crate::escrow::Ownership::Collective {
            xs.push((t("ownership"), t("collective")));
            xs.push((
                t("rights"),
                Value::Int(self.rights.get(COLLECTIVE_POOL).copied().unwrap_or(0)),
            ));
            if let Some(h) = &self.headroom {
                xs.push((
                    t("headroom"),
                    Value::Int(h.get(COLLECTIVE_POOL).copied().unwrap_or(0)),
                ));
            }
        } else {
            xs.push((t("rights"), balances(&self.rights)));
            if let Some(h) = &self.headroom {
                xs.push((t("headroom"), balances(h)));
            }
        }
        xs.push((
            t("finalized"),
            Value::List(self.finalized.iter().map(|s| t(s)).collect()),
        ));
        xs.push((
            t("pending"),
            Value::List(self.pending.iter().map(|s| t(s)).collect()),
        ));
        Value::Map(xs)
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Operation {
    pub act: Act,
    pub account: String,
    pub epoch: String,
    pub cost: Resources,
    pub credits: BTreeMap<String, Resources>,
}
