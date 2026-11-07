//! Native-computed, payload-free repeat-position continuation.
//!
//! Like Summary, decoding recognizes a candidate, not snapshot truth. A usable
//! store port additionally verifies the actual enclosing native certificate and
//! exact summary commitment. No boolean flag or wire-supplied rank is accepted.
use crate::{
    codec::{put_string, put_u32, Reader},
    hash, Error, Hash, Result,
};
use alloc::{borrow::Cow, sync::Arc};
use alloc::{string::String, vec::Vec};
use cbcl_core::{
    canonical::dialect_hash,
    dialect::base_dialect,
    message::{CausedBy, Message, WrapperType},
    protocol::CausalProtocol,
    state::Act,
    store::{
        ContentHash, MaterializedPositions, MessageStore, PositionContext, PositionMetadata,
        ThreadId,
    },
};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

const MAX_RECORDS: usize = 65536;
const MAX_BYTES: usize = 16 * 1024 * 1024;
fn protocol_code(p: Option<&CausalProtocol>) -> Hash {
    let mut d = base_dialect();
    d.causal_protocol = p.cloned();
    hash(
        b"cbcl/checkpoint/progress-resume/schema-v1",
        dialect_hash(&d).as_bytes(),
    )
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProgressResume {
    protocol: Option<Arc<CausalProtocol>>,
    verb: String,
    positions: Option<MaterializedPositions>,
}
impl ProgressResume {
    pub fn new(protocol: Option<&CausalProtocol>, verb: &str) -> Result<Self> {
        // Validate even before a root arrives; native protocol-none progress is 0.
        MaterializedPositions::new(
            PositionContext {
                code: protocol_code(protocol),
                root: ContentHash(String::new()),
                thread: ThreadId(String::new()),
            },
            protocol,
        )
        .map_err(|_| Error::Invalid("progress protocol"))?;
        Ok(Self {
            protocol: protocol.map(|p| Arc::new(p.clone())),
            verb: verb.into(),
            positions: None,
        })
    }
    /// All fresh accepted messages must pass here, including non-state ancestors.
    /// Authentication and ordinary native admission belong to the caller.
    pub fn apply(&mut self, act: &Act) -> Result<()> {
        let simple = act
            .message
            .innermost_simple()
            .ok_or(Error::Invalid("progress simple"))?;
        let native = cbcl_core::equivocation::message_content_hash(simple);
        if act.address != cbcl_core::state::wire_address(simple)
            || act.verb
                != simple
                    .performative()
                    .ok_or(Error::Invalid("progress verb"))?
                    .name()
        {
            return Err(Error::Invalid("progress derived act"));
        }
        // The native kernel defines protocol-free progress as zero for every
        // history. No root, thread or retained ancestry is needed in that case.
        if self.protocol.is_none() {
            return Ok(());
        }
        let thread = ThreadId(
            simple
                .thread()
                .ok_or(Error::Invalid("progress thread"))?
                .into(),
        );
        if let Some(p) = &mut self.positions {
            if p.len() >= MAX_RECORDS && !p.contains(&native) {
                return Err(Error::Budget);
            }
            return p
                .apply_accepted(&act.message)
                .map_err(|_| Error::Invalid("progress native position"));
        }
        if act.message.wrapper_type() != Some(WrapperType::WithRoles)
            || !matches!(simple.caused_by(), Some(CausedBy::Begin))
        {
            return Err(Error::Invalid("progress first act must be root"));
        }
        let mut p = MaterializedPositions::new(
            PositionContext {
                code: protocol_code(self.protocol.as_deref()),
                root: ContentHash(native),
                thread,
            },
            self.protocol.as_deref(),
        )
        .map_err(|_| Error::Invalid("progress protocol"))?;
        p.apply_accepted(&act.message)
            .map_err(|_| Error::Invalid("progress root"))?;
        self.positions = Some(p);
        Ok(())
    }
    pub fn progress(&self) -> usize {
        self.positions
            .as_ref()
            .map(|p| p.progress(&self.verb))
            .unwrap_or(0)
    }
    pub fn progress_for(&self, verb: &str) -> usize {
        self.positions
            .as_ref()
            .map(|p| p.progress(verb))
            .unwrap_or(0)
    }
    pub fn verb(&self) -> &str {
        &self.verb
    }
    pub fn protocol(&self) -> Option<&CausalProtocol> {
        self.protocol.as_deref()
    }
    pub(crate) fn materialized(&self) -> Option<&MaterializedPositions> {
        self.positions.as_ref()
    }
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::new();
        put_u32(&mut out, 1);
        out.extend(protocol_code(self.protocol.as_deref()));
        put_string(&mut out, &self.verb);
        put_u32(&mut out, usize::from(self.positions.is_some()));
        if let Some(p) = &self.positions {
            put_string(&mut out, &p.context().root.0);
            put_string(&mut out, &p.context().thread.0);
            let records: Vec<_> = p.metadata().collect();
            put_u32(&mut out, records.len());
            for r in records {
                put_string(&mut out, &r.id);
                put_string(&mut out, &r.verb);
                match &r.cause {
                    None => put_u32(&mut out, 0),
                    Some(CausedBy::Begin) => put_u32(&mut out, 1),
                    Some(CausedBy::Single(h)) => {
                        put_u32(&mut out, 2);
                        put_string(&mut out, h);
                    }
                    Some(CausedBy::Multiple(hs)) => {
                        put_u32(&mut out, 3);
                        put_u32(&mut out, hs.len());
                        for h in hs {
                            put_string(&mut out, h);
                        }
                    }
                }
            }
        }
        out
    }
    /// Pure structural/native-relation recognition. Snapshot truth is external;
    /// this method cannot install a trusted MessageStore port.
    pub fn decode(bytes: &[u8], expected_protocol: Option<&CausalProtocol>) -> Result<Self> {
        let mut r = Reader::new(bytes, MAX_BYTES)?;
        if r.u32()? != 1 || r.hash()? != protocol_code(expected_protocol) {
            return Err(Error::Invalid("progress schema/protocol"));
        }
        let verb = r.string(4096)?;
        let tag = r.u32()?;
        let positions = match tag {
            0 => None,
            1 => {
                let root = r.string(256)?;
                crate::certificate::native_id(&root)?;
                let thread = r.string(4096)?;
                let n = r.count(MAX_RECORDS)?;
                let mut records = Vec::new();
                let mut previous: Option<String> = None;
                for _ in 0..n {
                    let id = r.string(256)?;
                    crate::certificate::native_id(&id)?;
                    if previous.as_ref().is_some_and(|p| p >= &id) {
                        return Err(Error::Invalid("progress record order"));
                    }
                    previous = Some(id.clone());
                    let verb = r.string(4096)?;
                    let cause = match r.u32()? {
                        0 => None,
                        1 => Some(CausedBy::Begin),
                        2 => {
                            let h = r.string(256)?;
                            crate::certificate::native_id(&crate::certificate::native(&h))?;
                            Some(CausedBy::Single(h))
                        }
                        3 => {
                            let n = r.count(256)?;
                            if n == 0 {
                                return Err(Error::Invalid("progress empty parents"));
                            }
                            let mut hs = Vec::new();
                            for _ in 0..n {
                                let h = r.string(256)?;
                                crate::certificate::native_id(&crate::certificate::native(&h))?;
                                if hs.last().is_some_and(|p| p >= &h) {
                                    return Err(Error::Invalid("progress parent order"));
                                }
                                hs.push(h);
                            }
                            Some(CausedBy::Multiple(hs))
                        }
                        _ => return Err(Error::Invalid("progress cause tag")),
                    };
                    records.push(PositionMetadata { id, verb, cause });
                }
                let context = PositionContext {
                    code: protocol_code(expected_protocol),
                    root: ContentHash(root),
                    thread: ThreadId(thread),
                };
                let p =
                    MaterializedPositions::restore_attested(context, expected_protocol, records)
                        .map_err(|_| Error::Invalid("progress native relation"))?;
                if !p.contains(&p.context().root.0) {
                    return Err(Error::Invalid("progress absent root"));
                }
                Some(p)
            }
            _ => return Err(Error::Invalid("progress presence tag")),
        };
        r.finish()?;
        let out = Self {
            protocol: expected_protocol.map(|p| Arc::new(p.clone())),
            verb,
            positions,
        };
        if out.encode() != bytes {
            return Err(Error::Invalid("progress canonical encoding"));
        }
        Ok(out)
    }
}

// Serde carries its expected protocol explicitly for intermediate host records.
// Summary's pinned decode_for must still compare it to the installed protocol.
impl Serialize for ProgressResume {
    fn serialize<S: Serializer>(&self, s: S) -> core::result::Result<S::Ok, S::Error> {
        (&self.protocol.as_deref(), self.encode()).serialize(s)
    }
}
impl<'de> Deserialize<'de> for ProgressResume {
    fn deserialize<D: Deserializer<'de>>(d: D) -> core::result::Result<Self, D::Error> {
        let (p, bytes) = <(Option<CausalProtocol>, Vec<u8>)>::deserialize(d)?;
        Self::decode(&bytes, p.as_ref()).map_err(serde::de::Error::custom)
    }
}

/// A public store adapter cannot be constructed from an unverified decode.
/// Its constructor verifies actual native endorsements plus the summary binding.
pub struct CertifiedProgressPort<'a, S> {
    inner: &'a S,
    resume: Option<Cow<'a, ProgressResume>>,
}
impl<'a, S: MessageStore> CertifiedProgressPort<'a, S> {
    /// Crate-only continuation seam. Client/Member owns accepted-history
    /// provenance; no caller-supplied flag can promote an arbitrary decode.
    /// Borrow the current cache, so a tail check does not clone its prefix.
    pub(crate) fn from_summary(
        inner: &'a S,
        summary: &'a crate::summary::Summary,
        context: &crate::certificate::Context,
    ) -> Result<Self> {
        let resume = summary.global_progress_resume();
        if let Some(r) = resume {
            if r.protocol() != context.target.causal_protocol.as_ref() {
                return Err(Error::Invalid("progress protocol context"));
            }
            if let Some(p) = r.materialized() {
                let thread = context
                    .target_root
                    .message()
                    .innermost_simple()
                    .and_then(Message::thread)
                    .ok_or(Error::Invalid("target thread"))?;
                if p.context().root.0 != context.target_root.id()?
                    || p.context().thread.0 != thread
                    || p.context().code != protocol_code(context.target.causal_protocol.as_ref())
                {
                    return Err(Error::Invalid("progress context"));
                }
            }
        } else if context
            .target
            .causal_protocol
            .as_ref()
            .is_some_and(|p| p.steps.keys().any(|name| name.contains('#')))
        {
            return Err(Error::Invalid("global progress cache absent"));
        }
        Ok(Self {
            inner,
            resume: resume.map(Cow::Borrowed),
        })
    }
    pub fn install_materialized_port(
        inner: &'a S,
        verb: &str,
        certificate: &crate::certificate::Certificate,
        context: &crate::certificate::Context,
        keys: &dyn crate::certificate::KeyVerifier,
    ) -> Result<Self> {
        certificate.verify(context, keys)?;
        let summary = crate::summary::Summary::decode_for(
            &certificate.summary,
            context.target.state.as_ref().ok_or(Error::Unsupported)?,
            context.target.causal_protocol.as_ref(),
        )?;
        let _ = verb; // R5 uses every native base verb in the global relation.
        let port = CertifiedProgressPort::from_summary(inner, &summary, context)?;
        let owned = port.resume.map(|r| Cow::Owned(r.into_owned()));
        Ok(Self {
            inner,
            resume: owned,
        })
    }
}
impl<S: MessageStore> MessageStore for CertifiedProgressPort<'_, S> {
    fn materialized_positions(&self) -> Option<&MaterializedPositions> {
        self.resume
            .as_deref()
            .and_then(ProgressResume::materialized)
    }
    fn lookup(&self, h: &ContentHash) -> Option<&Message> {
        self.inner.lookup(h)
    }
    fn lookup_in_thread(&self, h: &ContentHash, t: &ThreadId) -> Option<&Message> {
        self.inner.lookup_in_thread(h, t)
    }
    fn contains(&self, h: &ContentHash, t: &ThreadId) -> bool {
        self.inner.contains(h, t)
    }
    fn append(&mut self, _: ContentHash, _: ThreadId, _: Message) -> bool {
        false
    }
    fn frontier(&self, t: &ThreadId) -> Vec<&ContentHash> {
        self.inner.frontier(t)
    }
    fn causal_closure(&self, h: &ContentHash, t: &ThreadId) -> Vec<ContentHash> {
        self.inner.causal_closure(h, t)
    }
    fn envelope_in_thread(
        &self,
        h: &ContentHash,
        t: &ThreadId,
    ) -> Option<&cbcl_core::envelope::RedactedEnvelope> {
        self.inner.envelope_in_thread(h, t)
    }
    fn opened_in_thread(
        &self,
        h: &ContentHash,
        t: &ThreadId,
    ) -> Option<&cbcl_core::envelope::OpenedEnvelope> {
        self.inner.opened_in_thread(h, t)
    }
}
#[cfg(test)]
#[path = "progress_resume_tests.rs"]
mod tests;
