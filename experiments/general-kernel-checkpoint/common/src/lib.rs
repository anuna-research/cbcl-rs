//! The guest calls the existing kernel; no dialect-specific transitions live here.
use cbcl_core::{
    canonical::dialect_name,
    intend::canonical_text,
    message::Message,
    state::{render_json, Act},
    store::ThreadId,
};
use cbcl_parser::{
    parse, parse_and_install_dialect, parse_message,
    state_exports::{admit, Admission},
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::BTreeSet;

pub const MAX_INPUT: usize = 1024 * 1024;
pub const SEMANTICS: &str = "cbcl-rs:c45b468:state_exports::admit+escrow::fold_instance";
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Input {
    pub dialect: String,
    pub thread: String,
    pub messages: Vec<Record>,
}
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Record {
    pub signer: String,
    pub canonical: String,
}
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct Journal {
    pub version: u32,
    pub semantics: String,
    pub authentication: String,
    pub dialect_sources_hash: [u8; 32],
    pub dialect: String,
    pub thread: String,
    pub messages_hash: [u8; 32],
    pub count: u32,
    pub state_hash: [u8; 32],
}
pub struct Computed {
    pub journal: Journal,
    pub state: String,
}
fn hash(domain: &[u8], parts: &[&[u8]]) -> [u8; 32] {
    let mut h = Sha256::new();
    for part in std::iter::once(domain).chain(parts.iter().copied()) {
        h.update((part.len() as u64).to_le_bytes());
        h.update(part);
    }
    h.finalize().into()
}
pub fn state_hash(state: &str) -> [u8; 32] {
    hash(b"cbcl-checkpoint-state-v1", &[state.as_bytes()])
}
fn context(m: &Message, name: &str, identity: &str) -> Result<(), String> {
    match m {
        Message::Dialect {
            dialect_name,
            inner,
        } => {
            if dialect_name != name && dialect_name != identity {
                return Err("dialect context mismatch".into());
            }
            context(inner, name, identity)
        }
        Message::Wrapped { content, .. } => context(content, name, identity),
        Message::Simple { .. } => Ok(()),
        Message::Meta { .. } => Err("meta message is not a state act".into()),
    }
}
pub fn compute(bytes: &[u8]) -> Result<Computed, String> {
    if bytes.len() > MAX_INPUT {
        return Err("input byte bound".into());
    }
    let input: Input = serde_json::from_slice(bytes).map_err(|e| e.to_string())?;
    if input.dialect.len() > 65536
        || input.thread.is_empty()
        || input.thread.len() > 1024
        || input.messages.len() > 256
    {
        return Err("input bounds".into());
    }
    let registry = parse_and_install_dialect(&parse(&input.dialect).map_err(|e| e.to_string())?)?;
    let dialect = registry.iter().last().ok_or("missing dialect")?;
    if dialect.state.is_none() {
        return Err("dialect has no state projection".into());
    }
    let identity = dialect_name(dialect);
    let mut acts = Vec::new();
    let mut seen = BTreeSet::new();
    for record in &input.messages {
        if record.canonical.len() > 8192 || record.signer.is_empty() || record.signer.len() > 1024 {
            return Err("record bounds".into());
        }
        let message = parse_message(&parse(&record.canonical).map_err(|e| e.to_string())?)
            .map_err(|e| e.to_string())?;
        if canonical_text(&message) != record.canonical {
            return Err("noncanonical message".into());
        }
        context(&message, &dialect.name, &identity)?;
        let simple = message.innermost_simple().ok_or("missing simple message")?;
        if simple.thread() != Some(input.thread.as_str()) {
            return Err("thread context mismatch".into());
        }
        let act = Act::from_message(message, &record.signer)?;
        if !seen.insert(act.address.clone()) {
            return Err("duplicate act address".into());
        }
        acts.push(act);
    }
    // Deterministic retry of the native consumer admission operation from empty.
    acts.sort_by(|a, b| a.address.cmp(&b.address));
    let mut accepted = Vec::new();
    let mut pending = acts;
    let thread = ThreadId(input.thread.clone());
    while !pending.is_empty() {
        let before = pending.len();
        let mut remaining = Vec::new();
        for act in pending {
            match admit(dialect, &thread, &accepted, &act) {
                Admission::Accepted => accepted.push(act),
                Admission::Pending => remaining.push(act),
                Admission::Rejected(reason) => return Err(format!("rejected: {reason}")),
            }
        }
        if remaining.len() == before {
            return Err("unresolved causal dependencies".into());
        }
        pending = remaining;
    }
    let state = render_json(&cbcl_core::escrow::fold_instance(
        dialect,
        &input.thread,
        &accepted,
    ));
    let mut records: Vec<_> = input.messages.iter().collect();
    records.sort_by(|a, b| a.canonical.cmp(&b.canonical).then(a.signer.cmp(&b.signer)));
    let count = (records.len() as u32).to_le_bytes();
    let mut fields: Vec<&[u8]> = vec![&count];
    for r in records {
        fields.push(r.signer.as_bytes());
        fields.push(r.canonical.as_bytes());
    }
    let journal = Journal {
        version: 1,
        semantics: SEMANTICS.into(),
        authentication: "asserted-signer-labels; no Ed25519 verification".into(),
        dialect_sources_hash: hash(
            b"cbcl-checkpoint-dialect-source-closure-v1",
            &[input.dialect.as_bytes()],
        ),
        dialect: identity,
        thread: input.thread,
        messages_hash: hash(b"cbcl-checkpoint-message-set-v1", &fields),
        count: input.messages.len() as u32,
        state_hash: state_hash(&state),
    };
    Ok(Computed { journal, state })
}
