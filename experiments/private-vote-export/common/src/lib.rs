#![no_std]
extern crate alloc;

use alloc::{
    collections::{BTreeMap, BTreeSet},
    format,
    string::{String, ToString},
    vec::Vec,
};
use cbcl_core::{
    message::Message,
    sexpr::{Atom, SExpr},
    state::Act,
    store::ThreadId,
};
use cbcl_parser::state_exports::{admit, parse_and_install_dialect, Admission};
use ed25519_dalek::{Signature, VerifyingKey};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

pub const MAX_INPUT: usize = 131_072;
pub const MAX_MESSAGES: usize = 32;
pub const MAX_PARTICIPANTS: usize = 8;
pub const MAX_SOURCE: usize = 8192;
pub const MAX_MESSAGE: usize = 4096;
pub const SEMANTICS: &str = "cbcl-native-6e3ad4e/private-vote-export-v1";
pub const DIALECT: &str = r#"(define private-vote (cbcl) @alice
  (extend open (to question options) (tell to :question question :options options))
  (extend discuss (to text) (tell to :text text))
  (extend vote (to choice) (tell to :choice choice))
  (shape open (require :question string) (require :options list))
  (shape discuss (require :text string))
  (shape vote (require :choice string) (require :clock hlc))
  (protocol (then begin open) (then open discuss) (then open vote))
  (state (question (initial open :question)) (options (initial open :options))
    (discussion (events discuss :text))
    (domain vote :choice options)
    (ballots (lww-per-signer vote :choice :clock))
    (tally (histogram ballots))))"#;

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct Participant {
    pub label: String,
    pub key: [u8; 32],
}
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct Record {
    pub signer: usize,
    pub canonical: String,
    pub signature: Vec<u8>,
}
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct Input {
    pub dialect: String,
    pub thread: String,
    pub participants: Vec<Participant>,
    pub messages: Vec<Record>,
    pub salt: [u8; 32],
    pub closure_signatures: Vec<Vec<u8>>,
}
/// Public statement. `dialect` is native content identity, `source_commitment`
/// hashes exact installed source, and `semantics` pins this consumer's rules.
/// Participants are in label order. Counts include every admitted covered act;
/// ballot_count counts current eligible ballots after native replacement/HLC.
/// covered_set_commitment is salted; neither salt nor ballot map is exported.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct Journal {
    pub semantics: String,
    pub dialect: String,
    pub source_commitment: [u8; 32],
    pub thread: String,
    pub participants: Vec<Participant>,
    pub covered_count: u64,
    pub covered_set_commitment: [u8; 32],
    pub ballot_count: u64,
    pub tally: BTreeMap<String, u64>,
}
fn hash<T: Serialize>(domain: &[u8], value: &T) -> Result<[u8; 32], String> {
    let bytes = postcard::to_allocvec(value).map_err(|e| e.to_string())?;
    let mut h = Sha256::new();
    h.update(domain);
    h.update(bytes);
    Ok(h.finalize().into())
}
fn scope(input: &Input) -> (&str, &str, &str, &[Participant]) {
    (
        SEMANTICS,
        &input.dialect,
        &input.thread,
        &input.participants,
    )
}
/// Signing API: scope and exact canonical bytes; signatures themselves are excluded.
pub fn message_digest(input: &Input, record: &Record) -> Result<[u8; 32], String> {
    hash(
        b"cbcl/private-vote/message/v1\0",
        &(scope(input), record.signer as u64, &record.canonical),
    )
}
/// Commits a sorted exact (signer,canonical) set, not delivery order or signatures.
/// Bounds are checked here too, so signing callers cannot allocate unbounded sets.
pub fn closure_digest(input: &Input) -> Result<[u8; 32], String> {
    bounds(input)?;
    let mut set: Vec<_> = input
        .messages
        .iter()
        .map(|r| (r.signer as u64, r.canonical.as_str()))
        .collect();
    set.sort();
    let commitment = hash(
        b"cbcl/private-vote/set/v1\0",
        &(scope(input), input.salt, &set),
    )?;
    hash(
        b"cbcl/private-vote/closure/v1\0",
        &(scope(input), input.messages.len() as u64, commitment),
    )
}
fn bounds(i: &Input) -> Result<(), String> {
    if i.dialect.len() > MAX_SOURCE
        || i.thread.is_empty()
        || i.thread.len() > 128
        || i.participants.is_empty()
        || i.participants.len() > MAX_PARTICIPANTS
        || i.messages.is_empty()
        || i.messages.len() > MAX_MESSAGES
        || i.closure_signatures.len() > MAX_PARTICIPANTS
    {
        return Err("input bounds".into());
    }
    if i.messages
        .iter()
        .any(|r| r.canonical.len() > MAX_MESSAGE || r.signature.len() > 64)
        || i.closure_signatures.iter().any(|s| s.len() > 64)
    {
        return Err("record bounds".into());
    }
    for p in &i.participants {
        if p.label.len() < 2
            || p.label.len() > 64
            || !p.label.starts_with('@')
            || !p.label[1..]
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'-')
        {
            return Err("invalid label".into());
        }
    }
    Ok(())
}
fn verify(key: &[u8; 32], digest: [u8; 32], signature: &[u8]) -> Result<(), String> {
    let key = VerifyingKey::from_bytes(key).map_err(|_| String::from("invalid key"))?;
    let sig = Signature::from_slice(signature).map_err(|_| String::from("signature length"))?;
    key.verify_strict(&digest, &sig)
        .map_err(|_| String::from("invalid signature"))
}
/// Entire guest computation, including authentication, closure, admission and fold.
pub fn compute(bytes: &[u8]) -> Result<Journal, String> {
    if bytes.len() > MAX_INPUT {
        return Err("MAX_INPUT".into());
    }
    let i: Input = serde_json::from_slice(bytes).map_err(|e| e.to_string())?;
    bounds(&i)?;
    if i.dialect != DIALECT {
        return Err("unexpected dialect source".into());
    }
    let mut keys = BTreeSet::new();
    for (n, p) in i.participants.iter().enumerate() {
        if n > 0 && i.participants[n - 1].label >= p.label {
            return Err("roster order/duplicate label".into());
        }
        if !keys.insert(p.key) {
            return Err("duplicate key".into());
        }
    }
    if i.closure_signatures.len() != i.participants.len() {
        return Err("missing closure signer".into());
    }
    let closure = closure_digest(&i)?;
    for (p, s) in i.participants.iter().zip(&i.closure_signatures) {
        verify(&p.key, closure, s)?;
    }
    let registry =
        parse_and_install_dialect(&cbcl_parser::parse(&i.dialect).map_err(|e| e.to_string())?)?;
    let d = registry.iter().last().ok_or("missing dialect")?;
    let mut pending = Vec::new();
    let mut addresses = BTreeSet::new();
    let mut roots = 0;
    for r in &i.messages {
        let p = i.participants.get(r.signer).ok_or("outsider signer")?;
        verify(&p.key, message_digest(&i, r)?, &r.signature)?;
        let msg = cbcl_parser::parse_message(
            &cbcl_parser::parse(&r.canonical).map_err(|e| e.to_string())?,
        )?;
        match &msg {
            Message::Dialect {
                dialect_name,
                inner,
            } if dialect_name == "private-vote"
                && matches!(inner.as_ref(), Message::Simple { .. }) =>
            {
                ()
            }
            _ => return Err("single dialect wrapper required".into()),
        }
        if cbcl_core::intend::canonical_text(&msg) != r.canonical {
            return Err("noncanonical message".into());
        }
        match msg.innermost_simple() {
            Some(Message::Simple {
                params,
                thread,
                caused_by,
                ..
            }) if params.windows(2).filter(|kv| matches!(&kv[0], SExpr::Atom(Atom::Keyword(k)) if k == "from")).count() == 1
                && params.windows(2).any(|kv| matches!((&kv[0], &kv[1]), (SExpr::Atom(Atom::Keyword(k)), SExpr::Atom(Atom::Symbol(v))) if k == "from" && v == &p.label))
                && thread.as_deref() == Some(i.thread.as_str())
                && caused_by.is_some() =>
            {
                ()
            }
            _ => return Err("from/thread/context mismatch".into()),
        }
        let act = Act::from_message(msg, &p.label)?;
        if !addresses.insert(act.address.clone()) {
            return Err("duplicate act".into());
        }
        if act.verb == "open" {
            roots += 1;
            if act.fields.get("options")
                != Some(&cbcl_parser::parse("(\"yes\" \"no\")").map_err(|e| e.to_string())?)
            {
                return Err("options must be yes/no".into());
            }
        } else if act.verb == "vote" {
            if !matches!(act.fields.get("choice"),Some(SExpr::Atom(Atom::Str(s))) if s=="yes" || s=="no")
            {
                return Err("invalid choice".into());
            }
        } else if act.verb != "discuss" {
            return Err("unexpected act".into());
        }
        pending.push(act);
    }
    if roots != 1 {
        return Err("exactly one opener required".into());
    }
    pending.sort_by(|a, b| a.address.cmp(&b.address));
    let mut accepted = Vec::new();
    while !pending.is_empty() {
        let mut retry = Vec::new();
        let before = accepted.len();
        for act in pending {
            match admit(d, &ThreadId(i.thread.clone()), &accepted, &act) {
                Admission::Accepted => accepted.push(act),
                Admission::Pending => retry.push(act),
                Admission::Rejected(e) => return Err(format!("native rejection: {e}")),
            }
        }
        if accepted.len() == before {
            return Err("unresolved causality".into());
        }
        pending = retry;
    }
    let folded = cbcl_core::escrow::fold_instance(d, &i.thread, &accepted);
    let state: serde_json::Value =
        serde_json::from_str(&cbcl_core::state::render_json(&folded)).map_err(|e| e.to_string())?;
    let tally: BTreeMap<String, u64> =
        serde_json::from_value(state["tally"].clone()).map_err(|e| e.to_string())?;
    let ballot_count = tally.values().sum();
    if ballot_count > i.participants.len() as u64 || tally.keys().any(|k| k != "yes" && k != "no") {
        return Err("invalid native tally".into());
    }
    let mut set: Vec<_> = i
        .messages
        .iter()
        .map(|r| (r.signer as u64, r.canonical.as_str()))
        .collect();
    set.sort();
    Ok(Journal {
        semantics: SEMANTICS.into(),
        dialect: cbcl_core::canonical::dialect_name(d),
        source_commitment: Sha256::digest(i.dialect.as_bytes()).into(),
        thread: i.thread.clone(),
        participants: i.participants.clone(),
        covered_count: i.messages.len() as u64,
        covered_set_commitment: hash(b"cbcl/private-vote/set/v1\0", &(scope(&i), i.salt, &set))?,
        ballot_count,
        tally,
    })
}
