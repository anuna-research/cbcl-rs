use crate::{limbs, Result};
use cbcl_core::{
    canonical::dialect_hash,
    dialect::Dialect,
    message::Message,
    serializer::serialize,
    sexpr::{Atom, SExpr},
    state::{fold, render_json, Act},
    store::ThreadId,
};
use cbcl_parser::{
    parse_and_install_dialect, parse_message,
    state_exports::{admit, Admission},
};
use halo2_proofs::pasta::Fp;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::BTreeSet;

pub const MAX_CANDIDATES: usize = 8;
/// Kernel semantics revision bound into every profile identity. Bump it, and
/// regenerate `test-vectors/state-proof/*.json`, when admission or fold
/// semantics change (README, "Semantics version").
pub const SEMANTICS_VERSION: &str = "c9093e8";
/// Identity domain `cbcl-state-proof/relation-v1/<version>`.
pub(crate) fn relation_domain(version: &str) -> Vec<u8> {
    format!("cbcl-state-proof/relation-v1/{version}").into_bytes()
}
const MAX_SOURCE: usize = 65_536;
const MAX_MESSAGE: usize = 8_192;
const PARSER_FUEL: usize = 256;
fn parse_bounded(source: &str) -> Result<SExpr> {
    cbcl_parser::parser::parse_with_fuel(source, Some(PARSER_FUEL)).map_err(|e| e.to_string())
}

/// Public candidate vocabulary. `signer` must be established by the host.
#[derive(Clone, Debug)]
pub struct Candidate {
    pub canonical: String,
    pub signer: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Checkpoint {
    pub accepted: [u8; 32],
    pub state: [u8; 32],
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Statement {
    pub profile: [u8; 32],
    pub before: Checkpoint,
    pub after: Checkpoint,
    pub batch: [u8; 32],
}
impl Statement {
    pub(crate) fn instance(&self) -> Vec<Fp> {
        [
            self.profile,
            self.before.accepted,
            self.before.state,
            self.after.accepted,
            self.after.state,
            self.batch,
        ]
        .into_iter()
        .flat_map(limbs)
        .collect()
    }
}

#[derive(Clone, Debug)]
pub(crate) struct Row {
    pub checkpoint: Checkpoint,
    pub state: String,
    pub valid: bool,
}
impl Row {
    pub(crate) fn fields(&self) -> [Fp; 5] {
        let set = limbs(self.checkpoint.accepted);
        let state = limbs(self.checkpoint.state);
        [
            Fp::from(u64::from(self.valid)),
            set[0],
            set[1],
            state[0],
            state[1],
        ]
    }
}
#[derive(Clone, Debug)]
pub struct Profile {
    id: [u8; 32],
    #[cfg(test)]
    id_parts: Vec<Vec<u8>>,
    addresses: Vec<String>,
    pub(crate) rows: Vec<Row>,
    pub(crate) transitions: Vec<(usize, usize)>,
}

/// Domain-separated, length-prefixed hash. No ambiguous concatenation.
fn hash(domain: &[u8], parts: &[&[u8]]) -> [u8; 32] {
    let mut h = Sha256::new();
    for p in std::iter::once(domain).chain(parts.iter().copied()) {
        h.update((p.len() as u64).to_le_bytes());
        h.update(p);
    }
    h.finalize().into()
}
/// Profile identity: `hash` over the identity parts under `domain`.
fn relation_id(domain: &[u8], parts: &[&[u8]]) -> [u8; 32] {
    hash(domain, parts)
}
impl Profile {
    /// Compile the full bounded relation using the installed CBCL semantics.
    /// SIMPLIFY: exponential at <=8 candidates; replace enumeration with a
    /// constrained incremental admission/fold kernel before extending this bound.
    /// Trace: experiments/state-proof/BRIEF.md, scope and P5.
    pub fn compile(source: &str, thread: &str, candidates: &[Candidate]) -> Result<Self> {
        if candidates.len() > MAX_CANDIDATES
            || source.len() > MAX_SOURCE
            || thread.len() > 2048
            || candidates
                .iter()
                .any(|c| c.canonical.len() > MAX_MESSAGE || c.signer.len() > 2048)
        {
            return Err("profile resource limit".into());
        }
        let registry = parse_and_install_dialect(&parse_bounded(source)?)?;
        let d: Dialect = registry.iter().last().cloned().ok_or("missing dialect")?;
        if !d.roles.is_empty() {
            return Err("prototype supports role-free dialects only".into());
        }
        let clause = d.state.as_ref().ok_or("dialect has no state clause")?;
        if d.causal_protocol.is_none() {
            return Err("dialect has no protocol".into());
        }
        let mut acts = Vec::new();
        for c in candidates {
            let sexpr = parse_bounded(&c.canonical)?;
            let message = parse_message(&sexpr).map_err(|e| e.to_string())?;
            let act = Act::from_message(message, &c.signer)?;
            let canonical = serialize(&SExpr::from(&act.message));
            acts.push((act, canonical));
        }
        acts.sort_by(|a, b| a.0.address.cmp(&b.0.address));
        let mut seen = BTreeSet::new();
        if acts.iter().any(|(a, _)| !seen.insert(a.address.clone())) {
            return Err("duplicate candidate identity".into());
        }
        // The installed dialect chain and candidate bytes are verifier-owned.
        let dialect_text = serialize(&parse_bounded(source)?);
        let dialect_id = dialect_hash(&d);
        let mut parts = vec![
            dialect_text.as_bytes(),
            dialect_id.as_bytes(),
            thread.as_bytes(),
        ];
        for (act, text) in &acts {
            parts.extend([act.signer.as_bytes(), text.as_bytes()]);
        }
        let id = relation_id(&relation_domain(SEMANTICS_VERSION), &parts);
        #[cfg(test)]
        let id_parts = parts.iter().map(|p| p.to_vec()).collect();
        let thread_id = ThreadId(thread.into());
        let mut rows = Vec::new();
        for mask in 0..1usize << acts.len() {
            let selected: Vec<_> = acts
                .iter()
                .enumerate()
                .filter(|(i, _)| mask & (1 << i) != 0)
                .map(|(_, a)| a)
                .collect();
            let mut set_parts = vec![id.as_slice()];
            for (act, text) in &selected {
                set_parts.extend([act.signer.as_bytes(), text.as_bytes()]);
            }
            let accepted_root = hash(b"cbcl-state-proof/set-v1", &set_parts);
            let bindings_ok = selected.iter().all(|(a, _)| {
                a.simple().thread() == Some(thread)
                    && sender_matches(a)
                    && a.message.dialect_name() == Some(d.name.as_str())
            });
            let selected_acts: Vec<Act> = selected.iter().map(|(a, _)| a.clone()).collect();
            let valid = bindings_ok && admits_extension(&d, &thread_id, &[], &selected_acts);
            let state = if valid {
                render_json(&fold(clause, d.causal_protocol.as_ref(), &selected_acts))
            } else {
                String::new()
            };
            let state_root = hash(
                b"cbcl-state-proof/state-v1",
                &[id.as_slice(), state.as_bytes()],
            );
            rows.push(Row {
                checkpoint: Checkpoint {
                    accepted: accepted_root,
                    state: state_root,
                },
                state,
                valid,
            });
        }
        // Admission is checked against the *previous* accepted context as well:
        // independently reachable endpoints alone do not establish a transition.
        let mut transitions = Vec::new();
        for (old, _) in rows.iter().enumerate().filter(|(_, r)| r.valid) {
            let before: Vec<_> = acts
                .iter()
                .enumerate()
                .filter(|(i, _)| old & (1 << i) != 0)
                .map(|(_, (a, _))| a.clone())
                .collect();
            let remaining = (rows.len() - 1) ^ old;
            let mut addition = remaining;
            loop {
                let new = old | addition;
                if rows[new].valid {
                    let delta: Vec<_> = acts
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| addition & (1 << i) != 0)
                        .map(|(_, (a, _))| a.clone())
                        .collect();
                    if admits_extension(&d, &thread_id, &before, &delta) {
                        transitions.push((old, new));
                    }
                }
                if addition == 0 {
                    break;
                }
                addition = (addition - 1) & remaining;
            }
        }
        transitions.sort_unstable();
        Ok(Self {
            id,
            #[cfg(test)]
            id_parts,
            transitions,
            addresses: acts.into_iter().map(|(a, _)| a.address).collect(),
            rows,
        })
    }
    pub fn id(&self) -> [u8; 32] {
        self.id
    }
    /// Identity of this profile's parts under another domain. Test seam for
    /// the `SEMANTICS_VERSION` binding; `id()` uses `relation_domain(SEMANTICS_VERSION)`.
    #[cfg(test)]
    pub(crate) fn id_with_domain(&self, domain: &[u8]) -> [u8; 32] {
        let parts: Vec<&[u8]> = self.id_parts.iter().map(Vec::as_slice).collect();
        relation_id(domain, &parts)
    }
    pub fn addresses(&self) -> &[String] {
        &self.addresses
    }
    pub fn mask(&self, addresses: &[&str]) -> Result<u16> {
        let mut mask = 0;
        for a in addresses {
            let i = self
                .addresses
                .iter()
                .position(|x| x == a)
                .ok_or("unknown candidate")?;
            mask |= 1 << i;
        }
        Ok(mask)
    }
    /// The empty-set checkpoint. Mask 0 is valid for every compiled profile.
    pub fn genesis(&self) -> Checkpoint {
        self.rows[0].checkpoint
    }
    pub fn checkpoint(&self, mask: u16) -> Result<Checkpoint> {
        let row = self.rows.get(mask as usize).ok_or("mask outside profile")?;
        if !row.valid {
            return Err("set contains an unadmitted candidate".into());
        }
        Ok(row.checkpoint)
    }
    pub fn state_json(&self, mask: u16) -> Result<&str> {
        self.checkpoint(mask)?;
        Ok(&self.rows[mask as usize].state)
    }
    pub fn statement(&self, before: u16, after: u16) -> Result<Statement> {
        let before_root = self.checkpoint(before)?;
        let after_root = self.checkpoint(after)?;
        if before & !after != 0 {
            return Err("accepted set cannot shrink".into());
        }
        if !self
            .transitions
            .contains(&(before as usize, after as usize))
        {
            return Err("batch is not admitted against previous set".into());
        }
        Ok(Statement {
            profile: self.id,
            before: before_root,
            after: after_root,
            batch: self.rows[(after & !before) as usize].checkpoint.accepted,
        })
    }
}

fn admits_extension(d: &Dialect, thread: &ThreadId, before: &[Act], delta: &[Act]) -> bool {
    let mut accepted = before.to_vec();
    let mut pending: Vec<&Act> = delta.iter().collect();
    loop {
        let previous = pending.len();
        let mut next = Vec::new();
        for act in pending {
            match admit(d, thread, &accepted, act) {
                Admission::Accepted => accepted.push(act.clone()),
                Admission::Pending => next.push(act),
                Admission::Rejected(_) => return false,
            }
        }
        if next.is_empty() {
            return true;
        }
        if next.len() == previous {
            return false;
        }
        pending = next;
    }
}

// `:from` remains a keyword in the typed message; Message::sender() reads
// the distinct `:sender` routing field. Reject ambiguous or conflicting labels.
fn sender_matches(act: &Act) -> bool {
    let Message::Simple { params, .. } = act.simple() else {
        return false;
    };
    let from: Vec<_> = params
        .chunks_exact(2)
        .filter_map(|pair| {
            if matches!(&pair[0], SExpr::Atom(Atom::Keyword(k)) if k == "from") {
                Some(&pair[1])
            } else {
                None
            }
        })
        .collect();
    from.len() == 1
        && matches!(from[0], SExpr::Atom(Atom::Str(s) | Atom::Symbol(s)) if s == &act.signer)
        && act
            .simple()
            .sender()
            .is_none_or(|sender| sender == act.signer)
}
