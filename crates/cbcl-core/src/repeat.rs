//! Runtime interpretation of install-time repeat copies (SPEC-015 REQ-704).
//!
//! Wire verbs stay unindexed. A copy is established by its causal ancestry,
//! not by arrival order, a mutable counter, or a sender-supplied index. Dynamic
//! programming over the finite expanded DAG avoids recursive store traversal;
//! missing ancestry stays Unknown. No state fold is read by this module.
#![forbid(unsafe_code)]
use crate::message::CausedBy;
use crate::protocol::{
    allowed_single_predecessors, predecessor_type, repeat_base_name, CausalProtocol,
    CausalViolation, NodeRef, StepDecl, VerificationResult, BEGIN_KEYWORD, REPEAT_SEPARATOR,
};
use crate::store::{ContentHash, MessageStore, ThreadId};
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::String;
use alloc::vec::Vec;

pub(crate) fn has_repeat(protocol: &CausalProtocol) -> bool {
    protocol.steps.keys().any(|s| s.contains(REPEAT_SEPARATOR))
}

// Safety-level position resolution needs only authenticated causal metadata.
// Full payloads are still required by the separate occupant-completion check.
fn metadata<S: MessageStore>(
    store: &S,
    hash: &ContentHash,
    thread: &ThreadId,
) -> Option<(String, Option<CausedBy>)> {
    if let Some(message) = store.lookup_in_thread(hash, thread) {
        let simple = message.innermost_simple()?;
        return Some((
            String::from(simple.performative()?.name()),
            simple.caused_by().cloned(),
        ));
    }
    if let Some(envelope) = store.envelope_in_thread(hash, thread) {
        return Some((
            envelope.header.performative.clone(),
            envelope.header.caused_by.clone(),
        ));
    }
    let opened = store.opened_in_thread(hash, thread)?;
    Some((
        String::from(opened.performative()?),
        opened.causal_reference()?,
    ))
}

/// A finite evidence table, scoped to a thread and to the referenced closure.
/// Entries say whether a particular message inhabits a particular expanded step.
/// The topological step order makes every lookup depend only on earlier rows.
pub(crate) struct Resolution<'a, S> {
    store: &'a S,
    protocol: &'a CausalProtocol,
    thread: &'a ThreadId,
    root: Option<&'a ContentHash>,
    pub(crate) order: Vec<&'a str>,
    rows: BTreeMap<(String, String), VerificationResult>,
}
impl<'a, S: MessageStore> Resolution<'a, S> {
    pub(crate) fn new(
        store: &'a S,
        protocol: &'a CausalProtocol,
        thread: &'a ThreadId,
        root: Option<&'a ContentHash>,
        hashes: impl IntoIterator<Item = String>,
    ) -> Self {
        let mut messages = BTreeMap::new();
        let mut seen = BTreeSet::new();
        let mut todo: Vec<String> = hashes.into_iter().collect();
        while let Some(hash) = todo.pop() {
            if !seen.insert(hash.clone()) {
                continue;
            }
            if let Some((verb, cause)) = metadata(store, &ContentHash(hash.clone()), thread) {
                match &cause {
                    Some(CausedBy::Single(h)) => todo.push(h.clone()),
                    Some(CausedBy::Multiple(hs)) => todo.extend(hs.iter().cloned()),
                    _ => {}
                }
                messages.insert(hash, (verb, cause));
            }
        }

        let mut order = Vec::new();
        let mut done = BTreeSet::new();
        // Installed protocols are acyclic. A malformed programmatic protocol
        // leaves cyclic rows absent, which fails closed rather than looping.
        loop {
            let ready: Vec<&str> = protocol
                .steps
                .iter()
                .filter(|(name, step)| {
                    !done.contains(name.as_str())
                        && step
                            .predecessors
                            .iter()
                            .all(|nr| nr.performatives().all(|p| done.contains(p)))
                })
                .map(|(name, _)| name.as_str())
                .collect();
            if ready.is_empty() {
                break;
            }
            for name in ready {
                done.insert(name);
                order.push(name);
            }
        }
        let mut result = Self {
            store,
            protocol,
            thread,
            root,
            order,
            rows: BTreeMap::new(),
        };
        for name in result.order.clone() {
            if name == BEGIN_KEYWORD {
                continue;
            }
            for (hash, (verb, cause)) in &messages {
                if verb != repeat_base_name(name) {
                    continue;
                }
                let value = result.step(&protocol.steps[name], cause.as_ref());
                result
                    .rows
                    .insert((hash.clone(), String::from(name)), value);
            }
        }

        result
    }
    pub(crate) fn at(&self, hash: &str, step: &str) -> VerificationResult {
        let key = ContentHash(String::from(hash));
        let Some(found) = predecessor_type(self.store, &key, self.thread) else {
            return VerificationResult::Unknown;
        };
        if found != repeat_base_name(step) {
            return self.wrong(hash, alloc::vec![String::from(step)]);
        }
        // Ordinary types retain their pre-repeat interpretation. Only indexed
        // types (and plain copies of a repeated base) need ancestry evidence.
        let repeated = self
            .protocol
            .steps
            .keys()
            .any(|s| s.contains(REPEAT_SEPARATOR) && repeat_base_name(s) == found);
        if !step.contains(REPEAT_SEPARATOR) && !repeated {
            return VerificationResult::Valid;
        }
        if metadata(self.store, &key, self.thread).is_none() {
            // A sealed causal opening cannot establish a repeat position.
            return VerificationResult::Unknown;
        }
        self.rows
            .get(&(String::from(hash), String::from(step)))
            .cloned()
            .unwrap_or_else(|| self.wrong(hash, alloc::vec![String::from(step)]))
    }
    fn wrong(&self, hash: &str, expected: Vec<String>) -> VerificationResult {
        VerificationResult::Violation(CausalViolation::InvalidPredecessor {
            caused_by: String::from(hash),
            expected,
            found: String::from(
                predecessor_type(self.store, &ContentHash(String::from(hash)), self.thread)
                    .unwrap_or(""),
            ),
        })
    }
    fn alternatives(&self, hash: &str, allowed: &[String]) -> VerificationResult {
        // Copy alternatives are existential: a wrong copy must not eclipse a
        // still-missing candidate. This is deliberately NOT eager lattice join.
        let mut missing =
            predecessor_type(self.store, &ContentHash(String::from(hash)), self.thread).is_none();
        for name in allowed {
            match self.at(hash, name) {
                VerificationResult::Valid => return VerificationResult::Valid,
                VerificationResult::Unknown => missing = true,
                VerificationResult::Violation(_) => {}
            }
        }
        if missing {
            VerificationResult::Unknown
        } else {
            self.wrong(hash, allowed.to_vec())
        }
    }
    pub(crate) fn step(&self, step: &StepDecl, caused_by: Option<&CausedBy>) -> VerificationResult {
        let rewritten;
        let caused_by = match (caused_by, self.root) {
            (Some(CausedBy::Single(h)), Some(root)) if h == &root.0 => {
                rewritten = CausedBy::Begin;
                Some(&rewritten)
            }
            _ => caused_by,
        };
        match caused_by {
            None if step.predecessors.is_empty() => VerificationResult::Valid,
            None => VerificationResult::Violation(CausalViolation::MissingCausedBy),
            Some(CausedBy::Begin) => {
                let allowed = allowed_single_predecessors(step);
                if allowed.iter().any(|n| n == BEGIN_KEYWORD) {
                    VerificationResult::Valid
                } else {
                    self.wrong(BEGIN_KEYWORD, allowed)
                }
            }
            Some(CausedBy::Single(h)) => self.alternatives(h, &allowed_single_predecessors(step)),
            Some(CausedBy::Multiple(hashes)) => {
                let Some(all) = step.predecessors.iter().find_map(|nr| {
                    if let NodeRef::All(s) = nr {
                        Some(s)
                    } else {
                        None
                    }
                }) else {
                    return VerificationResult::Violation(CausalViolation::FanInWithoutAllDecl {
                        performative: step.performative.clone(),
                    });
                };
                let mut found = BTreeSet::new();
                let mut possible = BTreeSet::new();
                let mut missing = false;
                for h in hashes {
                    let mut matched = false;
                    let mut unknown =
                        predecessor_type(self.store, &ContentHash(h.clone()), self.thread)
                            .is_none();
                    for name in all {
                        match self.at(h, name) {
                            VerificationResult::Valid => {
                                found.insert(name.clone());
                                matched = true;
                            }
                            VerificationResult::Unknown => {
                                possible.insert(name.clone());
                                unknown = true;
                            }
                            VerificationResult::Violation(_) => {}
                        }
                    }
                    if !matched && !unknown {
                        return self.wrong(h, all.iter().cloned().collect());
                    }
                    missing |= !matched && unknown;
                }
                let absent: Vec<String> = all.difference(&found).cloned().collect();
                if missing || absent.iter().any(|n| possible.contains(n)) {
                    VerificationResult::Unknown
                } else if absent.is_empty() {
                    VerificationResult::Valid
                } else {
                    VerificationResult::Violation(CausalViolation::IncompleteFanIn {
                        missing_types: absent,
                    })
                }
            }
        }
    }
    pub(crate) fn verify(&self, verb: &str, cause: Option<&CausedBy>) -> VerificationResult {
        let mut unknown = false;
        let mut error = VerificationResult::Violation(CausalViolation::MissingCausedBy);
        for (name, step) in &self.protocol.steps {
            if name == BEGIN_KEYWORD || repeat_base_name(name) != verb {
                continue;
            }
            match self.step(step, cause) {
                VerificationResult::Valid => return VerificationResult::Valid,
                VerificationResult::Unknown => unknown = true,
                invalid => error = invalid,
            }
        }
        if unknown {
            VerificationResult::Unknown
        } else {
            error
        }
    }
}

pub(crate) fn verify<S: MessageStore>(
    verb: &str,
    cause: Option<&CausedBy>,
    store: &S,
    protocol: &CausalProtocol,
    thread: &ThreadId,
    root: Option<&ContentHash>,
) -> VerificationResult {
    // Preserve the legacy route only for genuinely non-protocol verbs. A
    // repeated base IS a protocol verb, even when it has no unindexed key.
    if !protocol
        .steps
        .keys()
        .any(|name| repeat_base_name(name) == verb)
    {
        return VerificationResult::Valid;
    }
    let hashes = match cause {
        Some(CausedBy::Single(h)) => alloc::vec![h.clone()],
        Some(CausedBy::Multiple(hs)) => hs.clone(),
        _ => Vec::new(),
    };
    Resolution::new(store, protocol, thread, root, hashes).verify(verb, cause)
}

/// Ordered occurrences of a verb in the finite protocol. Every consecutive
/// pair must be causally comparable; an arbitrary topological tie-break is
/// never allowed to invent progress between independent branches.
pub(crate) fn position_chain<'a>(
    protocol: &'a CausalProtocol,
    verb: &str,
) -> Result<Vec<&'a str>, String> {
    let mut ancestors: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
    let mut positions = Vec::new();
    loop {
        let ready: Vec<&str> = protocol
            .steps
            .iter()
            .filter(|(name, step)| {
                !ancestors.contains_key(name.as_str())
                    && step
                        .predecessors
                        .iter()
                        .all(|nr| nr.performatives().all(|p| ancestors.contains_key(p)))
            })
            .map(|(name, _)| name.as_str())
            .collect();
        if ready.is_empty() {
            break;
        }
        for name in ready {
            let mut inherited = BTreeSet::new();
            for parent in protocol.steps[name]
                .predecessors
                .iter()
                .flat_map(NodeRef::performatives)
            {
                inherited.insert(parent);
                inherited.extend(ancestors[parent].iter().copied());
            }
            if name != BEGIN_KEYWORD && repeat_base_name(name) == verb {
                if positions
                    .last()
                    .is_some_and(|previous| !inherited.contains(previous))
                {
                    return Err(alloc::format!(
                        "progress '{verb}' has incomparable protocol positions"
                    ));
                }
                positions.push(name);
            }
            ancestors.insert(name, inherited);
        }
    }
    if ancestors.len() != protocol.steps.len() || positions.is_empty() {
        return Err(alloc::format!(
            "progress '{verb}' requires positions in an acyclic protocol"
        ));
    }
    Ok(positions)
}

/// Select established protocol ranks from accepted evidence. Data-domain filters
/// do not change causal progress. The fold owns the max reduction, including 0.
pub(crate) fn accepted_positions(
    protocol: &CausalProtocol,
    verb: &str,
    acts: &[&crate::state::Act],
) -> Vec<usize> {
    let Ok(chain) = position_chain(protocol, verb) else {
        return Vec::new();
    };
    let mut store = crate::store::ThreadedMessageStore::new();
    let mut threads: BTreeMap<String, Vec<&crate::state::Act>> = BTreeMap::new();
    for act in acts {
        let Some(thread) = act.simple().thread() else {
            continue;
        };
        store.append(
            ContentHash(act.address.clone()),
            ThreadId(String::from(thread)),
            act.message.clone(),
        );
        threads.entry(String::from(thread)).or_default().push(act);
    }
    let mut positions = Vec::new();
    for (thread, members) in threads {
        let thread = ThreadId(thread);
        let root = members
            .iter()
            .filter(|a| {
                a.message.wrapper_type() == Some(crate::message::WrapperType::WithRoles)
                    && a.predecessors.is_empty()
            })
            .min_by(|a, b| a.address.cmp(&b.address))
            .map(|a| ContentHash(a.address.clone()));
        let resolution = Resolution::new(
            &store,
            protocol,
            &thread,
            root.as_ref(),
            members.iter().map(|a| a.address.clone()),
        );
        for act in members.iter().filter(|a| a.verb == verb) {
            for (index, name) in chain.iter().enumerate() {
                if matches!(
                    resolution
                        .rows
                        .get(&(act.address.clone(), String::from(*name))),
                    Some(VerificationResult::Valid)
                ) {
                    positions.push(index + 1);
                }
            }
        }
    }
    positions
}
