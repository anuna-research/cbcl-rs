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
use alloc::borrow::Cow;
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;

// State wire addresses and native causal identities share digest bytes. Only
// the recognized state prefix is translated; no arbitrary identifier aliases.
fn native_reference(id: &str) -> Cow<'_, str> {
    if let Some(hex) = id.strip_prefix("sha256-") {
        Cow::Owned(alloc::format!("sha256:{hex}"))
    } else {
        Cow::Borrowed(id)
    }
}

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
    materialized: Option<&'a MaterializedPositions>,
}
impl<'a, S: MessageStore> Resolution<'a, S> {
    pub(crate) fn new(
        store: &'a S,
        protocol: &'a CausalProtocol,
        thread: &'a ThreadId,
        root: Option<&'a ContentHash>,
        hashes: impl IntoIterator<Item = String>,
    ) -> Self {
        let materialized = store
            .materialized_positions()
            .filter(|p| p.matches(protocol, thread, root));
        let mut messages = BTreeMap::new();
        let mut seen = BTreeSet::new();
        let mut todo: Vec<String> = hashes.into_iter().collect();
        while let Some(hash) = todo.pop() {
            if !seen.insert(hash.clone()) {
                continue;
            }
            if materialized
                .is_some_and(|p| p.entries.contains_key(native_reference(&hash).as_ref()))
            {
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

        if messages.is_empty() {
            return Self {
                store,
                protocol,
                thread,
                root,
                order: Vec::new(),
                rows: BTreeMap::new(),
                materialized,
            };
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
            materialized,
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
    fn kind(&self, hash: &str) -> Option<&str> {
        self.materialized
            .and_then(|p| p.entries.get(native_reference(hash).as_ref()))
            .map(|f| f.metadata.verb.as_str())
            .or_else(|| predecessor_type(self.store, &ContentHash(String::from(hash)), self.thread))
    }
    pub(crate) fn at(&self, hash: &str, step: &str) -> VerificationResult {
        if let Some(fact) = self
            .materialized
            .and_then(|p| p.entries.get(native_reference(hash).as_ref()))
        {
            let repeated =
                self.protocol.steps.keys().any(|s| {
                    s.contains(REPEAT_SEPARATOR) && repeat_base_name(s) == fact.metadata.verb
                });
            let ordinary = !step.contains(REPEAT_SEPARATOR)
                && !repeated
                && repeat_base_name(step) == fact.metadata.verb;
            return if ordinary || fact.steps.contains(step) {
                VerificationResult::Valid
            } else {
                self.wrong(hash, alloc::vec![String::from(step)])
            };
        }
        let key = ContentHash(String::from(hash));
        let Some(found) = self.kind(hash) else {
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
            found: String::from(self.kind(hash).unwrap_or("")),
        })
    }
    fn alternatives(&self, hash: &str, allowed: &[String]) -> VerificationResult {
        // Copy alternatives are existential: a wrong copy must not eclipse a
        // still-missing candidate. This is deliberately NOT eager lattice join.
        let mut missing = self.kind(hash).is_none();
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
            (Some(CausedBy::Single(h)), Some(root))
                if h == &root.0
                    || h.strip_prefix("sha256-")
                        .zip(root.0.strip_prefix("sha256:"))
                        .is_some_and(|(a, b)| a == b) =>
            {
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
                    let mut unknown = self.kind(h).is_none();
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
        // Fold acts use the state/wire address spelling, whereas native causal
        // headers historically use the simple-message hash. Retain that lookup
        // alias, but resolve pinned role roots using their actual state identity.
        // Never change the supplied act or its causal edges.
        store.append(
            ContentHash(crate::equivocation::message_content_hash(act.simple())),
            ThreadId(String::from(thread)),
            act.message.clone(),
        );
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
            .filter(|a| crate::state::is_role_root(a))
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

/// Immutable installation binding. The context digest binds the entire native
/// dialect/address/authentication schema; root and thread are explicit as well.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PositionContext {
    pub code: [u8; 32],
    pub root: ContentHash,
    pub thread: ThreadId,
}
/// Payload-free authenticated causal metadata. No sender-supplied rank exists.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PositionMetadata {
    pub id: String,
    pub verb: String,
    pub cause: Option<CausedBy>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct PositionFact {
    metadata: PositionMetadata,
    steps: BTreeSet<String>,
}
// Persistent treap: cloning a cut shares every unchanged native fact. Priorities
// are SHA-256 of immutable identity bytes, with identity as deterministic tie-break.
// Neither admission deltas nor borrowed resolver ports clone the covered prefix.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct PositionIndex {
    root: Option<Arc<PositionNode>>,
}
#[derive(Debug, PartialEq, Eq)]
struct PositionNode {
    fact: Arc<PositionFact>,
    priority: [u8; 32],
    size: usize,
    left: Option<Arc<PositionNode>>,
    right: Option<Arc<PositionNode>>,
}
impl PositionIndex {
    fn get(&self, id: &str) -> Option<&PositionFact> {
        let mut next = self.root.as_deref();
        while let Some(n) = next {
            match id.cmp(&n.fact.metadata.id) {
                core::cmp::Ordering::Equal => return Some(&n.fact),
                core::cmp::Ordering::Less => next = n.left.as_deref(),
                core::cmp::Ordering::Greater => next = n.right.as_deref(),
            }
        }
        None
    }
    fn contains_key(&self, id: &str) -> bool {
        self.get(id).is_some()
    }
    fn values(&self) -> alloc::vec::IntoIter<&PositionFact> {
        fn visit<'a>(n: Option<&'a PositionNode>, out: &mut Vec<&'a PositionFact>) {
            if let Some(n) = n {
                visit(n.left.as_deref(), out);
                out.push(&n.fact);
                visit(n.right.as_deref(), out);
            }
        }
        let mut out = Vec::new();
        visit(self.root.as_deref(), &mut out);
        out.into_iter()
    }
    fn insert(&mut self, fact: PositionFact) {
        use sha2::{Digest, Sha256};
        let priority: [u8; 32] = Sha256::digest(fact.metadata.id.as_bytes()).into();
        fn node(
            fact: Arc<PositionFact>,
            priority: [u8; 32],
            left: Option<Arc<PositionNode>>,
            right: Option<Arc<PositionNode>>,
        ) -> Arc<PositionNode> {
            let size =
                1 + left.as_ref().map_or(0, |n| n.size) + right.as_ref().map_or(0, |n| n.size);
            Arc::new(PositionNode {
                fact,
                priority,
                size,
                left,
                right,
            })
        }
        fn split(
            root: Option<&Arc<PositionNode>>,
            id: &str,
        ) -> (Option<Arc<PositionNode>>, Option<Arc<PositionNode>>) {
            let Some(n) = root else { return (None, None) };
            if n.fact.metadata.id.as_str() < id {
                let (l, r) = split(n.right.as_ref(), id);
                (Some(node(n.fact.clone(), n.priority, n.left.clone(), l)), r)
            } else {
                let (l, r) = split(n.left.as_ref(), id);
                (
                    l,
                    Some(node(n.fact.clone(), n.priority, r, n.right.clone())),
                )
            }
        }
        fn put(
            root: Option<&Arc<PositionNode>>,
            f: Arc<PositionFact>,
            p: [u8; 32],
        ) -> Arc<PositionNode> {
            let Some(n) = root else {
                return node(f, p, None, None);
            };
            if (p, f.metadata.id.as_str()) < (n.priority, n.fact.metadata.id.as_str()) {
                let (l, r) = split(Some(n), &f.metadata.id);
                return node(f, p, l, r);
            }
            if f.metadata.id < n.fact.metadata.id {
                node(
                    n.fact.clone(),
                    n.priority,
                    Some(put(n.left.as_ref(), f, p)),
                    n.right.clone(),
                )
            } else {
                node(
                    n.fact.clone(),
                    n.priority,
                    n.left.clone(),
                    Some(put(n.right.as_ref(), f, p)),
                )
            }
        }
        self.root = Some(put(self.root.as_ref(), Arc::new(fact), priority));
    }
}

/// Native-computed position cache. Facts have private fields and no deserialize
/// implementation. This is an accepted-evidence port, not authentication itself.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MaterializedPositions {
    context: PositionContext,
    protocol: Option<Arc<CausalProtocol>>,
    entries: PositionIndex,
    ranks: Arc<BTreeMap<String, BTreeMap<String, usize>>>,
    progress: BTreeMap<String, usize>,
}
impl MaterializedPositions {
    pub fn new(
        context: PositionContext,
        protocol: Option<&CausalProtocol>,
    ) -> Result<Self, String> {
        let mut ranks = BTreeMap::new();
        if let Some(p) = protocol {
            if !p.check_acyclicity().is_empty() || !p.check_reachability().is_empty() {
                return Err(String::from("invalid resume protocol"));
            }
            let verbs: BTreeSet<_> = p
                .steps
                .keys()
                .filter(|n| n.as_str() != BEGIN_KEYWORD)
                .map(|n| String::from(repeat_base_name(n)))
                .collect();
            for verb in verbs {
                // Incomparable positions have native progress zero, but may
                // still be used for native R5 resolution.
                if let Ok(chain) = position_chain(p, &verb) {
                    ranks.insert(
                        verb,
                        chain
                            .iter()
                            .enumerate()
                            .map(|(i, n)| (String::from(*n), i + 1))
                            .collect(),
                    );
                }
            }
        }
        Ok(Self {
            context,
            protocol: protocol.map(|p| Arc::new(p.clone())),
            entries: PositionIndex::default(),
            ranks: Arc::new(ranks),
            progress: BTreeMap::new(),
        })
    }
    pub fn context(&self) -> &PositionContext {
        &self.context
    }
    pub fn protocol(&self) -> Option<&CausalProtocol> {
        self.protocol.as_deref()
    }
    pub fn metadata(&self) -> impl DoubleEndedIterator<Item = &PositionMetadata> {
        self.entries.values().map(|f| &f.metadata)
    }
    pub fn len(&self) -> usize {
        self.entries.root.as_ref().map_or(0, |n| n.size)
    }
    pub fn is_empty(&self) -> bool {
        self.entries.root.is_none()
    }
    pub fn contains(&self, id: &str) -> bool {
        self.entries.contains_key(native_reference(id).as_ref())
    }
    pub fn progress(&self, verb: &str) -> usize {
        self.progress.get(verb).copied().unwrap_or(0)
    }
    fn matches(
        &self,
        protocol: &CausalProtocol,
        thread: &ThreadId,
        root: Option<&ContentHash>,
    ) -> bool {
        self.protocol.as_deref() == Some(protocol)
            && &self.context.thread == thread
            && root.map_or(true, |r| r == &self.context.root)
    }
    /// Called after native signature/context/admission checks. Requires exact
    /// native identity and thread, and computes positions with the native R5
    /// evaluator. No full message is retained.
    pub fn apply_accepted(&mut self, message: &crate::message::Message) -> Result<(), String> {
        let simple = message.innermost_simple().ok_or("resume simple")?;
        if simple.thread() != Some(self.context.thread.0.as_str()) {
            return Err(String::from("resume thread"));
        }
        let data = PositionMetadata {
            id: crate::equivocation::message_content_hash(simple),
            verb: String::from(simple.performative().ok_or("resume verb")?.name()),
            cause: simple.caused_by().cloned(),
        };
        self.apply_metadata(data)
    }
    /// Restore *externally authenticated accepted* metadata, never arbitrary
    /// claimed positions. Hosts must verify snapshot truth/scope before calling;
    /// checkpoint's safe wrapper performs that verification. Native relation is
    /// recomputed here, so even an attested rank cannot override R5.
    pub fn restore_attested(
        context: PositionContext,
        protocol: Option<&CausalProtocol>,
        records: Vec<PositionMetadata>,
    ) -> Result<Self, String> {
        let mut out = Self::new(context, protocol)?;
        let mut todo: BTreeMap<String, PositionMetadata> = BTreeMap::new();
        let mut waiting: BTreeMap<String, Vec<String>> = BTreeMap::new();
        let mut remaining = BTreeMap::new();
        let mut ready = Vec::new();
        for r in records {
            if todo.insert(r.id.clone(), r).is_some() {
                return Err(String::from("duplicate resume identity"));
            }
        }
        for (id, r) in &todo {
            let parents = match &r.cause {
                Some(CausedBy::Single(h)) => alloc::vec![h.clone()],
                Some(CausedBy::Multiple(hs)) => hs.clone(),
                _ => Vec::new(),
            };
            for parent in &parents {
                if !todo.contains_key(native_reference(parent).as_ref()) {
                    return Err(String::from("missing resume ancestor"));
                }
                waiting
                    .entry(native_reference(parent).into_owned())
                    .or_default()
                    .push(id.clone());
            }
            remaining.insert(id.clone(), parents.len());
            if parents.is_empty() {
                ready.push(id.clone());
            }
        }
        while let Some(id) = ready.pop() {
            let r = todo.remove(&id).ok_or("resume cycle")?;
            out.apply_metadata(r)?;
            for child in waiting.remove(&id).unwrap_or_default() {
                let count = remaining.get_mut(&child).ok_or("resume child")?;
                *count -= 1;
                if *count == 0 {
                    ready.push(child);
                }
            }
        }
        if !todo.is_empty() {
            return Err(String::from("cyclic resume ancestry"));
        }
        Ok(out)
    }
    fn apply_metadata(&mut self, data: PositionMetadata) -> Result<(), String> {
        if let Some(old) = self.entries.get(&data.id) {
            return if old.metadata == data {
                Ok(())
            } else {
                Err(String::from("conflicting resume identity"))
            };
        }
        let parents: &[String] = match &data.cause {
            Some(CausedBy::Single(h)) => core::slice::from_ref(h),
            Some(CausedBy::Multiple(hs)) => hs,
            _ => &[],
        };
        if parents
            .iter()
            .any(|h| !self.entries.contains_key(native_reference(h).as_ref()))
        {
            return Err(String::from("missing resume ancestor"));
        }
        let root = data.id == self.context.root.0;
        if root {
            if !matches!(data.cause, Some(CausedBy::Begin)) {
                return Err(String::from("resume root cause"));
            }
        } else if self.protocol.is_some()
            && (parents.is_empty() || !self.entries.contains_key(&self.context.root.0))
        {
            return Err(String::from("resume root required"));
        }
        let mut steps = BTreeSet::new();
        if let Some(p) = &self.protocol {
            struct Port<'a>(&'a MaterializedPositions);
            impl MessageStore for Port<'_> {
                fn materialized_positions(&self) -> Option<&MaterializedPositions> {
                    Some(self.0)
                }
                fn lookup(&self, _: &ContentHash) -> Option<&crate::message::Message> {
                    None
                }
                fn lookup_in_thread(
                    &self,
                    _: &ContentHash,
                    _: &ThreadId,
                ) -> Option<&crate::message::Message> {
                    None
                }
                fn contains(&self, h: &ContentHash, t: &ThreadId) -> bool {
                    t == &self.0.context.thread && self.0.contains(&h.0)
                }
                fn append(
                    &mut self,
                    _: ContentHash,
                    _: ThreadId,
                    _: crate::message::Message,
                ) -> bool {
                    false
                }
                fn frontier(&self, _: &ThreadId) -> Vec<&ContentHash> {
                    Vec::new()
                }
                fn causal_closure(&self, _: &ContentHash, _: &ThreadId) -> Vec<ContentHash> {
                    Vec::new()
                }
            }
            // Empty closure: all accepted parents are already materialized.
            let port = Port(self);
            let resolution = Resolution {
                store: &port,
                protocol: p,
                thread: &self.context.thread,
                root: Some(&self.context.root),
                order: Vec::new(),
                rows: BTreeMap::new(),
                materialized: Some(self),
            };
            let mut declared = false;
            for (name, step) in &p.steps {
                if name == BEGIN_KEYWORD || repeat_base_name(name) != data.verb {
                    continue;
                }
                declared = true;
                if resolution.step(step, data.cause.as_ref()) == VerificationResult::Valid {
                    steps.insert(name.clone());
                }
            }
            if declared && !root && steps.is_empty() {
                return Err(String::from("invalid resume position"));
            }
        }
        if let Some(ranks) = self.ranks.get(&data.verb) {
            let rank = steps
                .iter()
                .filter_map(|s| ranks.get(s))
                .copied()
                .max()
                .unwrap_or(0);
            self.progress
                .entry(data.verb.clone())
                .and_modify(|v| *v = (*v).max(rank))
                .or_insert(rank);
        }
        self.entries.insert(PositionFact {
            metadata: data,
            steps,
        });
        Ok(())
    }
}

#[cfg(test)]
mod materialized_tests {
    use super::*;
    use crate::message::{Message, Performative, WrapperType};
    use crate::sexpr::SExpr;
    use alloc::{boxed::Box, format, vec};
    use core::cell::Cell;
    fn protocol(depth: usize) -> CausalProtocol {
        let mut steps = BTreeMap::new();
        for (name, parent, next) in [
            (String::from("begin"), None, Some(String::from("open"))),
            ("open".into(), Some("begin".into()), Some("tick#1".into())),
        ] {
            steps.insert(
                name.clone(),
                StepDecl {
                    performative: name,
                    predecessors: parent.into_iter().map(NodeRef::Single).collect(),
                    successors: next.into_iter().map(NodeRef::Single).collect(),
                },
            );
        }
        for i in 1..=depth {
            let name = format!("tick#{i}");
            steps.insert(
                name.clone(),
                StepDecl {
                    performative: name,
                    predecessors: vec![NodeRef::Single(if i == 1 {
                        "open".into()
                    } else {
                        format!("tick#{}", i - 1)
                    })],
                    successors: if i == depth {
                        vec![]
                    } else {
                        vec![NodeRef::Single(format!("tick#{}", i + 1))]
                    },
                },
            );
        }
        CausalProtocol { steps }
    }
    fn message(v: &str, cause: CausedBy, nonce: usize) -> Message {
        let simple = Message::Simple {
            performative: Performative::Custom(v.into()),
            recipient: None,
            content: format!("\"{nonce}\"").parse::<SExpr>().unwrap(),
            params: vec![],
            sender: Some("@a".into()),
            thread: Some("resume".into()),
            caused_by: Some(cause),
        };
        if v == "hello" {
            Message::Wrapped {
                wrapper: WrapperType::WithRoles,
                params: vec![],
                content: Box::new(simple),
            }
        } else {
            simple
        }
    }
    fn id(m: &Message) -> String {
        crate::equivocation::message_content_hash(m.innermost_simple().unwrap())
    }
    struct Port<'a>(&'a MaterializedPositions, Cell<usize>);
    impl MessageStore for Port<'_> {
        fn materialized_positions(&self) -> Option<&MaterializedPositions> {
            Some(self.0)
        }
        fn lookup(&self, _: &ContentHash) -> Option<&Message> {
            self.1.set(self.1.get() + 1);
            None
        }
        fn lookup_in_thread(&self, _: &ContentHash, _: &ThreadId) -> Option<&Message> {
            self.1.set(self.1.get() + 1);
            None
        }
        fn contains(&self, _: &ContentHash, _: &ThreadId) -> bool {
            false
        }
        fn append(&mut self, _: ContentHash, _: ThreadId, _: Message) -> bool {
            false
        }
        fn frontier(&self, _: &ThreadId) -> Vec<&ContentHash> {
            vec![]
        }
        fn causal_closure(&self, _: &ContentHash, _: &ThreadId) -> Vec<ContentHash> {
            panic!("ancestor replay")
        }
    }
    #[test]
    fn native_progress_oracle_and_compact_tail() {
        let p = protocol(8);
        let root = message("hello", CausedBy::Begin, 0);
        let rootid = id(&root);
        let mut cache = MaterializedPositions::new(
            PositionContext {
                code: [1; 32],
                root: ContentHash(rootid.clone()),
                thread: ThreadId("resume".into()),
            },
            Some(&p),
        )
        .unwrap();
        cache.apply_accepted(&root).unwrap();
        let open = message("open", CausedBy::Single(rootid.clone()), 1);
        cache.apply_accepted(&open).unwrap();
        let mut acts = vec![
            crate::state::Act::from_message(root, "@a").unwrap(),
            crate::state::Act::from_message(open.clone(), "@a").unwrap(),
        ];
        let mut previous = id(&open);
        for i in 1..=8 {
            let m = message("tick", CausedBy::Single(previous), i + 1);
            previous = id(&m);
            cache.apply_accepted(&m).unwrap();
            acts.push(crate::state::Act::from_message(m, "@a").unwrap());
            assert_eq!(cache.progress("tick"), i);
            assert_eq!(
                accepted_positions(&p, "tick", &acts.iter().collect::<Vec<_>>())
                    .into_iter()
                    .max()
                    .unwrap_or(0),
                i
            );
            if i < 8 {
                let port = Port(&cache, Cell::new(0));
                assert_eq!(
                    verify(
                        "tick",
                        Some(&CausedBy::Single(previous.clone())),
                        &port,
                        &p,
                        &ThreadId("resume".into()),
                        Some(&ContentHash(rootid.clone()))
                    ),
                    VerificationResult::Valid
                );
                assert_eq!(port.1.get(), 0);
            }
        }
    }
    #[test]
    fn future_tail_after_5000_metadata_facts_no_body_reads() {
        let p = protocol(32);
        let root = message("hello", CausedBy::Begin, 0);
        let rid = id(&root);
        let mut c = MaterializedPositions::new(
            PositionContext {
                code: [2; 32],
                root: ContentHash(rid.clone()),
                thread: ThreadId("resume".into()),
            },
            Some(&p),
        )
        .unwrap();
        c.apply_accepted(&root).unwrap();
        let open = message("open", CausedBy::Single(rid.clone()), 1);
        let oid = id(&open);
        c.apply_accepted(&open).unwrap();
        let mut previous = oid.clone();
        for i in 0..5000 {
            if i % 32 == 0 {
                previous = oid.clone();
            }
            let m = message("tick", CausedBy::Single(previous), i + 2);
            previous = id(&m);
            c.apply_accepted(&m).unwrap();
        }
        let frozen = c.clone();
        assert!(Arc::ptr_eq(
            c.entries.root.as_ref().unwrap(),
            frozen.entries.root.as_ref().unwrap()
        ));
        assert!(Arc::ptr_eq(
            c.protocol.as_ref().unwrap(),
            frozen.protocol.as_ref().unwrap()
        ));
        assert!(Arc::ptr_eq(&c.ranks, &frozen.ranks));
        assert_eq!(c.len(), 5002);
        let restored = MaterializedPositions::restore_attested(
            c.context.clone(),
            Some(&p),
            c.metadata().cloned().rev().collect(),
        )
        .unwrap();
        assert_eq!(c, restored);
        assert_eq!(c.progress("tick"), 32);
        let port = Port(&restored, Cell::new(0));
        assert_eq!(
            verify(
                "tick",
                Some(&CausedBy::Single(previous)),
                &port,
                &p,
                &ThreadId("resume".into()),
                Some(&ContentHash(rid))
            ),
            VerificationResult::Valid
        );
        assert_eq!(port.1.get(), 0);
    }
    #[test]
    fn out_of_order_and_foreign_context_do_not_install_facts() {
        let p = protocol(3);
        let root = message("hello", CausedBy::Begin, 0);
        let rid = id(&root);
        let mut c = MaterializedPositions::new(
            PositionContext {
                code: [3; 32],
                root: ContentHash(rid.clone()),
                thread: ThreadId("resume".into()),
            },
            Some(&p),
        )
        .unwrap();
        let m = message("open", CausedBy::Single(rid.clone()), 1);
        assert!(c.apply_accepted(&m).is_err());
        assert_eq!(c.metadata().count(), 0);
        c.apply_accepted(&root).unwrap();
        c.apply_accepted(&m).unwrap();
        let frozen = c.clone();
        let missing = message("tick", CausedBy::Single("missing".into()), 2);
        assert!(c.apply_accepted(&missing).is_err());
        assert_eq!(c, frozen);
        let port = Port(&c, Cell::new(0));
        assert!(!matches!(
            verify(
                "tick",
                Some(&CausedBy::Single(id(&m))),
                &port,
                &p,
                &ThreadId("foreign".into()),
                Some(&ContentHash(rid.clone()))
            ),
            VerificationResult::Valid
        ));
        assert!(!matches!(
            verify(
                "tick",
                Some(&CausedBy::Single(id(&m))),
                &port,
                &p,
                &ThreadId("resume".into()),
                Some(&ContentHash("foreign".into()))
            ),
            VerificationResult::Valid
        ));
        assert!(MaterializedPositions::restore_attested(
            c.context.clone(),
            Some(&p),
            vec![PositionMetadata {
                id: "a".into(),
                verb: "tick".into(),
                cause: Some(CausedBy::Single("a".into()))
            }]
        )
        .is_err());
        let mut no = MaterializedPositions::new(c.context.clone(), None).unwrap();
        no.apply_accepted(&root).unwrap();
        no.apply_accepted(&m).unwrap();
        assert_eq!(no.progress("open"), 0);
    }
    /// Regression evidence: old accepted_positions indexed only state aliases,
    /// so native causal headers incorrectly rendered progress zero. Both valid
    /// digest spellings must resolve to the same accepted native position.
    #[test]
    fn native_progress_indexes_native_causal_ids_and_state_aliases() {
        let p = protocol(3);
        for state_alias in [false, true] {
            let root = message("hello", CausedBy::Begin, 0);
            let reference = |m: &Message| {
                if state_alias {
                    crate::state::wire_address(m.innermost_simple().unwrap())
                } else {
                    id(m)
                }
            };
            let open = message("open", CausedBy::Single(reference(&root)), 1);
            let mut cache = MaterializedPositions::new(
                PositionContext {
                    code: [9; 32],
                    root: ContentHash(id(&root)),
                    thread: ThreadId("resume".into()),
                },
                Some(&p),
            )
            .unwrap();
            cache.apply_accepted(&root).unwrap();
            cache.apply_accepted(&open).unwrap();
            let mut history = vec![
                crate::state::Act::from_message(root, "@a").unwrap(),
                crate::state::Act::from_message(open.clone(), "@a").unwrap(),
            ];
            let mut previous = open;
            for i in 1..=3 {
                let m = message("tick", CausedBy::Single(reference(&previous)), i + 1);
                cache.apply_accepted(&m).unwrap();
                history.push(crate::state::Act::from_message(m.clone(), "@a").unwrap());
                assert_eq!(
                    accepted_positions(&p, "tick", &history.iter().collect::<Vec<_>>())
                        .into_iter()
                        .max()
                        .unwrap_or(0),
                    i
                );
                assert_eq!(cache.progress("tick"), i);
                previous = m;
            }
        }
    }
}
