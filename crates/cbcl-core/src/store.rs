//! Message store with G-Set CRDT semantics (REQ-300, REQ-309, ADR-008).
//!
//! Provides [`HashIndex`] for O(1) lookup and [`ThreadedMessageStore`] for
//! append-only, deduplicated, per-thread message storage.
//!
//! The store is a join-semilattice (REQ-300): messages are the elements,
//! `:caused-by` links form the covers relation (REQ-301), fan-in is join,
//! and causal closure computes the principal ideal.
//!
//! Also provides [`CausalClosureBundle`] for transferring verifiable subsets
//! of the message store (REQ-311, REQ-212).

#![forbid(unsafe_code)]

use crate::attest::AttestError;
use crate::envelope::{verify_opened, OpenedEnvelope, OpenedError, RedactedEnvelope};
use crate::message::{CausedBy, Message};
use crate::typed_addr::FieldId;
use crate::protocol::{CausalProtocol, CausalViolation, VerificationResult};
use crate::r4::Signer;
use crate::sexpr::{Atom, SExpr};
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;
use hashbrown::{HashMap, HashSet};

/// Content-addressed hash identifying a message (SHA-256 hex string).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ContentHash(pub String);

/// Thread identifier scoping causal chains (ADR-008).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ThreadId(pub String);

/// Thread-scoped hash index for O(1) message lookup (REQ-309).
///
/// Each entry maps a [`ContentHash`] to its owning [`ThreadId`] and position
/// index within that thread. Lookups enforce thread isolation per ADR-008:
/// a lookup for hash H in thread T returns `None` if H belongs to thread T'.
///
/// Memory budget: <= 64 bytes per entry (NFR-303).
#[derive(Debug, Clone)]
pub struct HashIndex {
    map: HashMap<ContentHash, (ThreadId, usize)>,
}

impl HashIndex {
    /// Creates an empty hash index.
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
        }
    }

    /// Creates an empty hash index with pre-allocated capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            map: HashMap::with_capacity(capacity),
        }
    }

    /// Inserts a content hash mapped to a thread and position index.
    ///
    /// Returns `true` if the entry was newly inserted, `false` if the hash
    /// already existed (duplicate — entry is not overwritten).
    pub fn insert(&mut self, hash: ContentHash, thread: ThreadId, index: usize) -> bool {
        use hashbrown::hash_map::Entry;
        match self.map.entry(hash) {
            Entry::Vacant(e) => {
                e.insert((thread, index));
                true
            }
            Entry::Occupied(_) => false,
        }
    }

    /// Looks up a content hash, enforcing thread isolation (ADR-008).
    ///
    /// Returns `Some(index)` only if the hash exists AND belongs to the given thread.
    /// Returns `None` if the hash is absent or belongs to a different thread.
    pub fn lookup(&self, hash: &ContentHash, thread: &ThreadId) -> Option<usize> {
        self.map
            .get(hash)
            .and_then(|(t, idx)| if t == thread { Some(*idx) } else { None })
    }

    /// Checks whether a content hash exists in the given thread (ADR-008).
    ///
    /// Returns `true` only if the hash exists AND belongs to the given thread.
    pub fn contains(&self, hash: &ContentHash, thread: &ThreadId) -> bool {
        self.lookup(hash, thread).is_some()
    }

    /// Rebuilds the index from an iterator of `(ContentHash, ThreadId, usize)` triples.
    ///
    /// Clears the existing index and repopulates from the iterator.
    /// Duplicates in the iterator are silently skipped (first wins).
    pub fn rebuild<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = (ContentHash, ThreadId, usize)>,
    {
        self.map.clear();
        for (hash, thread, index) in iter {
            self.insert(hash, thread, index);
        }
    }

    /// Returns the number of entries in the index.
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns `true` if the index contains no entries.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
}

impl Default for HashIndex {
    fn default() -> Self {
        Self::new()
    }
}

/// Trait for an append-only message store with G-Set CRDT semantics (REQ-300).
pub trait MessageStore {
    /// Look up a message by content hash across all threads.
    fn lookup(&self, hash: &ContentHash) -> Option<&Message>;

    /// Look up a message by content hash within a specific thread (ADR-008).
    fn lookup_in_thread(&self, hash: &ContentHash, thread: &ThreadId) -> Option<&Message>;

    /// Check whether a content hash exists in the given thread.
    fn contains(&self, hash: &ContentHash, thread: &ThreadId) -> bool;

    /// Append a message to a thread. Returns `false` if the hash already exists
    /// (deduplication per REQ-310). Returns `true` if newly inserted.
    fn append(&mut self, hash: ContentHash, thread: ThreadId, message: Message) -> bool;

    /// Returns the frontier (leaf messages) of a thread — messages not referenced
    /// by any other message's `:caused-by` in the same thread.
    fn frontier(&self, thread: &ThreadId) -> Vec<&ContentHash>;

    /// Returns the causal closure (principal ideal) of a message — all messages
    /// reachable by transitively following `:caused-by` links back to root(s).
    fn causal_closure(&self, hash: &ContentHash, thread: &ThreadId) -> Vec<ContentHash>;

    /// Look up a redacted envelope by the content hash of the message it
    /// redacts, scoped to the envelope's *authenticated* thread (SPEC-015
    /// REQ-702).
    ///
    /// This is the safety-level seam: `protocol::verify_causal` falls back
    /// to it when a `:caused-by` reference has no full message, reading
    /// only the envelope's authenticated performative type. The
    /// completion-level occupant fan-in (`projection.rs`, REQ-618)
    /// deliberately never consults it (REQ-703).
    ///
    /// Default: no envelope shelf (stores predating SPEC-015 change
    /// nothing and keep their exact v1 behaviour).
    fn envelope_in_thread(
        &self,
        hash: &ContentHash,
        thread: &ThreadId,
    ) -> Option<&RedactedEnvelope> {
        let _ = (hash, thread);
        None
    }

    /// Look up an opened envelope by the typed content root of the message
    /// it opens, scoped to the envelope's *authenticated* Thread opening
    /// (SPEC-017 REQ-813).
    ///
    /// The Stage-3 native-openings counterpart of [`Self::envelope_in_thread`]:
    /// `protocol::verify_causal` falls back to it for the safety-level
    /// predecessor type when a `:caused-by` reference has no full message,
    /// reading only the envelope's authenticated Performative opening. The
    /// completion-level occupant fan-in (`projection.rs`, REQ-703) never
    /// consults it — that boundary is preserved exactly as for redacted
    /// envelopes.
    ///
    /// Default: no opened shelf (stores that never accept opened envelopes
    /// keep their exact behaviour).
    fn opened_in_thread(
        &self,
        hash: &ContentHash,
        thread: &ThreadId,
    ) -> Option<&OpenedEnvelope> {
        let _ = (hash, thread);
        None
    }
}

/// Per-thread append-only message store with G-Set CRDT semantics (REQ-300).
///
/// Uses [`HashIndex`] for O(1) lookup (REQ-309) and deduplication (REQ-310).
/// Maintains a frontier set per thread for efficient leaf queries.
#[derive(Debug, Clone)]
pub struct ThreadedMessageStore {
    /// Per-thread message storage: `ThreadId -> Vec<(ContentHash, Message)>`.
    threads: HashMap<ThreadId, Vec<(ContentHash, Message)>>,
    /// Global hash index for O(1) lookup.
    index: HashIndex,
    /// Per-thread set of hashes referenced by some message's `:caused-by`.
    referenced: HashMap<ThreadId, HashSet<ContentHash>>,
    /// Redacted-envelope shelf (SPEC-015 REQ-702), keyed by the content
    /// hash of the redacted message. Thread placement is the envelope's
    /// authenticated thread field, checked at lookup — an envelope can
    /// never be filed under a thread its signature does not vouch for.
    envelopes: HashMap<ContentHash, RedactedEnvelope>,
    /// Opened-envelope shelf (SPEC-017 REQ-813), keyed by the typed content
    /// root of the opened message. Thread placement is the envelope's
    /// authenticated Thread opening, checked at lookup — as for the redacted
    /// shelf, an opened envelope can never be filed under a thread its
    /// signature and opening do not vouch for.
    opened: HashMap<ContentHash, OpenedEnvelope>,
}

impl ThreadedMessageStore {
    /// Creates an empty message store.
    pub fn new() -> Self {
        Self {
            threads: HashMap::new(),
            index: HashIndex::new(),
            referenced: HashMap::new(),
            envelopes: HashMap::new(),
            opened: HashMap::new(),
        }
    }

    /// Accept a redacted envelope (SPEC-015 REQ-702).
    ///
    /// Verifies the envelope's R4 v2 attestation from its own fields first
    /// (`signer` embodies verification for the envelope's sender key), then
    /// places it in the thread its *authenticated* thread field names —
    /// there is deliberately no thread parameter, so cross-thread injection
    /// of a genuine envelope is a signature failure at the source, not a
    /// policy question. An unverifiable envelope is never stored.
    ///
    /// Returns `Ok(true)` if newly shelved, `Ok(false)` if an envelope for
    /// this content hash is already present (G-Set dedup, as for messages).
    pub fn append_envelope(
        &mut self,
        envelope: RedactedEnvelope,
        signer: &dyn Signer,
    ) -> Result<bool, AttestError> {
        envelope.verify(signer)?;
        use hashbrown::hash_map::Entry;
        match self
            .envelopes
            .entry(ContentHash(envelope.header.content_hash.clone()))
        {
            Entry::Vacant(e) => {
                e.insert(envelope);
                Ok(true)
            }
            Entry::Occupied(_) => Ok(false),
        }
    }

    /// Accept an opened envelope (SPEC-017 REQ-813).
    ///
    /// Verifies the v3 root-signature and every field-opening from the
    /// envelope's own fields first (`signer` embodies verification for the
    /// sender key), then shelves it under its typed root, placed in the
    /// thread its *authenticated* Thread opening names. As with
    /// [`Self::append_envelope`] there is deliberately no thread parameter,
    /// so cross-thread injection of a genuine envelope is a signature/opening
    /// failure at the source, not a policy question; an envelope that does
    /// not open its Thread leaf cannot be placed (fail closed).
    ///
    /// Returns `Ok(true)` if newly shelved, `Ok(false)` if an opened
    /// envelope for this root is already present (G-Set dedup).
    pub fn append_opened(
        &mut self,
        envelope: OpenedEnvelope,
        signer: &dyn Signer,
    ) -> Result<bool, OpenedError> {
        verify_opened(&envelope, signer)?;
        // Thread placement is by an *authenticated* opening; an envelope
        // whose Thread leaf is not opened has no place to go.
        if envelope.thread().is_none() {
            return Err(OpenedError::MissingField {
                field: FieldId::Thread,
            });
        }
        use hashbrown::hash_map::Entry;
        match self.opened.entry(ContentHash(envelope.root.clone())) {
            Entry::Vacant(e) => {
                e.insert(envelope);
                Ok(true)
            }
            Entry::Occupied(_) => Ok(false),
        }
    }
}

impl Default for ThreadedMessageStore {
    fn default() -> Self {
        Self::new()
    }
}

impl MessageStore for ThreadedMessageStore {
    fn lookup(&self, hash: &ContentHash) -> Option<&Message> {
        // Look up in the global index (ignoring thread isolation)
        let (thread, idx) = self.index.map.get(hash)?;
        self.threads
            .get(thread)
            .and_then(|msgs| msgs.get(*idx).map(|(_, m)| m))
    }

    fn lookup_in_thread(&self, hash: &ContentHash, thread: &ThreadId) -> Option<&Message> {
        let idx = self.index.lookup(hash, thread)?;
        self.threads
            .get(thread)
            .and_then(|msgs| msgs.get(idx).map(|(_, m)| m))
    }

    fn contains(&self, hash: &ContentHash, thread: &ThreadId) -> bool {
        self.index.contains(hash, thread)
    }

    fn append(&mut self, hash: ContentHash, thread: ThreadId, message: Message) -> bool {
        let thread_msgs = self.threads.entry(thread.clone()).or_default();
        let idx = thread_msgs.len();

        if !self.index.insert(hash.clone(), thread.clone(), idx) {
            return false; // duplicate
        }

        // Track caused-by references for frontier computation
        if let Some(cb) = message.caused_by() {
            let refs = self.referenced.entry(thread.clone()).or_default();
            match cb {
                CausedBy::Begin => {}
                CausedBy::Single(h) => {
                    refs.insert(ContentHash(h.clone()));
                }
                CausedBy::Multiple(hs) => {
                    for h in hs {
                        refs.insert(ContentHash(h.clone()));
                    }
                }
            }
        }

        thread_msgs.push((hash, message));
        true
    }

    fn frontier(&self, thread: &ThreadId) -> Vec<&ContentHash> {
        let Some(msgs) = self.threads.get(thread) else {
            return Vec::new();
        };
        let empty = HashSet::new();
        let refs = self.referenced.get(thread).unwrap_or(&empty);
        msgs.iter()
            .map(|(h, _)| h)
            .filter(|h| !refs.contains(*h))
            .collect()
    }

    fn causal_closure(&self, hash: &ContentHash, thread: &ThreadId) -> Vec<ContentHash> {
        let mut result = Vec::new();
        let mut visited = HashSet::new();
        let mut stack = Vec::new();

        if self.index.contains(hash, thread) {
            stack.push(hash.clone());
        }

        while let Some(current) = stack.pop() {
            if !visited.insert(current.clone()) {
                continue;
            }
            result.push(current.clone());

            // Look up the message and follow its caused-by links
            if let Some(msg) = self.lookup_in_thread(&current, thread) {
                if let Some(cb) = msg.caused_by() {
                    match cb {
                        CausedBy::Begin => {}
                        CausedBy::Single(h) => {
                            let ch = ContentHash(h.clone());
                            if !visited.contains(&ch) {
                                stack.push(ch);
                            }
                        }
                        CausedBy::Multiple(hs) => {
                            for h in hs {
                                let ch = ContentHash(h.clone());
                                if !visited.contains(&ch) {
                                    stack.push(ch);
                                }
                            }
                        }
                    }
                }
            }
        }

        result
    }

    fn envelope_in_thread(
        &self,
        hash: &ContentHash,
        thread: &ThreadId,
    ) -> Option<&RedactedEnvelope> {
        // Thread scoping is by the envelope's authenticated field (REQ-702):
        // the shelf never records a caller-chosen thread to compare against.
        self.envelopes
            .get(hash)
            .filter(|e| e.header.thread == thread.0)
    }

    fn opened_in_thread(
        &self,
        hash: &ContentHash,
        thread: &ThreadId,
    ) -> Option<&OpenedEnvelope> {
        // Thread scoping is by the envelope's authenticated Thread opening
        // (REQ-813): the shelf holds no caller-chosen thread to compare.
        self.opened
            .get(hash)
            .filter(|e| e.thread() == Some(thread.0.as_str()))
    }
}

// ================================================================
// Causal Closure Bundle (REQ-311, REQ-212, CON-304)
// ================================================================

/// Error during causal closure extraction.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ClosureError {
    /// Target message not found in the store.
    TargetNotFound,
    /// Store is incomplete — some `:caused-by` hashes are missing.
    IncompleteStore { missing_hashes: Vec<ContentHash> },
}

impl fmt::Display for ClosureError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TargetNotFound => write!(f, "target message not found in store"),
            Self::IncompleteStore { missing_hashes } => {
                write!(f, "incomplete store, missing hashes: ")?;
                for (i, h) in missing_hashes.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", h.0)?;
                }
                Ok(())
            }
        }
    }
}

/// Error during bundle verification.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum BundleVerificationError {
    /// A message's content hash does not match its computed hash.
    HashMismatch {
        hash: ContentHash,
        expected: ContentHash,
        computed: ContentHash,
    },
    /// A `:caused-by` hash does not resolve within the bundle.
    DanglingReference { caused_by: String },
    /// A causal link violates the protocol declaration.
    CausalViolation(CausalViolation),
}

impl fmt::Display for BundleVerificationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::HashMismatch {
                hash,
                expected,
                computed,
            } => write!(
                f,
                "hash mismatch for {}: expected {}, computed {}",
                hash.0, expected.0, computed.0
            ),
            Self::DanglingReference { caused_by } => {
                write!(f, "dangling :caused-by reference: {caused_by}")
            }
            Self::CausalViolation(v) => write!(f, "causal violation: {v}"),
        }
    }
}

/// Result of merging a bundle into a store.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MergeResult {
    /// Number of messages newly added to the store.
    pub added: usize,
    /// Number of messages already present (deduplicated).
    pub deduplicated: usize,
}

/// A transferable, verifiable subset of the message store (REQ-311, CON-304).
///
/// Contains the principal ideal ↓target — all messages reachable by following
/// `:caused-by` links from the target back to root(s). Messages are stored in
/// topological order (predecessors before successors).
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CausalClosureBundle {
    /// The target message this bundle is the causal closure of.
    pub target: ContentHash,
    /// The thread this bundle belongs to.
    pub thread: ThreadId,
    /// All messages in ↓target, topologically sorted (predecessors first).
    /// Each entry is `(content_hash, message)`.
    pub messages: Vec<(ContentHash, Message)>,
}

impl CausalClosureBundle {
    /// Extract the causal closure (principal ideal ↓target) from a store (REQ-311).
    ///
    /// Performs a DAG traversal following `:caused-by` links from `target` back
    /// to root(s). The resulting bundle is topologically sorted: every message
    /// appears after all of its predecessors.
    pub fn extract<S: MessageStore>(
        target: &ContentHash,
        thread: &ThreadId,
        store: &S,
    ) -> Result<Self, ClosureError> {
        // Verify target exists
        let target_msg = store
            .lookup_in_thread(target, thread)
            .ok_or(ClosureError::TargetNotFound)?;

        // Phase 1: DFS to collect all hashes in the closure
        let mut visited = HashSet::new();
        let mut stack = vec![target.clone()];
        let mut hash_to_msg: Vec<(ContentHash, Message)> = Vec::new();
        let mut missing = Vec::new();

        // We need the target message; clone it here
        let _ = target_msg; // used only to verify existence above

        while let Some(current) = stack.pop() {
            if !visited.insert(current.clone()) {
                continue;
            }

            let msg = match store.lookup_in_thread(&current, thread) {
                Some(m) => m,
                None => {
                    missing.push(current);
                    continue;
                }
            };

            hash_to_msg.push((current.clone(), msg.clone()));

            // Follow caused-by links
            if let Some(cb) = msg.caused_by() {
                match cb {
                    CausedBy::Begin => {}
                    CausedBy::Single(h) => {
                        let ch = ContentHash(h.clone());
                        if !visited.contains(&ch) {
                            stack.push(ch);
                        }
                    }
                    CausedBy::Multiple(hs) => {
                        for h in hs {
                            let ch = ContentHash(h.clone());
                            if !visited.contains(&ch) {
                                stack.push(ch);
                            }
                        }
                    }
                }
            }
        }

        if !missing.is_empty() {
            return Err(ClosureError::IncompleteStore {
                missing_hashes: missing,
            });
        }

        // Phase 2: Topological sort (Kahn's algorithm — predecessors before successors)
        // Use indices into hash_to_msg to avoid lifetime issues.
        let hash_to_idx: HashMap<ContentHash, usize> = hash_to_msg
            .iter()
            .enumerate()
            .map(|(i, (h, _))| (h.clone(), i))
            .collect();

        let n = hash_to_msg.len();
        let mut in_degree: Vec<usize> = alloc::vec![0; n];
        let mut successors_map: Vec<Vec<usize>> = (0..n).map(|_| Vec::new()).collect();

        // Build edges: for each message, its caused-by predecessors have an edge TO this message
        for (idx, (_, m)) in hash_to_msg.iter().enumerate() {
            if let Some(cb) = m.caused_by() {
                let pred_hashes: Vec<&str> = match cb {
                    CausedBy::Begin => vec![],
                    CausedBy::Single(p) => vec![p.as_str()],
                    CausedBy::Multiple(ps) => ps.iter().map(|p| p.as_str()).collect(),
                };
                for p in pred_hashes {
                    if let Some(&pred_idx) = hash_to_idx.get(&ContentHash(p.into())) {
                        successors_map[pred_idx].push(idx);
                        in_degree[idx] += 1;
                    }
                }
            }
        }

        // Kahn's: start with nodes having in-degree 0
        let mut queue: Vec<usize> = (0..n).filter(|&i| in_degree[i] == 0).collect();
        // Sort by hash for deterministic ordering
        queue.sort_by(|&a, &b| hash_to_msg[a].0.cmp(&hash_to_msg[b].0));

        let mut sorted_indices: Vec<usize> = Vec::with_capacity(n);

        while let Some(node) = queue.pop() {
            sorted_indices.push(node);
            for &succ in &successors_map[node] {
                in_degree[succ] -= 1;
                if in_degree[succ] == 0 {
                    // Insert in sorted position for determinism
                    let pos = queue.partition_point(|&x| {
                        hash_to_msg[x].0.cmp(&hash_to_msg[succ].0) == core::cmp::Ordering::Greater
                    });
                    queue.insert(pos, succ);
                }
            }
        }

        // Build the sorted messages vec
        let mut msg_slots: Vec<Option<(ContentHash, Message)>> =
            hash_to_msg.into_iter().map(Some).collect();
        let messages: Vec<(ContentHash, Message)> = sorted_indices
            .into_iter()
            .filter_map(|i| msg_slots[i].take())
            .collect();

        Ok(CausalClosureBundle {
            target: target.clone(),
            thread: thread.clone(),
            messages,
        })
    }

    /// Verify bundle completeness — all `:caused-by` hashes resolve within the bundle.
    ///
    /// This is the Tier 2 verification path (REQ-212): verify that the bundle is
    /// self-contained. No external store or protocol is needed.
    pub fn verify_completeness(&self) -> Result<(), Vec<BundleVerificationError>> {
        let known: HashSet<&str> = self.messages.iter().map(|(h, _)| h.0.as_str()).collect();
        let mut errors = Vec::new();

        for (_, msg) in &self.messages {
            if let Some(cb) = msg.caused_by() {
                let refs: Vec<&str> = match cb {
                    CausedBy::Begin => vec![],
                    CausedBy::Single(h) => vec![h.as_str()],
                    CausedBy::Multiple(hs) => hs.iter().map(|h| h.as_str()).collect(),
                };
                for r in refs {
                    if !known.contains(r) {
                        errors.push(BundleVerificationError::DanglingReference {
                            caused_by: r.into(),
                        });
                    }
                }
            }
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    /// Verify hash integrity using a caller-supplied hash function.
    ///
    /// For each message in the bundle, recomputes the hash from the message content
    /// and verifies it matches the stored content hash. The hasher function receives
    /// a reference to a `Message` and should return the computed `ContentHash`
    /// (typically SHA-256 of the canonical serialisation).
    pub fn verify_hashes<F>(&self, hasher: F) -> Result<(), Vec<BundleVerificationError>>
    where
        F: Fn(&Message) -> ContentHash,
    {
        let mut errors = Vec::new();

        for (expected_hash, msg) in &self.messages {
            let computed = hasher(msg);
            if &computed != expected_hash {
                errors.push(BundleVerificationError::HashMismatch {
                    hash: expected_hash.clone(),
                    expected: expected_hash.clone(),
                    computed,
                });
            }
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    /// Verify causal validity against a protocol declaration (Tier 3, REQ-212).
    ///
    /// Builds a temporary store from the bundle messages and runs causal
    /// verification (REQ-203) on each message against the given protocol.
    pub fn verify_causal(
        &self,
        protocol: &CausalProtocol,
    ) -> Result<(), Vec<BundleVerificationError>> {
        // Build a temporary store from the bundle
        let mut temp_store = ThreadedMessageStore::new();
        for (hash, msg) in &self.messages {
            temp_store.append(hash.clone(), self.thread.clone(), msg.clone());
        }

        let mut errors = Vec::new();
        for (_, msg) in &self.messages {
            let perf_name = msg.performative().map(|p| p.name()).unwrap_or("");

            let result = crate::protocol::verify_causal(
                perf_name,
                msg.caused_by(),
                &temp_store,
                protocol,
                &self.thread,
            );

            if let VerificationResult::Violation(v) = result {
                errors.push(BundleVerificationError::CausalViolation(v));
            }
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    /// Full verification: completeness + hash integrity + causal validity (Tier 3, REQ-212).
    ///
    /// Combines all three verification checks. The hasher function computes
    /// content hashes; the protocol is used for causal validity checking.
    pub fn verify_full<F>(
        &self,
        hasher: F,
        protocol: &CausalProtocol,
    ) -> Result<(), Vec<BundleVerificationError>>
    where
        F: Fn(&Message) -> ContentHash,
    {
        let mut all_errors = Vec::new();

        if let Err(mut errs) = self.verify_completeness() {
            all_errors.append(&mut errs);
        }
        if let Err(mut errs) = self.verify_hashes(hasher) {
            all_errors.append(&mut errs);
        }
        if let Err(mut errs) = self.verify_causal(protocol) {
            all_errors.append(&mut errs);
        }

        if all_errors.is_empty() {
            Ok(())
        } else {
            Err(all_errors)
        }
    }

    /// Merge this bundle into a message store (set union with deduplication, REQ-300).
    ///
    /// Messages already present in the store are skipped (REQ-310 deduplication).
    /// Returns counts of newly added and deduplicated messages.
    pub fn merge<S: MessageStore>(&self, store: &mut S) -> MergeResult {
        let mut added = 0;
        let mut deduplicated = 0;

        for (hash, msg) in &self.messages {
            if store.append(hash.clone(), self.thread.clone(), msg.clone()) {
                added += 1;
            } else {
                deduplicated += 1;
            }
        }

        MergeResult {
            added,
            deduplicated,
        }
    }

    /// Serialize this bundle to a `(meta (causal-closure ...))` S-expression (REQ-311).
    pub fn to_sexpr(&self) -> SExpr {
        let mut inner = vec![
            SExpr::Atom(Atom::Symbol("causal-closure".into())),
            SExpr::Atom(Atom::Keyword("target".into())),
            SExpr::Atom(Atom::Str(self.target.0.clone())),
            SExpr::Atom(Atom::Keyword("thread".into())),
            SExpr::Atom(Atom::Str(self.thread.0.clone())),
            SExpr::Atom(Atom::Keyword("messages".into())),
        ];

        let msg_list: Vec<SExpr> = self
            .messages
            .iter()
            .map(|(_, msg)| SExpr::from(msg))
            .collect();

        inner.push(SExpr::List(msg_list));

        SExpr::List(vec![
            SExpr::Atom(Atom::Symbol("meta".into())),
            SExpr::List(inner),
        ])
    }

    /// Returns the number of messages in the bundle.
    pub fn len(&self) -> usize {
        self.messages.len()
    }

    /// Returns true if the bundle contains no messages.
    pub fn is_empty(&self) -> bool {
        self.messages.is_empty()
    }

    /// Returns the content hashes of all messages in the bundle, in topological order.
    pub fn hashes(&self) -> Vec<&ContentHash> {
        self.messages.iter().map(|(h, _)| h).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::string::ToString;
    use alloc::vec;
    use alloc::vec::Vec;

    fn hash(s: &str) -> ContentHash {
        ContentHash(s.to_string())
    }

    fn thread(s: &str) -> ThreadId {
        ThreadId(s.to_string())
    }

    // --- insert tests ---

    #[test]
    fn insert_returns_true_for_new_entry() {
        let mut idx = HashIndex::new();
        assert!(idx.insert(hash("h1"), thread("t1"), 0));
    }

    #[test]
    fn insert_returns_false_for_duplicate() {
        let mut idx = HashIndex::new();
        idx.insert(hash("h1"), thread("t1"), 0);
        assert!(!idx.insert(hash("h1"), thread("t1"), 1));
    }

    #[test]
    fn insert_duplicate_does_not_overwrite() {
        let mut idx = HashIndex::new();
        idx.insert(hash("h1"), thread("t1"), 0);
        idx.insert(hash("h1"), thread("t2"), 99);
        // Original entry preserved
        assert_eq!(idx.lookup(&hash("h1"), &thread("t1")), Some(0));
    }

    #[test]
    fn insert_distinct_hashes_independent() {
        let mut idx = HashIndex::new();
        assert!(idx.insert(hash("h1"), thread("t1"), 0));
        assert!(idx.insert(hash("h2"), thread("t1"), 1));
        assert_eq!(idx.len(), 2);
    }

    // --- lookup tests ---

    #[test]
    fn lookup_returns_index_for_matching_thread() {
        let mut idx = HashIndex::new();
        idx.insert(hash("h1"), thread("t1"), 42);
        assert_eq!(idx.lookup(&hash("h1"), &thread("t1")), Some(42));
    }

    #[test]
    fn lookup_returns_none_for_wrong_thread() {
        let mut idx = HashIndex::new();
        idx.insert(hash("h1"), thread("t1"), 42);
        assert_eq!(idx.lookup(&hash("h1"), &thread("t2")), None);
    }

    #[test]
    fn lookup_returns_none_for_absent_hash() {
        let idx = HashIndex::new();
        assert_eq!(idx.lookup(&hash("h1"), &thread("t1")), None);
    }

    // --- contains tests ---

    #[test]
    fn contains_true_for_matching_thread() {
        let mut idx = HashIndex::new();
        idx.insert(hash("h1"), thread("t1"), 0);
        assert!(idx.contains(&hash("h1"), &thread("t1")));
    }

    #[test]
    fn contains_false_for_wrong_thread() {
        let mut idx = HashIndex::new();
        idx.insert(hash("h1"), thread("t1"), 0);
        assert!(!idx.contains(&hash("h1"), &thread("t2")));
    }

    #[test]
    fn contains_false_for_absent_hash() {
        let idx = HashIndex::new();
        assert!(!idx.contains(&hash("nonexistent"), &thread("t1")));
    }

    // --- thread isolation (ADR-008) ---

    #[test]
    fn thread_isolation_across_multiple_threads() {
        let mut idx = HashIndex::new();
        idx.insert(hash("h1"), thread("t1"), 0);
        idx.insert(hash("h2"), thread("t2"), 1);
        idx.insert(hash("h3"), thread("t1"), 2);

        // t1 sees h1 and h3, not h2
        assert_eq!(idx.lookup(&hash("h1"), &thread("t1")), Some(0));
        assert_eq!(idx.lookup(&hash("h3"), &thread("t1")), Some(2));
        assert_eq!(idx.lookup(&hash("h2"), &thread("t1")), None);

        // t2 sees h2, not h1 or h3
        assert_eq!(idx.lookup(&hash("h2"), &thread("t2")), Some(1));
        assert_eq!(idx.lookup(&hash("h1"), &thread("t2")), None);
        assert_eq!(idx.lookup(&hash("h3"), &thread("t2")), None);
    }

    // --- rebuild tests ---

    #[test]
    fn rebuild_clears_and_repopulates() {
        let mut idx = HashIndex::new();
        idx.insert(hash("old"), thread("t1"), 0);

        idx.rebuild(vec![
            (hash("new1"), thread("t1"), 0),
            (hash("new2"), thread("t2"), 1),
        ]);

        assert_eq!(idx.len(), 2);
        assert_eq!(idx.lookup(&hash("old"), &thread("t1")), None);
        assert_eq!(idx.lookup(&hash("new1"), &thread("t1")), Some(0));
        assert_eq!(idx.lookup(&hash("new2"), &thread("t2")), Some(1));
    }

    #[test]
    fn rebuild_skips_duplicates_first_wins() {
        let mut idx = HashIndex::new();
        idx.rebuild(vec![
            (hash("h1"), thread("t1"), 0),
            (hash("h1"), thread("t2"), 99),
        ]);
        assert_eq!(idx.len(), 1);
        assert_eq!(idx.lookup(&hash("h1"), &thread("t1")), Some(0));
    }

    #[test]
    fn rebuild_from_empty_iterator() {
        let mut idx = HashIndex::new();
        idx.insert(hash("h1"), thread("t1"), 0);
        idx.rebuild(Vec::<(ContentHash, ThreadId, usize)>::new());
        assert!(idx.is_empty());
    }

    // --- len / is_empty ---

    #[test]
    fn new_index_is_empty() {
        let idx = HashIndex::new();
        assert!(idx.is_empty());
        assert_eq!(idx.len(), 0);
    }

    #[test]
    fn len_tracks_insertions() {
        let mut idx = HashIndex::new();
        idx.insert(hash("h1"), thread("t1"), 0);
        idx.insert(hash("h2"), thread("t1"), 1);
        assert_eq!(idx.len(), 2);
        assert!(!idx.is_empty());
    }

    // --- with_capacity ---

    #[test]
    fn with_capacity_creates_empty_index() {
        let idx = HashIndex::with_capacity(100);
        assert!(idx.is_empty());
    }

    // --- Default ---

    #[test]
    fn default_creates_empty_index() {
        let idx = HashIndex::default();
        assert!(idx.is_empty());
    }

    // --- scale test (TEST-309: 10K messages across 10 threads) ---

    #[test]
    fn scale_10k_messages_10_threads() {
        let mut idx = HashIndex::new();
        let threads: Vec<ThreadId> = (0..10).map(|i| thread(&i.to_string())).collect();

        // Insert 10K messages across 10 threads (1K per thread)
        for t in 0..10 {
            for m in 0..1000 {
                let h = hash(&alloc::format!("t{}-m{}", t, m));
                assert!(idx.insert(h, threads[t].clone(), m));
            }
        }
        assert_eq!(idx.len(), 10_000);

        // Verify thread isolation: each message visible only in its own thread
        for t in 0..10 {
            for m in 0..1000 {
                let h = hash(&alloc::format!("t{}-m{}", t, m));
                assert_eq!(idx.lookup(&h, &threads[t]), Some(m));
                // Cross-thread lookup must fail
                let other = &threads[(t + 1) % 10];
                assert_eq!(idx.lookup(&h, other), None);
            }
        }

        // Rebuild and verify
        let mut entries = Vec::with_capacity(10_000);
        for t in 0..10 {
            for m in 0..1000 {
                entries.push((
                    hash(&alloc::format!("t{}-m{}", t, m)),
                    threads[t].clone(),
                    m,
                ));
            }
        }
        idx.rebuild(entries);
        assert_eq!(idx.len(), 10_000);

        // Spot check after rebuild
        assert_eq!(idx.lookup(&hash("t5-m500"), &threads[5]), Some(500));
        assert_eq!(idx.lookup(&hash("t5-m500"), &threads[0]), None);
    }

    // =========================================================================
    // ThreadedMessageStore tests
    // =========================================================================

    use crate::message::{CausedBy, Performative};
    use crate::sexpr::{Atom, SExpr};

    /// Helper: create a simple message with optional caused_by and thread.
    fn simple_msg(perf: &str, content: &str, caused_by: Option<CausedBy>) -> Message {
        Message::Simple {
            performative: Performative::Core(
                crate::message::CorePerformative::parse(perf)
                    .unwrap_or(crate::message::CorePerformative::Tell),
            ),
            recipient: None,
            content: SExpr::Atom(Atom::Str(content.to_string())),
            params: Vec::new(),
            thread: None,
            sender: None,
            caused_by,
        }
    }

    // --- append tests (REQ-310 deduplication) ---

    #[test]
    fn append_returns_true_for_new_message() {
        let mut store = ThreadedMessageStore::new();
        let msg = simple_msg("tell", "hello", Some(CausedBy::Begin));
        assert!(store.append(hash("h1"), thread("t1"), msg));
    }

    #[test]
    fn append_returns_false_for_duplicate_hash() {
        let mut store = ThreadedMessageStore::new();
        let msg1 = simple_msg("tell", "hello", Some(CausedBy::Begin));
        let msg2 = simple_msg("tell", "hello again", Some(CausedBy::Begin));
        store.append(hash("h1"), thread("t1"), msg1);
        assert!(!store.append(hash("h1"), thread("t1"), msg2));
    }

    #[test]
    fn append_duplicate_cross_thread_rejected() {
        let mut store = ThreadedMessageStore::new();
        let msg1 = simple_msg("tell", "hello", Some(CausedBy::Begin));
        let msg2 = simple_msg("tell", "hello", Some(CausedBy::Begin));
        store.append(hash("h1"), thread("t1"), msg1);
        // Same hash in different thread is still a duplicate (global dedup)
        assert!(!store.append(hash("h1"), thread("t2"), msg2));
    }

    // --- lookup tests ---

    #[test]
    fn lookup_returns_message_across_threads() {
        let mut store = ThreadedMessageStore::new();
        let msg = simple_msg("tell", "hello", Some(CausedBy::Begin));
        store.append(hash("h1"), thread("t1"), msg);
        let found = store.lookup(&hash("h1"));
        assert!(found.is_some());
        assert_eq!(
            found.unwrap().performative(),
            Some(&Performative::Core(crate::message::CorePerformative::Tell))
        );
    }

    #[test]
    fn lookup_returns_none_for_absent() {
        let store = ThreadedMessageStore::new();
        assert!(store.lookup(&hash("nonexistent")).is_none());
    }

    // --- lookup_in_thread tests ---

    #[test]
    fn lookup_in_thread_returns_message_for_correct_thread() {
        let mut store = ThreadedMessageStore::new();
        let msg = simple_msg("tell", "hello", Some(CausedBy::Begin));
        store.append(hash("h1"), thread("t1"), msg);
        assert!(store.lookup_in_thread(&hash("h1"), &thread("t1")).is_some());
    }

    #[test]
    fn lookup_in_thread_returns_none_for_wrong_thread() {
        let mut store = ThreadedMessageStore::new();
        let msg = simple_msg("tell", "hello", Some(CausedBy::Begin));
        store.append(hash("h1"), thread("t1"), msg);
        assert!(store.lookup_in_thread(&hash("h1"), &thread("t2")).is_none());
    }

    #[test]
    fn lookup_in_thread_returns_none_for_absent() {
        let store = ThreadedMessageStore::new();
        assert!(store.lookup_in_thread(&hash("h1"), &thread("t1")).is_none());
    }

    // --- contains tests ---

    #[test]
    fn contains_true_for_existing_in_thread() {
        let mut store = ThreadedMessageStore::new();
        let msg = simple_msg("tell", "hello", Some(CausedBy::Begin));
        store.append(hash("h1"), thread("t1"), msg);
        assert!(store.contains(&hash("h1"), &thread("t1")));
    }

    #[test]
    fn store_contains_false_for_wrong_thread() {
        let mut store = ThreadedMessageStore::new();
        let msg = simple_msg("tell", "hello", Some(CausedBy::Begin));
        store.append(hash("h1"), thread("t1"), msg);
        assert!(!store.contains(&hash("h1"), &thread("t2")));
    }

    #[test]
    fn contains_false_for_absent() {
        let store = ThreadedMessageStore::new();
        assert!(!store.contains(&hash("h1"), &thread("t1")));
    }

    // --- frontier tests (leaf messages) ---

    #[test]
    fn frontier_empty_thread_returns_empty() {
        let store = ThreadedMessageStore::new();
        assert!(store.frontier(&thread("t1")).is_empty());
    }

    #[test]
    fn frontier_single_begin_message_is_frontier() {
        let mut store = ThreadedMessageStore::new();
        store.append(
            hash("h1"),
            thread("t1"),
            simple_msg("tell", "start", Some(CausedBy::Begin)),
        );
        let f = store.frontier(&thread("t1"));
        assert_eq!(f.len(), 1);
        assert_eq!(f[0], &hash("h1"));
    }

    #[test]
    fn frontier_chain_only_leaf_is_frontier() {
        let mut store = ThreadedMessageStore::new();
        store.append(
            hash("h1"),
            thread("t1"),
            simple_msg("tell", "start", Some(CausedBy::Begin)),
        );
        store.append(
            hash("h2"),
            thread("t1"),
            simple_msg("reply", "ack", Some(CausedBy::Single("h1".into()))),
        );
        let f = store.frontier(&thread("t1"));
        assert_eq!(f.len(), 1);
        assert_eq!(f[0], &hash("h2"));
    }

    #[test]
    fn frontier_branching_two_leaves() {
        let mut store = ThreadedMessageStore::new();
        store.append(
            hash("root"),
            thread("t1"),
            simple_msg("tell", "start", Some(CausedBy::Begin)),
        );
        store.append(
            hash("b1"),
            thread("t1"),
            simple_msg("reply", "branch1", Some(CausedBy::Single("root".into()))),
        );
        store.append(
            hash("b2"),
            thread("t1"),
            simple_msg("reply", "branch2", Some(CausedBy::Single("root".into()))),
        );
        let mut f: Vec<_> = store.frontier(&thread("t1")).into_iter().cloned().collect();
        f.sort();
        assert_eq!(f, vec![hash("b1"), hash("b2")]);
    }

    #[test]
    fn frontier_fan_in_merge_removes_predecessors() {
        let mut store = ThreadedMessageStore::new();
        store.append(
            hash("root"),
            thread("t1"),
            simple_msg("tell", "start", Some(CausedBy::Begin)),
        );
        store.append(
            hash("b1"),
            thread("t1"),
            simple_msg("reply", "a", Some(CausedBy::Single("root".into()))),
        );
        store.append(
            hash("b2"),
            thread("t1"),
            simple_msg("reply", "b", Some(CausedBy::Single("root".into()))),
        );
        // Merge message references both branches
        store.append(
            hash("merge"),
            thread("t1"),
            simple_msg(
                "ok",
                "done",
                Some(CausedBy::Multiple(vec!["b1".into(), "b2".into()])),
            ),
        );
        let f = store.frontier(&thread("t1"));
        assert_eq!(f.len(), 1);
        assert_eq!(f[0], &hash("merge"));
    }

    #[test]
    fn frontier_separate_threads_independent() {
        let mut store = ThreadedMessageStore::new();
        store.append(
            hash("h1"),
            thread("t1"),
            simple_msg("tell", "a", Some(CausedBy::Begin)),
        );
        store.append(
            hash("h2"),
            thread("t2"),
            simple_msg("tell", "b", Some(CausedBy::Begin)),
        );
        assert_eq!(store.frontier(&thread("t1")).len(), 1);
        assert_eq!(store.frontier(&thread("t2")).len(), 1);
    }

    // --- causal_closure tests (principal ideal) ---

    #[test]
    fn causal_closure_begin_message_is_singleton() {
        let mut store = ThreadedMessageStore::new();
        store.append(
            hash("h1"),
            thread("t1"),
            simple_msg("tell", "start", Some(CausedBy::Begin)),
        );
        let cc = store.causal_closure(&hash("h1"), &thread("t1"));
        assert_eq!(cc.len(), 1);
        assert_eq!(cc[0], hash("h1"));
    }

    #[test]
    fn causal_closure_chain_returns_all_ancestors() {
        let mut store = ThreadedMessageStore::new();
        store.append(
            hash("h1"),
            thread("t1"),
            simple_msg("tell", "start", Some(CausedBy::Begin)),
        );
        store.append(
            hash("h2"),
            thread("t1"),
            simple_msg("reply", "mid", Some(CausedBy::Single("h1".into()))),
        );
        store.append(
            hash("h3"),
            thread("t1"),
            simple_msg("ok", "end", Some(CausedBy::Single("h2".into()))),
        );
        let mut cc = store.causal_closure(&hash("h3"), &thread("t1"));
        cc.sort();
        assert_eq!(cc, vec![hash("h1"), hash("h2"), hash("h3")]);
    }

    #[test]
    fn causal_closure_fan_in_includes_all_branches() {
        let mut store = ThreadedMessageStore::new();
        store.append(
            hash("root"),
            thread("t1"),
            simple_msg("tell", "start", Some(CausedBy::Begin)),
        );
        store.append(
            hash("b1"),
            thread("t1"),
            simple_msg("reply", "a", Some(CausedBy::Single("root".into()))),
        );
        store.append(
            hash("b2"),
            thread("t1"),
            simple_msg("reply", "b", Some(CausedBy::Single("root".into()))),
        );
        store.append(
            hash("merge"),
            thread("t1"),
            simple_msg(
                "ok",
                "done",
                Some(CausedBy::Multiple(vec!["b1".into(), "b2".into()])),
            ),
        );
        let mut cc = store.causal_closure(&hash("merge"), &thread("t1"));
        cc.sort();
        assert_eq!(
            cc,
            vec![hash("b1"), hash("b2"), hash("merge"), hash("root")]
        );
    }

    #[test]
    fn causal_closure_absent_message_returns_empty() {
        let store = ThreadedMessageStore::new();
        let cc = store.causal_closure(&hash("nonexistent"), &thread("t1"));
        assert!(cc.is_empty());
    }

    #[test]
    fn causal_closure_wrong_thread_returns_empty() {
        let mut store = ThreadedMessageStore::new();
        store.append(
            hash("h1"),
            thread("t1"),
            simple_msg("tell", "start", Some(CausedBy::Begin)),
        );
        let cc = store.causal_closure(&hash("h1"), &thread("t2"));
        assert!(cc.is_empty());
    }

    #[test]
    fn causal_closure_diamond_no_duplicates() {
        // Diamond: root -> a, root -> b, a + b -> merge
        let mut store = ThreadedMessageStore::new();
        store.append(
            hash("root"),
            thread("t1"),
            simple_msg("tell", "start", Some(CausedBy::Begin)),
        );
        store.append(
            hash("a"),
            thread("t1"),
            simple_msg("reply", "a", Some(CausedBy::Single("root".into()))),
        );
        store.append(
            hash("b"),
            thread("t1"),
            simple_msg("reply", "b", Some(CausedBy::Single("root".into()))),
        );
        store.append(
            hash("merge"),
            thread("t1"),
            simple_msg(
                "ok",
                "done",
                Some(CausedBy::Multiple(vec!["a".into(), "b".into()])),
            ),
        );
        let cc = store.causal_closure(&hash("merge"), &thread("t1"));
        // No duplicates — root appears once even though reachable via both a and b
        assert_eq!(cc.len(), 4);
        let mut sorted = cc.clone();
        sorted.sort();
        sorted.dedup();
        assert_eq!(sorted.len(), 4);
    }

    // --- G-Set monotonicity (REQ-300) ---

    #[test]
    fn append_is_monotonic_store_only_grows() {
        let mut store = ThreadedMessageStore::new();
        store.append(
            hash("h1"),
            thread("t1"),
            simple_msg("tell", "a", Some(CausedBy::Begin)),
        );
        assert!(store.contains(&hash("h1"), &thread("t1")));
        store.append(
            hash("h2"),
            thread("t1"),
            simple_msg("reply", "b", Some(CausedBy::Single("h1".into()))),
        );
        // h1 still present after adding h2
        assert!(store.contains(&hash("h1"), &thread("t1")));
        assert!(store.contains(&hash("h2"), &thread("t1")));
    }

    // --- message without caused_by ---

    #[test]
    fn message_without_caused_by_is_frontier() {
        let mut store = ThreadedMessageStore::new();
        let msg = Message::Simple {
            performative: Performative::Core(crate::message::CorePerformative::Tell),
            recipient: None,
            content: SExpr::Atom(Atom::Str("no causality".to_string())),
            params: Vec::new(),
            thread: None,
            sender: None,
            caused_by: None,
        };
        store.append(hash("h1"), thread("t1"), msg);
        let f = store.frontier(&thread("t1"));
        assert_eq!(f.len(), 1);
        assert_eq!(f[0], &hash("h1"));
    }

    // --- scale test ---

    #[test]
    fn scale_1000_message_chain() {
        let mut store = ThreadedMessageStore::new();
        let t = thread("t1");

        // Build a 1000-message chain
        store.append(
            hash("m0"),
            t.clone(),
            simple_msg("tell", "start", Some(CausedBy::Begin)),
        );
        for i in 1..1000 {
            let h = hash(&alloc::format!("m{}", i));
            let prev = alloc::format!("m{}", i - 1);
            store.append(
                h,
                t.clone(),
                simple_msg("reply", "msg", Some(CausedBy::Single(prev))),
            );
        }

        // Frontier should be only the last message
        let f = store.frontier(&t);
        assert_eq!(f.len(), 1);
        assert_eq!(f[0], &hash("m999"));

        // Causal closure of last message should be all 1000 messages
        let cc = store.causal_closure(&hash("m999"), &t);
        assert_eq!(cc.len(), 1000);

        // Causal closure of first message should be just itself
        let cc0 = store.causal_closure(&hash("m0"), &t);
        assert_eq!(cc0.len(), 1);
    }

    // =========================================================================
    // CausalClosureBundle tests (TEST-311, TEST-212)
    // =========================================================================

    // --- extract tests ---

    #[test]
    fn bundle_extract_single_begin_message() {
        let mut store = ThreadedMessageStore::new();
        let t = thread("t1");
        store.append(
            hash("h1"),
            t.clone(),
            simple_msg("tell", "start", Some(CausedBy::Begin)),
        );

        let bundle = CausalClosureBundle::extract(&hash("h1"), &t, &store).unwrap();
        assert_eq!(bundle.target, hash("h1"));
        assert_eq!(bundle.thread, t);
        assert_eq!(bundle.len(), 1);
        assert_eq!(bundle.messages[0].0, hash("h1"));
    }

    #[test]
    fn bundle_extract_chain_topological_order() {
        let mut store = ThreadedMessageStore::new();
        let t = thread("t1");
        store.append(
            hash("h1"),
            t.clone(),
            simple_msg("tell", "start", Some(CausedBy::Begin)),
        );
        store.append(
            hash("h2"),
            t.clone(),
            simple_msg("reply", "mid", Some(CausedBy::Single("h1".into()))),
        );
        store.append(
            hash("h3"),
            t.clone(),
            simple_msg("ok", "end", Some(CausedBy::Single("h2".into()))),
        );

        let bundle = CausalClosureBundle::extract(&hash("h3"), &t, &store).unwrap();
        assert_eq!(bundle.len(), 3);

        // Topological order: predecessors before successors
        let hashes: Vec<&ContentHash> = bundle.hashes();
        let pos_h1 = hashes.iter().position(|h| **h == hash("h1")).unwrap();
        let pos_h2 = hashes.iter().position(|h| **h == hash("h2")).unwrap();
        let pos_h3 = hashes.iter().position(|h| **h == hash("h3")).unwrap();
        assert!(pos_h1 < pos_h2);
        assert!(pos_h2 < pos_h3);
    }

    #[test]
    fn bundle_extract_diamond_dag() {
        let mut store = ThreadedMessageStore::new();
        let t = thread("t1");
        store.append(
            hash("root"),
            t.clone(),
            simple_msg("tell", "start", Some(CausedBy::Begin)),
        );
        store.append(
            hash("a"),
            t.clone(),
            simple_msg("reply", "a", Some(CausedBy::Single("root".into()))),
        );
        store.append(
            hash("b"),
            t.clone(),
            simple_msg("reply", "b", Some(CausedBy::Single("root".into()))),
        );
        store.append(
            hash("merge"),
            t.clone(),
            simple_msg(
                "ok",
                "done",
                Some(CausedBy::Multiple(vec!["a".into(), "b".into()])),
            ),
        );

        let bundle = CausalClosureBundle::extract(&hash("merge"), &t, &store).unwrap();
        assert_eq!(bundle.len(), 4);

        // root must come before a, b; a and b must come before merge
        let hashes: Vec<&ContentHash> = bundle.hashes();
        let pos = |h: &str| hashes.iter().position(|x| **x == hash(h)).unwrap();
        assert!(pos("root") < pos("a"));
        assert!(pos("root") < pos("b"));
        assert!(pos("a") < pos("merge"));
        assert!(pos("b") < pos("merge"));
    }

    #[test]
    fn bundle_extract_partial_closure() {
        // Extract closure of a mid-chain message — should NOT include later messages
        let mut store = ThreadedMessageStore::new();
        let t = thread("t1");
        store.append(
            hash("h1"),
            t.clone(),
            simple_msg("tell", "start", Some(CausedBy::Begin)),
        );
        store.append(
            hash("h2"),
            t.clone(),
            simple_msg("reply", "mid", Some(CausedBy::Single("h1".into()))),
        );
        store.append(
            hash("h3"),
            t.clone(),
            simple_msg("ok", "end", Some(CausedBy::Single("h2".into()))),
        );

        let bundle = CausalClosureBundle::extract(&hash("h2"), &t, &store).unwrap();
        assert_eq!(bundle.len(), 2);
        let mut sorted_hashes: Vec<ContentHash> = bundle.hashes().into_iter().cloned().collect();
        sorted_hashes.sort();
        assert_eq!(sorted_hashes, vec![hash("h1"), hash("h2")]);
    }

    #[test]
    fn bundle_extract_target_not_found() {
        let store = ThreadedMessageStore::new();
        let result = CausalClosureBundle::extract(&hash("nonexistent"), &thread("t1"), &store);
        assert_eq!(result, Err(ClosureError::TargetNotFound));
    }

    #[test]
    fn bundle_extract_wrong_thread() {
        let mut store = ThreadedMessageStore::new();
        store.append(
            hash("h1"),
            thread("t1"),
            simple_msg("tell", "start", Some(CausedBy::Begin)),
        );
        let result = CausalClosureBundle::extract(&hash("h1"), &thread("t2"), &store);
        assert_eq!(result, Err(ClosureError::TargetNotFound));
    }

    // --- verify_completeness tests ---

    #[test]
    fn bundle_verify_completeness_valid() {
        let mut store = ThreadedMessageStore::new();
        let t = thread("t1");
        store.append(
            hash("h1"),
            t.clone(),
            simple_msg("tell", "start", Some(CausedBy::Begin)),
        );
        store.append(
            hash("h2"),
            t.clone(),
            simple_msg("reply", "done", Some(CausedBy::Single("h1".into()))),
        );

        let bundle = CausalClosureBundle::extract(&hash("h2"), &t, &store).unwrap();
        assert!(bundle.verify_completeness().is_ok());
    }

    #[test]
    fn bundle_verify_completeness_dangling_reference() {
        let t = thread("t1");
        // Manually construct a bundle with a dangling reference
        let bundle = CausalClosureBundle {
            target: hash("h2"),
            thread: t,
            messages: vec![(
                hash("h2"),
                simple_msg("reply", "done", Some(CausedBy::Single("missing".into()))),
            )],
        };

        let result = bundle.verify_completeness();
        assert!(result.is_err());
        let errors = result.unwrap_err();
        assert_eq!(errors.len(), 1);
        assert!(
            matches!(&errors[0], BundleVerificationError::DanglingReference { caused_by } if caused_by == "missing")
        );
    }

    // --- verify_hashes tests ---

    #[test]
    fn bundle_verify_hashes_matching() {
        let mut store = ThreadedMessageStore::new();
        let t = thread("t1");
        store.append(
            hash("h1"),
            t.clone(),
            simple_msg("tell", "start", Some(CausedBy::Begin)),
        );

        let bundle = CausalClosureBundle::extract(&hash("h1"), &t, &store).unwrap();
        // Identity hasher — hashes match
        let result = bundle.verify_hashes(|_| hash("h1"));
        assert!(result.is_ok());
    }

    #[test]
    fn bundle_verify_hashes_mismatch() {
        let mut store = ThreadedMessageStore::new();
        let t = thread("t1");
        store.append(
            hash("h1"),
            t.clone(),
            simple_msg("tell", "start", Some(CausedBy::Begin)),
        );

        let bundle = CausalClosureBundle::extract(&hash("h1"), &t, &store).unwrap();
        // Hasher that returns wrong hash
        let result = bundle.verify_hashes(|_| hash("wrong"));
        assert!(result.is_err());
        let errors = result.unwrap_err();
        assert!(matches!(
            &errors[0],
            BundleVerificationError::HashMismatch { expected, computed, .. }
            if expected.0 == "h1" && computed.0 == "wrong"
        ));
    }

    // --- verify_causal tests ---

    #[test]
    fn bundle_verify_causal_no_protocol_steps() {
        use crate::protocol::CausalProtocol;
        use alloc::collections::BTreeMap;

        let mut store = ThreadedMessageStore::new();
        let t = thread("t1");
        store.append(
            hash("h1"),
            t.clone(),
            simple_msg("tell", "start", Some(CausedBy::Begin)),
        );
        store.append(
            hash("h2"),
            t.clone(),
            simple_msg("reply", "done", Some(CausedBy::Single("h1".into()))),
        );

        let bundle = CausalClosureBundle::extract(&hash("h2"), &t, &store).unwrap();
        let empty_protocol = CausalProtocol {
            steps: BTreeMap::new(),
        };
        assert!(bundle.verify_causal(&empty_protocol).is_ok());
    }

    // --- merge tests ---

    #[test]
    fn bundle_merge_into_empty_store() {
        let mut source_store = ThreadedMessageStore::new();
        let t = thread("t1");
        source_store.append(
            hash("h1"),
            t.clone(),
            simple_msg("tell", "start", Some(CausedBy::Begin)),
        );
        source_store.append(
            hash("h2"),
            t.clone(),
            simple_msg("reply", "done", Some(CausedBy::Single("h1".into()))),
        );

        let bundle = CausalClosureBundle::extract(&hash("h2"), &t, &source_store).unwrap();

        let mut target_store = ThreadedMessageStore::new();
        let result = bundle.merge(&mut target_store);
        assert_eq!(result.added, 2);
        assert_eq!(result.deduplicated, 0);

        // All messages now in target store
        assert!(target_store.contains(&hash("h1"), &t));
        assert!(target_store.contains(&hash("h2"), &t));
    }

    #[test]
    fn bundle_merge_deduplication() {
        let mut store = ThreadedMessageStore::new();
        let t = thread("t1");
        store.append(
            hash("h1"),
            t.clone(),
            simple_msg("tell", "start", Some(CausedBy::Begin)),
        );
        store.append(
            hash("h2"),
            t.clone(),
            simple_msg("reply", "done", Some(CausedBy::Single("h1".into()))),
        );

        let bundle = CausalClosureBundle::extract(&hash("h2"), &t, &store).unwrap();

        // Merge into a store that already has h1
        let mut target_store = ThreadedMessageStore::new();
        target_store.append(
            hash("h1"),
            t.clone(),
            simple_msg("tell", "start", Some(CausedBy::Begin)),
        );

        let result = bundle.merge(&mut target_store);
        assert_eq!(result.added, 1); // only h2 is new
        assert_eq!(result.deduplicated, 1); // h1 was deduplicated
    }

    #[test]
    fn bundle_merge_all_duplicates() {
        let mut store = ThreadedMessageStore::new();
        let t = thread("t1");
        store.append(
            hash("h1"),
            t.clone(),
            simple_msg("tell", "start", Some(CausedBy::Begin)),
        );

        let bundle = CausalClosureBundle::extract(&hash("h1"), &t, &store).unwrap();

        // Merge into same store
        let result = bundle.merge(&mut store);
        assert_eq!(result.added, 0);
        assert_eq!(result.deduplicated, 1);
    }

    // --- to_sexpr tests ---

    #[test]
    fn bundle_to_sexpr_structure() {
        let mut store = ThreadedMessageStore::new();
        let t = thread("t1");
        store.append(
            hash("h1"),
            t.clone(),
            simple_msg("tell", "start", Some(CausedBy::Begin)),
        );

        let bundle = CausalClosureBundle::extract(&hash("h1"), &t, &store).unwrap();
        let sexpr = bundle.to_sexpr();

        // Should be (meta (causal-closure :target ... :thread ... :messages ...))
        if let SExpr::List(outer) = &sexpr {
            assert_eq!(outer.len(), 2);
            assert_eq!(outer[0], SExpr::Atom(Atom::Symbol("meta".into())));
            if let SExpr::List(inner) = &outer[1] {
                assert_eq!(inner[0], SExpr::Atom(Atom::Symbol("causal-closure".into())));
                assert_eq!(inner[1], SExpr::Atom(Atom::Keyword("target".into())));
                assert_eq!(inner[2], SExpr::Atom(Atom::Str("h1".into())));
                assert_eq!(inner[3], SExpr::Atom(Atom::Keyword("thread".into())));
                assert_eq!(inner[4], SExpr::Atom(Atom::Str("t1".into())));
                assert_eq!(inner[5], SExpr::Atom(Atom::Keyword("messages".into())));
                if let SExpr::List(msgs) = &inner[6] {
                    assert_eq!(msgs.len(), 1); // one message
                } else {
                    panic!("expected messages list");
                }
            } else {
                panic!("expected inner list");
            }
        } else {
            panic!("expected outer list");
        }
    }

    // --- round-trip tests (extract -> merge -> compare) ---

    #[test]
    fn bundle_round_trip_extract_merge_matches() {
        let mut store = ThreadedMessageStore::new();
        let t = thread("t1");
        store.append(
            hash("h1"),
            t.clone(),
            simple_msg("tell", "start", Some(CausedBy::Begin)),
        );
        store.append(
            hash("h2"),
            t.clone(),
            simple_msg("reply", "mid", Some(CausedBy::Single("h1".into()))),
        );
        store.append(
            hash("h3"),
            t.clone(),
            simple_msg("ok", "end", Some(CausedBy::Single("h2".into()))),
        );

        let bundle = CausalClosureBundle::extract(&hash("h3"), &t, &store).unwrap();
        assert!(bundle.verify_completeness().is_ok());

        // Merge into empty store
        let mut target = ThreadedMessageStore::new();
        let result = bundle.merge(&mut target);
        assert_eq!(result.added, 3);

        // Target store should have same causal closure
        let cc = target.causal_closure(&hash("h3"), &t);
        assert_eq!(cc.len(), 3);
    }

    #[test]
    fn bundle_round_trip_diamond() {
        let mut store = ThreadedMessageStore::new();
        let t = thread("t1");
        store.append(
            hash("root"),
            t.clone(),
            simple_msg("tell", "start", Some(CausedBy::Begin)),
        );
        store.append(
            hash("a"),
            t.clone(),
            simple_msg("reply", "a", Some(CausedBy::Single("root".into()))),
        );
        store.append(
            hash("b"),
            t.clone(),
            simple_msg("reply", "b", Some(CausedBy::Single("root".into()))),
        );
        store.append(
            hash("merge"),
            t.clone(),
            simple_msg(
                "ok",
                "done",
                Some(CausedBy::Multiple(vec!["a".into(), "b".into()])),
            ),
        );

        let bundle = CausalClosureBundle::extract(&hash("merge"), &t, &store).unwrap();
        assert!(bundle.verify_completeness().is_ok());

        let mut target = ThreadedMessageStore::new();
        let result = bundle.merge(&mut target);
        assert_eq!(result.added, 4);

        // Verify causal closure matches
        let mut cc = target.causal_closure(&hash("merge"), &t);
        cc.sort();
        assert_eq!(cc, vec![hash("a"), hash("b"), hash("merge"), hash("root")]);

        // Verify frontier
        let f = target.frontier(&t);
        assert_eq!(f.len(), 1);
        assert_eq!(f[0], &hash("merge"));
    }

    // --- Tier 2: partial causal closure verification (REQ-212) ---

    #[test]
    fn tier2_partial_closure_sufficient_for_target() {
        // Build a larger thread, extract closure for a mid-point message,
        // verify the closure is self-contained
        let mut store = ThreadedMessageStore::new();
        let t = thread("t1");
        store.append(
            hash("h1"),
            t.clone(),
            simple_msg("tell", "start", Some(CausedBy::Begin)),
        );
        store.append(
            hash("h2"),
            t.clone(),
            simple_msg("reply", "a", Some(CausedBy::Single("h1".into()))),
        );
        store.append(
            hash("h3"),
            t.clone(),
            simple_msg("reply", "b", Some(CausedBy::Single("h2".into()))),
        );
        // h4 is on a different branch from h1
        store.append(
            hash("h4"),
            t.clone(),
            simple_msg("reply", "c", Some(CausedBy::Single("h1".into()))),
        );

        // Extract closure of h3 — should include h1, h2, h3 but NOT h4
        let bundle = CausalClosureBundle::extract(&hash("h3"), &t, &store).unwrap();
        assert_eq!(bundle.len(), 3);
        let hashes: Vec<ContentHash> = bundle.hashes().into_iter().cloned().collect();
        assert!(hashes.contains(&hash("h1")));
        assert!(hashes.contains(&hash("h2")));
        assert!(hashes.contains(&hash("h3")));
        assert!(!hashes.contains(&hash("h4"))); // unrelated branch excluded
        assert!(bundle.verify_completeness().is_ok());
    }

    // --- Tier 3: full audit verification (REQ-212) ---

    #[test]
    fn tier3_full_audit_detects_hash_mismatch() {
        let t = thread("t1");
        // Construct a bundle where one message has a wrong hash
        let bundle = CausalClosureBundle {
            target: hash("h2"),
            thread: t,
            messages: vec![
                (
                    hash("h1"),
                    simple_msg("tell", "start", Some(CausedBy::Begin)),
                ),
                (
                    hash("h2"),
                    simple_msg("reply", "done", Some(CausedBy::Single("h1".into()))),
                ),
            ],
        };

        // Hasher that always returns "computed-hash" — will mismatch both
        let result = bundle.verify_hashes(|_| hash("computed-hash"));
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().len(), 2);
    }

    #[test]
    fn tier3_full_audit_detects_dangling_refs() {
        let t = thread("t1");
        let bundle = CausalClosureBundle {
            target: hash("h2"),
            thread: t,
            messages: vec![(
                hash("h2"),
                simple_msg("reply", "done", Some(CausedBy::Single("missing".into()))),
            )],
        };

        let result = bundle.verify_completeness();
        assert!(result.is_err());
    }

    #[test]
    fn tier3_full_audit_all_checks_pass() {
        let mut store = ThreadedMessageStore::new();
        let t = thread("t1");
        store.append(
            hash("h1"),
            t.clone(),
            simple_msg("tell", "start", Some(CausedBy::Begin)),
        );
        store.append(
            hash("h2"),
            t.clone(),
            simple_msg("reply", "mid", Some(CausedBy::Single("h1".into()))),
        );
        store.append(
            hash("h3"),
            t.clone(),
            simple_msg("ok", "end", Some(CausedBy::Single("h2".into()))),
        );

        let bundle = CausalClosureBundle::extract(&hash("h3"), &t, &store).unwrap();

        // Identity hasher that maps known hashes
        let result = bundle.verify_full(
            |msg| {
                // Simple identity-like hasher for testing
                match msg.caused_by() {
                    Some(CausedBy::Begin) => hash("h1"),
                    Some(CausedBy::Single(p)) if p == "h1" => hash("h2"),
                    Some(CausedBy::Single(p)) if p == "h2" => hash("h3"),
                    _ => hash("unknown"),
                }
            },
            &CausalProtocol {
                steps: alloc::collections::BTreeMap::new(),
            },
        );
        assert!(result.is_ok());
    }

    // --- len / is_empty ---

    #[test]
    fn bundle_empty_has_correct_len() {
        let bundle = CausalClosureBundle {
            target: hash("h1"),
            thread: thread("t1"),
            messages: vec![],
        };
        assert!(bundle.is_empty());
        assert_eq!(bundle.len(), 0);
    }

    // --- scale test ---

    #[test]
    fn bundle_extract_100_message_chain() {
        let mut store = ThreadedMessageStore::new();
        let t = thread("t1");

        store.append(
            hash("m0"),
            t.clone(),
            simple_msg("tell", "start", Some(CausedBy::Begin)),
        );
        for i in 1..100 {
            let h = hash(&alloc::format!("m{}", i));
            let prev = alloc::format!("m{}", i - 1);
            store.append(
                h,
                t.clone(),
                simple_msg("reply", "msg", Some(CausedBy::Single(prev))),
            );
        }

        let bundle = CausalClosureBundle::extract(&hash("m99"), &t, &store).unwrap();
        assert_eq!(bundle.len(), 100);
        assert!(bundle.verify_completeness().is_ok());

        // Verify topological order: m0 before m1 before ... before m99
        let hashes: Vec<&ContentHash> = bundle.hashes();
        for i in 0..99 {
            let pos_i = hashes
                .iter()
                .position(|h| **h == hash(&alloc::format!("m{}", i)))
                .unwrap();
            let pos_next = hashes
                .iter()
                .position(|h| **h == hash(&alloc::format!("m{}", i + 1)))
                .unwrap();
            assert!(pos_i < pos_next, "m{} should come before m{}", i, i + 1);
        }

        // Round-trip merge
        let mut target = ThreadedMessageStore::new();
        let result = bundle.merge(&mut target);
        assert_eq!(result.added, 100);
        assert_eq!(result.deduplicated, 0);
    }

    // =========================================================================
    // SPEC-015 REQ-702: envelope shelf (append_envelope / envelope_in_thread)
    // =========================================================================

    use crate::attest::{sign_attestation_v2, AttestationHeader};
    use crate::keyid::KeyId;
    use alloc::collections::BTreeSet;

    /// Data-dependent test signer (as in `attest.rs`): any change to the
    /// authenticated fields kills the signature.
    struct TestSigner {
        secret: &'static [u8],
    }

    impl Signer for TestSigner {
        fn sign(&self, data: &[u8]) -> Vec<u8> {
            use sha2::{Digest, Sha256};
            let mut h = Sha256::new();
            h.update(self.secret);
            h.update(data);
            h.finalize().to_vec()
        }
        fn verify(&self, data: &[u8], sig: &[u8]) -> bool {
            self.sign(data) == sig
        }
    }

    const SIGNER: TestSigner = TestSigner { secret: b"alice" };

    fn env(hash_s: &str, perf: &str, thread_name: &str) -> RedactedEnvelope {
        let mut to = BTreeSet::new();
        to.insert(KeyId::parse("@bob").unwrap());
        let header = AttestationHeader {
            content_hash: hash_s.into(),
            performative: perf.into(),
            from: KeyId::parse("@alice").unwrap(),
            to,
            thread: thread_name.into(),
            caused_by: Some(CausedBy::Begin),
        };
        let signature = sign_attestation_v2(&SIGNER, &header).unwrap();
        RedactedEnvelope { header, signature }
    }

    /// REQ-702: acceptance places the envelope in the thread its
    /// *authenticated* thread field names — no caller-chosen thread exists.
    #[test]
    fn envelope_is_placed_by_its_authenticated_thread() {
        let mut store = ThreadedMessageStore::new();
        assert_eq!(store.append_envelope(env("h1", "offer", "t1"), &SIGNER), Ok(true));
        assert!(store.envelope_in_thread(&hash("h1"), &thread("t1")).is_some());
        // Invisible from any other thread.
        assert!(store.envelope_in_thread(&hash("h1"), &thread("t2")).is_none());
        // …and the message paths are untouched: no phantom full message.
        assert!(store.lookup_in_thread(&hash("h1"), &thread("t1")).is_none());
        assert!(!store.contains(&hash("h1"), &thread("t1")));
    }

    /// REQ-702: cross-thread injection of a genuine envelope is a
    /// *signature* failure — relabelling the thread breaks the attestation
    /// and the envelope is never stored.
    #[test]
    fn relabelled_envelope_is_a_signature_failure_and_not_stored() {
        let mut store = ThreadedMessageStore::new();
        let mut e = env("h1", "offer", "t1");
        e.header.thread = String::from("t2"); // inject into another thread
        assert_eq!(
            store.append_envelope(e, &SIGNER),
            Err(crate::attest::AttestError::InvalidSignature)
        );
        assert!(store.envelope_in_thread(&hash("h1"), &thread("t1")).is_none());
        assert!(store.envelope_in_thread(&hash("h1"), &thread("t2")).is_none());
    }

    #[test]
    fn envelope_shelf_deduplicates_by_content_hash() {
        let mut store = ThreadedMessageStore::new();
        assert_eq!(store.append_envelope(env("h1", "offer", "t1"), &SIGNER), Ok(true));
        assert_eq!(store.append_envelope(env("h1", "offer", "t1"), &SIGNER), Ok(false));
    }

    /// The trait's default lookup returns `None`: a pre-SPEC-015 store
    /// keeps its exact v1 behaviour without touching envelope code.
    #[test]
    fn default_envelope_lookup_is_none() {
        struct NullStore;
        impl MessageStore for NullStore {
            fn lookup(&self, _: &ContentHash) -> Option<&Message> {
                None
            }
            fn lookup_in_thread(&self, _: &ContentHash, _: &ThreadId) -> Option<&Message> {
                None
            }
            fn contains(&self, _: &ContentHash, _: &ThreadId) -> bool {
                false
            }
            fn append(&mut self, _: ContentHash, _: ThreadId, _: Message) -> bool {
                false
            }
            fn frontier(&self, _: &ThreadId) -> Vec<&ContentHash> {
                Vec::new()
            }
            fn causal_closure(&self, _: &ContentHash, _: &ThreadId) -> Vec<ContentHash> {
                Vec::new()
            }
        }
        assert!(NullStore
            .envelope_in_thread(&hash("h1"), &thread("t1"))
            .is_none());
        // The opened-shelf lookup is likewise a default-None (SPEC-017).
        assert!(NullStore
            .opened_in_thread(&hash("h1"), &thread("t1"))
            .is_none());
    }

    // =========================================================================
    // SPEC-017 REQ-813: opened-envelope shelf (append_opened / opened_in_thread)
    // =========================================================================

    use crate::envelope::{build_opened, OpenedError, HEADER_FIELDS};
    use crate::keyid::SignatureSuite;
    // `Performative` is already imported by the test module above.
    use crate::message::Recipients;
    use crate::typed_addr::{typed_root, FieldId};

    /// A predecessor message typed `perf`, sender `@alice`, thread
    /// `thread_name`; returns its opened envelope and its typed root.
    fn opened(perf: &str, thread_name: &str) -> (crate::envelope::OpenedEnvelope, String) {
        let mut to = alloc::collections::BTreeSet::new();
        to.insert("@bob".to_string());
        let m = Message::Simple {
            performative: Performative::Custom(perf.into()),
            recipient: Some(Recipients::Set(to)),
            content: SExpr::Atom(Atom::Str("secret".into())),
            params: Vec::new(),
            thread: Some(thread_name.into()),
            sender: Some("@alice".into()),
            caused_by: Some(CausedBy::Begin),
        };
        let root = typed_root(&m);
        let env = build_opened(&m, &HEADER_FIELDS, &SignatureSuite::Ed25519, &SIGNER).unwrap();
        (env, root)
    }

    /// REQ-813: acceptance places an opened envelope in the thread its
    /// *authenticated* Thread opening names — no caller-chosen thread.
    #[test]
    fn opened_envelope_is_placed_by_its_authenticated_thread() {
        let mut store = ThreadedMessageStore::new();
        let (env, root) = opened("offer", "t1");
        assert_eq!(store.append_opened(env, &SIGNER), Ok(true));
        assert!(store.opened_in_thread(&hash(&root), &thread("t1")).is_some());
        // Invisible from any other thread, and no phantom full message.
        assert!(store.opened_in_thread(&hash(&root), &thread("t2")).is_none());
        assert!(store.lookup_in_thread(&hash(&root), &thread("t1")).is_none());
    }

    /// REQ-813: relabelling the Thread opening to inject into another thread
    /// makes that opening fail against the signed root — the envelope is
    /// never stored (fail closed at the signature/opening, not a policy).
    #[test]
    fn relabelled_opened_envelope_is_a_signature_failure_and_not_stored() {
        let mut store = ThreadedMessageStore::new();
        let (mut env, root) = opened("offer", "t1");
        for op in &mut env.openings {
            if op.field == FieldId::Thread {
                op.value = SExpr::List(vec![SExpr::Atom(Atom::Str("t2".to_string()))]);
            }
        }
        assert_eq!(
            store.append_opened(env, &SIGNER),
            Err(OpenedError::OpeningFailed {
                field: FieldId::Thread
            })
        );
        assert!(store.opened_in_thread(&hash(&root), &thread("t1")).is_none());
        assert!(store.opened_in_thread(&hash(&root), &thread("t2")).is_none());
    }

    #[test]
    fn opened_shelf_deduplicates_by_root() {
        let mut store = ThreadedMessageStore::new();
        let (env1, _) = opened("offer", "t1");
        let (env2, _) = opened("offer", "t1");
        assert_eq!(store.append_opened(env1, &SIGNER), Ok(true));
        assert_eq!(store.append_opened(env2, &SIGNER), Ok(false));
    }
}
