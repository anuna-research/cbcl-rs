//! Message store with G-Set CRDT semantics (REQ-300, REQ-309, ADR-008).
//!
//! Provides [`HashIndex`] for O(1) lookup and [`ThreadedMessageStore`] for
//! append-only, deduplicated, per-thread message storage.
//!
//! The store is a join-semilattice (REQ-300): messages are the elements,
//! `:caused-by` links form the covers relation (REQ-301), fan-in is join,
//! and causal closure computes the principal ideal.

#![forbid(unsafe_code)]

use alloc::string::String;
use alloc::vec::Vec;
use crate::message::{CausedBy, Message};
use hashbrown::{HashMap, HashSet};

/// Content-addressed hash identifying a message (SHA-256 hex string).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ContentHash(pub String);

/// Thread identifier scoping causal chains (ADR-008).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ThreadId(pub String);

/// Thread-scoped hash index for O(1) message lookup (REQ-309).
///
/// Each entry maps a [`ContentHash`] to its owning [`ThreadId`] and position
/// index within that thread. Lookups enforce thread isolation per ADR-008:
/// a lookup for hash H in thread T returns `None` if H belongs to thread T'.
///
/// Memory budget: <= 64 bytes per entry (NFR-303).
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
        self.map.get(hash).and_then(|(t, idx)| {
            if t == thread {
                Some(*idx)
            } else {
                None
            }
        })
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
}

/// Per-thread append-only message store with G-Set CRDT semantics (REQ-300).
///
/// Uses [`HashIndex`] for O(1) lookup (REQ-309) and deduplication (REQ-310).
/// Maintains a frontier set per thread for efficient leaf queries.
pub struct ThreadedMessageStore {
    /// Per-thread message storage: `ThreadId -> Vec<(ContentHash, Message)>`.
    threads: HashMap<ThreadId, Vec<(ContentHash, Message)>>,
    /// Global hash index for O(1) lookup.
    index: HashIndex,
    /// Per-thread set of hashes referenced by some message's `:caused-by`.
    referenced: HashMap<ThreadId, HashSet<ContentHash>>,
}

impl ThreadedMessageStore {
    /// Creates an empty message store.
    pub fn new() -> Self {
        Self {
            threads: HashMap::new(),
            index: HashIndex::new(),
            referenced: HashMap::new(),
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
        self.threads.get(thread).and_then(|msgs| msgs.get(*idx).map(|(_, m)| m))
    }

    fn lookup_in_thread(&self, hash: &ContentHash, thread: &ThreadId) -> Option<&Message> {
        let idx = self.index.lookup(hash, thread)?;
        self.threads.get(thread).and_then(|msgs| msgs.get(idx).map(|(_, m)| m))
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
        assert_eq!(
            idx.lookup(&hash("t5-m500"), &threads[5]),
            Some(500)
        );
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
                crate::message::CorePerformative::parse(perf).unwrap_or(crate::message::CorePerformative::Tell),
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
        store.append(hash("h1"), thread("t1"), simple_msg("tell", "start", Some(CausedBy::Begin)));
        let f = store.frontier(&thread("t1"));
        assert_eq!(f.len(), 1);
        assert_eq!(f[0], &hash("h1"));
    }

    #[test]
    fn frontier_chain_only_leaf_is_frontier() {
        let mut store = ThreadedMessageStore::new();
        store.append(hash("h1"), thread("t1"), simple_msg("tell", "start", Some(CausedBy::Begin)));
        store.append(hash("h2"), thread("t1"), simple_msg("reply", "ack", Some(CausedBy::Single("h1".into()))));
        let f = store.frontier(&thread("t1"));
        assert_eq!(f.len(), 1);
        assert_eq!(f[0], &hash("h2"));
    }

    #[test]
    fn frontier_branching_two_leaves() {
        let mut store = ThreadedMessageStore::new();
        store.append(hash("root"), thread("t1"), simple_msg("tell", "start", Some(CausedBy::Begin)));
        store.append(hash("b1"), thread("t1"), simple_msg("reply", "branch1", Some(CausedBy::Single("root".into()))));
        store.append(hash("b2"), thread("t1"), simple_msg("reply", "branch2", Some(CausedBy::Single("root".into()))));
        let mut f: Vec<_> = store.frontier(&thread("t1")).into_iter().cloned().collect();
        f.sort();
        assert_eq!(f, vec![hash("b1"), hash("b2")]);
    }

    #[test]
    fn frontier_fan_in_merge_removes_predecessors() {
        let mut store = ThreadedMessageStore::new();
        store.append(hash("root"), thread("t1"), simple_msg("tell", "start", Some(CausedBy::Begin)));
        store.append(hash("b1"), thread("t1"), simple_msg("reply", "a", Some(CausedBy::Single("root".into()))));
        store.append(hash("b2"), thread("t1"), simple_msg("reply", "b", Some(CausedBy::Single("root".into()))));
        // Merge message references both branches
        store.append(hash("merge"), thread("t1"), simple_msg("ok", "done", Some(CausedBy::Multiple(vec!["b1".into(), "b2".into()]))));
        let f = store.frontier(&thread("t1"));
        assert_eq!(f.len(), 1);
        assert_eq!(f[0], &hash("merge"));
    }

    #[test]
    fn frontier_separate_threads_independent() {
        let mut store = ThreadedMessageStore::new();
        store.append(hash("h1"), thread("t1"), simple_msg("tell", "a", Some(CausedBy::Begin)));
        store.append(hash("h2"), thread("t2"), simple_msg("tell", "b", Some(CausedBy::Begin)));
        assert_eq!(store.frontier(&thread("t1")).len(), 1);
        assert_eq!(store.frontier(&thread("t2")).len(), 1);
    }

    // --- causal_closure tests (principal ideal) ---

    #[test]
    fn causal_closure_begin_message_is_singleton() {
        let mut store = ThreadedMessageStore::new();
        store.append(hash("h1"), thread("t1"), simple_msg("tell", "start", Some(CausedBy::Begin)));
        let cc = store.causal_closure(&hash("h1"), &thread("t1"));
        assert_eq!(cc.len(), 1);
        assert_eq!(cc[0], hash("h1"));
    }

    #[test]
    fn causal_closure_chain_returns_all_ancestors() {
        let mut store = ThreadedMessageStore::new();
        store.append(hash("h1"), thread("t1"), simple_msg("tell", "start", Some(CausedBy::Begin)));
        store.append(hash("h2"), thread("t1"), simple_msg("reply", "mid", Some(CausedBy::Single("h1".into()))));
        store.append(hash("h3"), thread("t1"), simple_msg("ok", "end", Some(CausedBy::Single("h2".into()))));
        let mut cc = store.causal_closure(&hash("h3"), &thread("t1"));
        cc.sort();
        assert_eq!(cc, vec![hash("h1"), hash("h2"), hash("h3")]);
    }

    #[test]
    fn causal_closure_fan_in_includes_all_branches() {
        let mut store = ThreadedMessageStore::new();
        store.append(hash("root"), thread("t1"), simple_msg("tell", "start", Some(CausedBy::Begin)));
        store.append(hash("b1"), thread("t1"), simple_msg("reply", "a", Some(CausedBy::Single("root".into()))));
        store.append(hash("b2"), thread("t1"), simple_msg("reply", "b", Some(CausedBy::Single("root".into()))));
        store.append(hash("merge"), thread("t1"), simple_msg("ok", "done", Some(CausedBy::Multiple(vec!["b1".into(), "b2".into()]))));
        let mut cc = store.causal_closure(&hash("merge"), &thread("t1"));
        cc.sort();
        assert_eq!(cc, vec![hash("b1"), hash("b2"), hash("merge"), hash("root")]);
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
        store.append(hash("h1"), thread("t1"), simple_msg("tell", "start", Some(CausedBy::Begin)));
        let cc = store.causal_closure(&hash("h1"), &thread("t2"));
        assert!(cc.is_empty());
    }

    #[test]
    fn causal_closure_diamond_no_duplicates() {
        // Diamond: root -> a, root -> b, a + b -> merge
        let mut store = ThreadedMessageStore::new();
        store.append(hash("root"), thread("t1"), simple_msg("tell", "start", Some(CausedBy::Begin)));
        store.append(hash("a"), thread("t1"), simple_msg("reply", "a", Some(CausedBy::Single("root".into()))));
        store.append(hash("b"), thread("t1"), simple_msg("reply", "b", Some(CausedBy::Single("root".into()))));
        store.append(hash("merge"), thread("t1"), simple_msg("ok", "done", Some(CausedBy::Multiple(vec!["a".into(), "b".into()]))));
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
        store.append(hash("h1"), thread("t1"), simple_msg("tell", "a", Some(CausedBy::Begin)));
        assert!(store.contains(&hash("h1"), &thread("t1")));
        store.append(hash("h2"), thread("t1"), simple_msg("reply", "b", Some(CausedBy::Single("h1".into()))));
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
}
