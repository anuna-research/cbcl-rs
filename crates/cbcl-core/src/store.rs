//! Hash index for O(1) message lookup with thread-scoped isolation (REQ-309, ADR-008).
//!
//! Provides [`HashIndex`], a `HashMap<ContentHash, (ThreadId, usize)>` that enforces
//! thread isolation: lookups for hash H in thread T never return entries from thread T'.

#![forbid(unsafe_code)]

use alloc::string::String;
use hashbrown::HashMap;

/// Content-addressed hash identifying a message (SHA-256 hex string).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ContentHash(pub String);

/// Thread identifier scoping causal chains (ADR-008).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
}
