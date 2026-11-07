//! Persistent ordered native evidence; path copies never copy message bodies.
use crate::{certificate::SignedMessage, codec, hash, Hash};
#[cfg(feature = "std")]
use crate::{Error, Result};
use alloc::{string::String, sync::Arc, vec::Vec};
use core::fmt;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

pub type Key = (String, Hash);
type Link = Option<Arc<Node>>;
const BLOB: &[u8] = b"cbcl/checkpoint/blob/v1";
const WIRE: &[u8] = b"cbcl/checkpoint/evidence/v1";
const MAGIC: &[u8] = b"cbcl/checkpoint/evidence-node/v2";
const MAX_NODES: usize = 1_000_000;
const MAX_DEPTH: usize = 64;
const MAX_NODE_BYTES: usize = 1024;
const MAX_MESSAGE_BYTES: usize = 256 * 1024;
#[cfg(feature = "std")]
const MAX_RECOVERY_BYTES: usize = 256 * 1024 * 1024;

struct Entry {
    key: Key,
    value: Arc<SignedMessage>,
    blob: Hash,
    encoded_len: usize,
    key_valid: bool,
}
struct Node {
    entry: Arc<Entry>,
    left: Link,
    right: Link,
    height: usize,
    size: usize,
    recovery_bytes: usize,
    recoverable: bool,
    #[cfg_attr(not(feature = "std"), allow(dead_code))]
    bytes: Vec<u8>,
    blob: Hash,
}
fn height(n: &Link) -> usize {
    n.as_ref().map_or(0, |n| n.height)
}
fn size(n: &Link) -> usize {
    n.as_ref().map_or(0, |n| n.size)
}
fn node_hash(n: &Link) -> Option<Hash> {
    n.as_ref().map(|n| n.blob)
}
fn put_link(bytes: &mut Vec<u8>, n: Option<Hash>) {
    bytes.push(u8::from(n.is_some()));
    if let Some(h) = n {
        bytes.extend_from_slice(&h);
    }
}
fn make(entry: Arc<Entry>, left: Link, right: Link) -> Arc<Node> {
    let height = 1 + height(&left).max(height(&right));
    let size = 1usize
        .saturating_add(size(&left))
        .saturating_add(size(&right));
    let mut bytes = Vec::new();
    bytes.extend_from_slice(MAGIC);
    codec::put_string(&mut bytes, &entry.key.0);
    bytes.extend_from_slice(&entry.key.1);
    bytes.extend_from_slice(&entry.blob);
    put_link(&mut bytes, node_hash(&left));
    put_link(&mut bytes, node_hash(&right));
    codec::put_u32(&mut bytes, height);
    codec::put_u32(&mut bytes, size);
    let recovery_bytes = bytes
        .len()
        .saturating_add(8)
        .saturating_add(entry.encoded_len)
        .saturating_add(left.as_ref().map_or(0, |n| n.recovery_bytes))
        .saturating_add(right.as_ref().map_or(0, |n| n.recovery_bytes));
    bytes.extend_from_slice(&(recovery_bytes as u64).to_be_bytes());
    let recoverable = entry.key_valid
        && entry.key.0.len() <= 128
        && entry.encoded_len <= MAX_MESSAGE_BYTES
        && bytes.len() <= MAX_NODE_BYTES
        && height <= MAX_DEPTH
        && left.as_ref().map_or(true, |n| n.recoverable)
        && right.as_ref().map_or(true, |n| n.recoverable);
    let blob = hash(BLOB, &bytes);
    Arc::new(Node {
        entry,
        left,
        right,
        height,
        size,
        recovery_bytes,
        recoverable,
        bytes,
        blob,
    })
}
fn rotate_left(n: Arc<Node>) -> Arc<Node> {
    let r = n.right.as_ref().expect("AVL right child");
    make(
        r.entry.clone(),
        Some(make(n.entry.clone(), n.left.clone(), r.left.clone())),
        r.right.clone(),
    )
}
fn rotate_right(n: Arc<Node>) -> Arc<Node> {
    let l = n.left.as_ref().expect("AVL left child");
    make(
        l.entry.clone(),
        l.left.clone(),
        Some(make(n.entry.clone(), l.right.clone(), n.right.clone())),
    )
}
fn balance(mut n: Arc<Node>) -> Arc<Node> {
    if height(&n.left) > height(&n.right) + 1 {
        let l = n.left.as_ref().expect("AVL left child");
        if height(&l.right) > height(&l.left) {
            n = make(
                n.entry.clone(),
                Some(rotate_left(l.clone())),
                n.right.clone(),
            );
        }
        rotate_right(n)
    } else if height(&n.right) > height(&n.left) + 1 {
        let r = n.right.as_ref().expect("AVL right child");
        if height(&r.left) > height(&r.right) {
            n = make(
                n.entry.clone(),
                n.left.clone(),
                Some(rotate_right(r.clone())),
            );
        }
        rotate_left(n)
    } else {
        n
    }
}
fn insert(n: &Link, entry: Arc<Entry>) -> (Arc<Node>, Option<Arc<Entry>>) {
    let Some(n) = n else {
        return (make(entry, None, None), None);
    };
    use core::cmp::Ordering::*;
    match entry.key.cmp(&n.entry.key) {
        Less => {
            let (l, old) = insert(&n.left, entry);
            if n.left
                .as_ref()
                .is_some_and(|before| Arc::ptr_eq(before, &l))
            {
                return (n.clone(), old);
            }
            (
                balance(make(n.entry.clone(), Some(l), n.right.clone())),
                old,
            )
        }
        Greater => {
            let (r, old) = insert(&n.right, entry);
            if n.right
                .as_ref()
                .is_some_and(|before| Arc::ptr_eq(before, &r))
            {
                return (n.clone(), old);
            }
            (balance(make(n.entry.clone(), n.left.clone(), Some(r))), old)
        }
        Equal => (
            if entry.blob == n.entry.blob {
                n.clone()
            } else {
                make(entry, n.left.clone(), n.right.clone())
            },
            Some(n.entry.clone()),
        ),
    }
}

/// O(1) clones, worst-case O(log N) lookup/insertion. Identity variants coexist.
#[derive(Clone, Default)]
pub struct Evidence {
    root: Link,
}
impl Evidence {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn len(&self) -> usize {
        size(&self.root)
    }
    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }
    pub fn get(&self, key: &Key) -> Option<&SignedMessage> {
        let mut n = self.root.as_deref();
        while let Some(node) = n {
            match key.cmp(&node.entry.key) {
                core::cmp::Ordering::Less => n = node.left.as_deref(),
                core::cmp::Ordering::Greater => n = node.right.as_deref(),
                core::cmp::Ordering::Equal => return Some(&node.entry.value),
            }
        }
        None
    }
    pub fn insert(&mut self, key: Key, value: SignedMessage) -> Option<SignedMessage> {
        // Only the incoming body is encoded. Copies of ancestor nodes reuse Entry.
        let bytes = value.encode();
        let encoded_len = bytes.len();
        let blob = hash(BLOB, &bytes);
        let key_valid = value.id().is_ok_and(|id| id == key.0) && hash(WIRE, &bytes) == key.1;
        let entry = Arc::new(Entry {
            key,
            value: Arc::new(value),
            blob,
            encoded_len,
            key_valid,
        });
        let (root, old) = insert(&self.root, entry);
        self.root = Some(root);
        // An owned replacement return requires a body copy when old versions exist.
        old.map(|old| match Arc::try_unwrap(old) {
            Ok(entry) => Arc::try_unwrap(entry.value).unwrap_or_else(|value| (*value).clone()),
            Err(entry) => (*entry.value).clone(),
        })
    }
    pub fn iter(&self) -> Iter<'_> {
        Iter::new(&self.root)
    }
    /// `self` is the small candidate delta, never the historical archive.
    pub fn retaining(&self, previous: &Evidence) -> Evidence {
        let mut out = previous.clone();
        for entry in Entries::new(&self.root) {
            out.root = Some(insert(&out.root, entry.clone()).0);
        }
        out
    }
    #[cfg(feature = "std")]
    pub fn persist(&self, cache: &crate::host::Cache) -> Result<Option<Hash>> {
        self.persist_counted(cache, &mut PersistWork::default())
    }
    #[cfg(feature = "std")]
    pub fn persist_counted(
        &self,
        cache: &crate::host::Cache,
        work: &mut PersistWork,
    ) -> Result<Option<Hash>> {
        // Check the entire generation before the trusted-root shortcut. Cached
        // totals include every node record and value read during cold recovery.
        if self.root.as_ref().is_some_and(|n| {
            n.size > MAX_NODES || n.recovery_bytes > MAX_RECOVERY_BYTES || !n.recoverable
        }) {
            return Err(Error::Budget);
        }
        fn save(n: &Link, cache: &crate::host::Cache, w: &mut PersistWork) -> Result<()> {
            let Some(n) = n else {
                return Ok(());
            };
            w.trusted_checks += 1;
            if cache.contains_trusted(n.blob)? {
                return Ok(());
            }
            save(&n.left, cache, w)?;
            save(&n.right, cache, w)?;
            w.trusted_checks += 1;
            if !cache.contains_trusted(n.entry.blob)? {
                let bytes = n.entry.value.encode();
                if bytes.len() > MAX_MESSAGE_BYTES {
                    return Err(Error::Budget);
                }
                if cache.put(&bytes)? != n.entry.blob {
                    return Err(Error::Invalid("evidence value hash"));
                }
                w.value_encodes += 1;
                w.value_bytes += bytes.len();
            }
            if n.bytes.len() > MAX_NODE_BYTES {
                return Err(Error::Budget);
            }
            if cache.put(&n.bytes)? != n.blob {
                return Err(Error::Invalid("evidence node hash"));
            }
            w.new_nodes += 1;
            w.node_bytes += n.bytes.len();
            Ok(())
        }
        save(&self.root, cache, work)?;
        Ok(node_hash(&self.root))
    }
    #[cfg(feature = "std")]
    pub fn recover(
        cache: &crate::host::Cache,
        root: Option<Hash>,
        keys: &dyn crate::certificate::KeyVerifier,
    ) -> Result<Self> {
        recover(cache, root, keys)
    }
}
impl Extend<(Key, SignedMessage)> for Evidence {
    fn extend<T: IntoIterator<Item = (Key, SignedMessage)>>(&mut self, rows: T) {
        for (key, value) in rows {
            let bytes = value.encode();
            let encoded_len = bytes.len();
            let blob = hash(BLOB, &bytes);
            let key_valid = value.id().is_ok_and(|id| id == key.0) && hash(WIRE, &bytes) == key.1;
            let entry = Arc::new(Entry {
                key,
                value: Arc::new(value),
                blob,
                encoded_len,
                key_valid,
            });
            self.root = Some(insert(&self.root, entry).0);
        }
    }
}
impl FromIterator<(Key, SignedMessage)> for Evidence {
    fn from_iter<T: IntoIterator<Item = (Key, SignedMessage)>>(rows: T) -> Self {
        let mut out = Self::new();
        out.extend(rows);
        out
    }
}
struct Entries<'a> {
    stack: Vec<&'a Node>,
}
impl<'a> Entries<'a> {
    fn new(root: &'a Link) -> Self {
        let mut out = Self { stack: Vec::new() };
        out.push(root);
        out
    }
    fn push(&mut self, root: &'a Link) {
        let mut n = root.as_deref();
        while let Some(node) = n {
            self.stack.push(node);
            n = node.left.as_deref();
        }
    }
}
impl<'a> Iterator for Entries<'a> {
    type Item = &'a Arc<Entry>;
    fn next(&mut self) -> Option<Self::Item> {
        let n = self.stack.pop()?;
        self.push(&n.right);
        Some(&n.entry)
    }
}
pub struct Iter<'a> {
    entries: Entries<'a>,
}
impl<'a> Iter<'a> {
    fn new(root: &'a Link) -> Self {
        Self {
            entries: Entries::new(root),
        }
    }
}
impl<'a> Iterator for Iter<'a> {
    type Item = (&'a Key, &'a SignedMessage);
    fn next(&mut self) -> Option<Self::Item> {
        self.entries.next().map(|e| (&e.key, e.value.as_ref()))
    }
}
impl<'a> IntoIterator for &'a Evidence {
    type Item = (&'a Key, &'a SignedMessage);
    type IntoIter = Iter<'a>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
impl PartialEq for Evidence {
    fn eq(&self, other: &Self) -> bool {
        if self
            .root
            .as_ref()
            .zip(other.root.as_ref())
            .is_some_and(|(a, b)| Arc::ptr_eq(a, b))
        {
            return true;
        }
        self.len() == other.len() && self.iter().eq(other.iter())
    }
}
impl Eq for Evidence {}
impl fmt::Debug for Evidence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}
impl Serialize for Evidence {
    fn serialize<S: Serializer>(&self, s: S) -> core::result::Result<S::Ok, S::Error> {
        use serde::ser::SerializeSeq;
        let mut seq = s.serialize_seq(Some(self.len()))?;
        for row in self {
            seq.serialize_element(&row)?;
        }
        seq.end()
    }
}
impl<'de> Deserialize<'de> for Evidence {
    fn deserialize<D: Deserializer<'de>>(d: D) -> core::result::Result<Self, D::Error> {
        struct Visitor;
        impl<'de> serde::de::Visitor<'de> for Visitor {
            type Value = Evidence;
            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("unique native evidence pairs")
            }
            fn visit_seq<A: serde::de::SeqAccess<'de>>(
                self,
                mut seq: A,
            ) -> core::result::Result<Evidence, A::Error> {
                let mut out = Evidence::new();
                while let Some((key, value)) = seq.next_element::<(Key, SignedMessage)>()? {
                    if out.len() >= MAX_NODES {
                        return Err(serde::de::Error::custom("evidence budget"));
                    }
                    let bytes = value.encode();
                    if bytes.len() > MAX_MESSAGE_BYTES
                        || value.id().map_err(serde::de::Error::custom)? != key.0
                        || hash(WIRE, &bytes) != key.1
                        || out.get(&key).is_some()
                    {
                        return Err(serde::de::Error::custom("invalid evidence identity"));
                    }
                    let entry = Arc::new(Entry {
                        key,
                        value: Arc::new(value),
                        blob: hash(BLOB, &bytes),
                        encoded_len: bytes.len(),
                        key_valid: true, // identity and wire binding checked above
                    });
                    out.root = Some(insert(&out.root, entry).0);
                }
                Ok(out)
            }
        }
        d.deserialize_seq(Visitor)
    }
}

/// Per-call persistence work, excluding metadata-only trusted checks' OS cost.
#[cfg(feature = "std")]
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct PersistWork {
    pub trusted_checks: usize,
    pub new_nodes: usize,
    pub node_bytes: usize,
    pub value_encodes: usize,
    pub value_bytes: usize,
}

/// Cold recovery alone reads/authenticates retained bodies. All limits apply
/// before recursive descent or decoding; both child order and AVL metadata bind.
#[cfg(feature = "std")]
pub fn recover(
    cache: &crate::host::Cache,
    root: Option<Hash>,
    keys: &dyn crate::certificate::KeyVerifier,
) -> Result<Evidence> {
    fn link(r: &mut codec::Reader<'_>) -> Result<Option<Hash>> {
        match r.take(1)?[0] {
            0 => Ok(None),
            1 => Ok(Some(r.hash()?)),
            _ => Err(Error::Invalid("evidence child tag")),
        }
    }
    struct Budget {
        nodes: usize,
        bytes: usize,
    }
    fn load(
        cache: &crate::host::Cache,
        id: Hash,
        keys: &dyn crate::certificate::KeyVerifier,
        low: Option<&Key>,
        high: Option<&Key>,
        depth: usize,
        b: &mut Budget,
    ) -> Result<Arc<Node>> {
        if depth >= MAX_DEPTH || b.nodes >= MAX_NODES {
            return Err(Error::Budget);
        }
        b.nodes += 1;
        let bytes = cache.read_once(id, MAX_NODE_BYTES)?;
        b.bytes = b.bytes.checked_add(bytes.len()).ok_or(Error::Budget)?;
        if b.bytes > MAX_RECOVERY_BYTES {
            return Err(Error::Budget);
        }
        if hash(BLOB, &bytes) != id {
            return Err(Error::Invalid("evidence node blob"));
        }
        let mut r = codec::Reader::new(&bytes, MAX_NODE_BYTES)?;
        if r.take(MAGIC.len())? != MAGIC {
            return Err(Error::Invalid("evidence node version"));
        }
        let key = (r.string(128)?, r.hash()?);
        if low.is_some_and(|l| key <= *l) || high.is_some_and(|h| key >= *h) {
            return Err(Error::Invalid("evidence tree ordering"));
        }
        let value_blob = r.hash()?;
        let left_hash = link(&mut r)?;
        let right_hash = link(&mut r)?;
        let claimed_height = r.count(MAX_DEPTH)?;
        let claimed_size = r.count(MAX_NODES)?;
        let claimed_bytes = u64::from_be_bytes(
            r.take(8)?
                .try_into()
                .map_err(|_| Error::Invalid("evidence byte total"))?,
        );
        if claimed_bytes > MAX_RECOVERY_BYTES as u64 {
            return Err(Error::Budget);
        }
        r.finish()?;
        let mut child = |id, low, high| load(cache, id, keys, low, high, depth + 1, b);
        let left = match left_hash {
            Some(id) => Some(child(id, low, Some(&key))?),
            None => None,
        };
        let right = match right_hash {
            Some(id) => Some(child(id, Some(&key), high)?),
            None => None,
        };
        if height(&left).abs_diff(height(&right)) > 1
            || claimed_height != 1 + height(&left).max(height(&right))
            || claimed_size != 1 + size(&left) + size(&right)
        {
            return Err(Error::Invalid("evidence AVL metadata"));
        }
        let remaining = MAX_RECOVERY_BYTES
            .checked_sub(b.bytes)
            .ok_or(Error::Budget)?;
        let body = cache.read_once(value_blob, MAX_MESSAGE_BYTES.min(remaining))?;
        b.bytes = b.bytes.checked_add(body.len()).ok_or(Error::Budget)?;
        if b.bytes > MAX_RECOVERY_BYTES {
            return Err(Error::Budget);
        }
        if hash(BLOB, &body) != value_blob || hash(WIRE, &body) != key.1 {
            return Err(Error::Invalid("evidence wire blob"));
        }
        let value = SignedMessage::decode(&body)?;
        value.authenticate(keys)?;
        if value.id()? != key.0 {
            return Err(Error::Invalid("evidence native identity"));
        }
        let node = make(
            Arc::new(Entry {
                key,
                value: Arc::new(value),
                blob: value_blob,
                encoded_len: body.len(),
                key_valid: true, // authenticated identity and wire binding checked above
            }),
            left,
            right,
        );
        if node.recovery_bytes as u64 != claimed_bytes
            || !node.recoverable
            || node.bytes != bytes
            || node.blob != id
        {
            return Err(Error::Invalid("noncanonical evidence node"));
        }
        Ok(node)
    }
    let root = match root {
        Some(id) => Some(load(
            cache,
            id,
            keys,
            None,
            None,
            0,
            &mut Budget { nodes: 0, bytes: 0 },
        )?),
        None => None,
    };
    Ok(Evidence { root })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::{parse, Keys};
    fn message(i: usize) -> SignedMessage {
        SignedMessage::sign(
            parse(&alloc::format!(
                "(tell @m1 :value {i} :sender @m0 :thread \"evidence\" :caused-by begin)"
            )),
            "@m0",
            &Keys,
        )
        .unwrap()
    }
    fn key(m: &SignedMessage) -> Key {
        (m.id().unwrap(), hash(WIRE, &m.encode()))
    }
    fn check(n: &Link, low: Option<&Key>, high: Option<&Key>) -> (usize, usize) {
        let Some(n) = n else {
            return (0, 0);
        };
        assert!(low.map_or(true, |l| l < &n.entry.key));
        assert!(high.map_or(true, |h| h > &n.entry.key));
        let (lh, ls) = check(&n.left, low, Some(&n.entry.key));
        let (rh, rs) = check(&n.right, Some(&n.entry.key), high);
        assert!(lh.abs_diff(rh) <= 1);
        assert_eq!(n.height, 1 + lh.max(rh));
        assert_eq!(n.size, 1 + ls + rs);
        (n.height, n.size)
    }
    #[test]
    fn persistent_rotations_retention_and_variants_share_bodies() {
        let rows: Vec<_> = (0..100)
            .map(|i| {
                let m = message(i);
                (key(&m), m)
            })
            .collect();
        let mut ordered = rows.clone();
        ordered.sort_by(|a, b| a.0.cmp(&b.0));
        for input in [
            rows.clone(),
            ordered.clone(),
            ordered.into_iter().rev().collect(),
        ] {
            let mut map = Evidence::new();
            for (key, value) in input {
                map.insert(key, value);
                check(&map.root, None, None);
            }
            let before = map.clone();
            assert!(Arc::ptr_eq(
                before.root.as_ref().unwrap(),
                map.root.as_ref().unwrap()
            ));
            let m = message(200);
            let k = key(&m);
            let mut delta = Evidence::new();
            delta.insert(k.clone(), m);
            let retained = delta.retaining(&map);
            assert_eq!(before, map);
            assert_eq!(retained.len(), 101);
            assert!(map.get(&k).is_none());
            for (key, value) in &map {
                assert!(core::ptr::eq(value, retained.get(key).unwrap()));
            }
            let variant = SignedMessage::sign(
                parse("(lang alternate (tell @m1 :value 0 :sender @m0 :thread \"evidence\" :caused-by begin))"),
                "@m0", &Keys,
            ).unwrap();
            assert_eq!(variant.id().unwrap(), rows[0].0 .0);
            assert_ne!(key(&variant), rows[0].0);
            map.insert(key(&variant), variant);
            assert_eq!(map.len(), 101);
            assert_eq!(before.len(), 100);
        }
    }
    #[cfg(feature = "std")]
    #[test]
    fn persistence_skips_old_subtrees_and_recovers_authenticated_values() {
        let dir = std::env::temp_dir().join(alloc::format!(
            "cbcl-evidence-{}-{:?}",
            std::process::id(),
            std::time::SystemTime::now()
        ));
        let cache = crate::host::Cache::open(&dir).unwrap();
        let mut old = Evidence::new();
        for i in 0..80 {
            let m = message(i);
            old.insert(key(&m), m);
        }
        let root = old.persist(&cache).unwrap();
        let mut work = PersistWork::default();
        assert_eq!(old.persist_counted(&cache, &mut work).unwrap(), root);
        assert_eq!(work.trusted_checks, 1);
        assert_eq!(work.new_nodes + work.value_encodes, 0);
        // Remove a body: metadata-only warm persistence must never read it.
        let entry = Entries::new(&old.root).next().unwrap();
        let body_path = cache.path(entry.blob);
        let saved = std::fs::read(&body_path).unwrap();
        std::fs::remove_file(&body_path).unwrap();
        assert_eq!(old.persist(&cache).unwrap(), root);
        let mut delta = Evidence::new();
        let m = message(100);
        delta.insert(key(&m), m);
        let next = delta.retaining(&old);
        let mut work = PersistWork::default();
        let next_root = next.persist_counted(&cache, &mut work).unwrap();
        assert_eq!(work.value_encodes, 1);
        assert!(work.new_nodes <= 3 * old.root.as_ref().unwrap().height + 3);
        assert!(work.trusted_checks <= 6 * old.root.as_ref().unwrap().height + 8);
        assert!(recover(&cache, next_root, &Keys).is_err());
        cache.put(&saved).unwrap();
        assert_eq!(recover(&cache, root, &Keys).unwrap(), old);
        assert_eq!(recover(&cache, next_root, &Keys).unwrap(), next);
        std::fs::remove_dir_all(dir).unwrap();
    }
    #[cfg(feature = "std")]
    #[test]
    fn recovery_rejects_authenticated_blob_with_invalid_tree_metadata() {
        let dir = std::env::temp_dir().join(alloc::format!(
            "cbcl-evidence-invalid-{}-{:?}",
            std::process::id(),
            std::time::SystemTime::now()
        ));
        let cache = crate::host::Cache::open(&dir).unwrap();
        let mut map = Evidence::new();
        for i in 0..3 {
            let m = message(i);
            map.insert(key(&m), m);
        }
        let root = map.persist(&cache).unwrap();
        let n = map.root.as_ref().unwrap();
        let mut bad = n.bytes.clone();
        *bad.last_mut().unwrap() ^= 1;
        let bad_id = cache.put(&bad).unwrap();
        assert!(recover(&cache, Some(bad_id), &Keys).is_err());
        let bad = make(n.entry.clone(), n.right.clone(), n.left.clone());
        let bad_id = cache.put(&bad.bytes).unwrap();
        assert!(recover(&cache, Some(bad_id), &Keys).is_err());
        struct Reject;
        impl crate::certificate::KeyVerifier for Reject {
            fn verify(&self, _: &str, _: &[u8], _: &[u8]) -> bool {
                false
            }
        }
        assert!(recover(&cache, root, &Reject).is_err());
        assert_eq!(recover(&cache, None, &Keys).unwrap(), Evidence::new());
        std::fs::remove_dir_all(dir).unwrap();
    }
    #[cfg(feature = "std")]
    #[test]
    fn generation_budgets_precede_all_cache_work_even_for_trusted_roots() {
        let dir = std::env::temp_dir().join(alloc::format!(
            "cbcl-evidence-budget-{}-{:?}",
            std::process::id(),
            std::time::SystemTime::now()
        ));
        let cache = crate::host::Cache::open(&dir).unwrap();
        let m = message(1);
        let value = Arc::new(m.clone());
        let blob = hash(BLOB, &m.encode());
        let mut large = Evidence::new();
        // Synthetic cached lengths exercise the 256 MiB aggregate boundary
        // without allocating large bodies. Each individual value is in budget.
        for i in 0..1025 {
            let entry = Arc::new(Entry {
                key: (alloc::format!("{i:08}"), [0; 32]),
                value: value.clone(),
                blob,
                encoded_len: MAX_MESSAGE_BYTES,
                key_valid: true, // synthetic budget-only metadata
            });
            large.root = Some(insert(&large.root, entry).0);
        }
        assert!(large.root.as_ref().unwrap().recoverable);
        assert!(large.root.as_ref().unwrap().recovery_bytes > MAX_RECOVERY_BYTES);
        cache.put(&large.root.as_ref().unwrap().bytes).unwrap();
        let mut work = PersistWork::default();
        assert_eq!(large.persist_counted(&cache, &mut work), Err(Error::Budget));
        assert_eq!(work, PersistWork::default());
        let mut small = Evidence::new();
        small.insert(key(&m), m);
        small.persist(&cache).unwrap();
        let original = small.clone();
        // Cached node count must also be checked before trusting a stored root.
        let root = small.root.take().unwrap();
        small.root = Some(Arc::new(Node {
            entry: root.entry.clone(),
            left: root.left.clone(),
            right: root.right.clone(),
            height: root.height,
            size: MAX_NODES + 1,
            recovery_bytes: root.recovery_bytes,
            recoverable: true,
            bytes: root.bytes.clone(),
            blob: root.blob,
        }));
        assert_eq!(small.persist_counted(&cache, &mut work), Err(Error::Budget));
        assert_eq!(work, PersistWork::default());
        let retained = original.retaining(&original);
        assert!(Arc::ptr_eq(
            original.root.as_ref().unwrap(),
            retained.root.as_ref().unwrap()
        ));
        assert!(core::ptr::eq(
            original.iter().next().unwrap().1,
            retained.iter().next().unwrap().1
        ));
        assert_eq!(
            retained.persist_counted(&cache, &mut work).unwrap(),
            node_hash(&original.root)
        );
        assert_eq!(work.trusted_checks, 1);
        assert_eq!(work.new_nodes + work.value_encodes, 0);
        std::fs::remove_dir_all(dir).unwrap();
    }
    #[cfg(feature = "std")]
    #[test]
    fn persist_rejects_wrong_public_keys_before_trusted_lookup() {
        let dir = std::env::temp_dir().join(alloc::format!(
            "cbcl-evidence-key-{}-{:?}",
            std::process::id(),
            std::time::SystemTime::now()
        ));
        let cache = crate::host::Cache::open(&dir).unwrap();
        let m = message(1);
        let good_key = key(&m);
        let mut wrong_id = good_key.clone();
        wrong_id.0 = String::from("wrong");
        let mut wrong_wire = good_key.clone();
        wrong_wire.1[0] ^= 1;
        let mut previous = Evidence::new();
        previous.insert(good_key, m.clone());
        previous.persist(&cache).unwrap();
        for bad_key in [wrong_id, wrong_wire] {
            for extend in [false, true] {
                let mut bad = Evidence::new();
                if extend {
                    bad.extend([(bad_key.clone(), m.clone())]);
                } else {
                    bad.insert(bad_key.clone(), m.clone());
                }
                assert!(!bad.root.as_ref().unwrap().recoverable);
                let retained = bad.retaining(&previous);
                assert!(!retained.root.as_ref().unwrap().recoverable);
                for map in [&bad, &retained] {
                    // Even a trusted node blob cannot bypass structural binding.
                    cache.put(&map.root.as_ref().unwrap().bytes).unwrap();
                    let mut work = PersistWork::default();
                    assert_eq!(map.persist_counted(&cache, &mut work), Err(Error::Budget));
                    assert_eq!(work, PersistWork::default());
                }
            }
        }
        assert!(previous.persist(&cache).is_ok());
        std::fs::remove_dir_all(dir).unwrap();
    }
    #[cfg(feature = "std")]
    #[test]
    fn serde_rejects_duplicate_or_mismatched_keys() {
        let mut map = Evidence::new();
        let m = message(1);
        map.insert(key(&m), m.clone());
        let json = serde_json::to_vec(&map).unwrap();
        assert_eq!(serde_json::from_slice::<Evidence>(&json).unwrap(), map);
        let k = key(&m);
        assert!(serde_json::from_slice::<Evidence>(
            &serde_json::to_vec(&alloc::vec![(k.clone(), m.clone()), (k, m.clone())]).unwrap()
        )
        .is_err());
        assert!(serde_json::from_slice::<Evidence>(
            &serde_json::to_vec(&alloc::vec![((String::from("wrong"), [0; 32]), m)]).unwrap()
        )
        .is_err());
    }
}
