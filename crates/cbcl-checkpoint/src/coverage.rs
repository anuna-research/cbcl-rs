//! Persistent coverage set for [[SPEC-035-cached-state-checkpoints#CON-3500]].
//!
//! Scheme v1 uses `hash` (u32-BE length-delimited domain and payload). Keys
//! are H("cbcl/checkpoint/coverage/key/v1", native_id UTF-8), without address
//! normalization: recognition of native identities belongs to the pinned codec.
//! Key bits run most-significant-first within each byte, byte zero first.
//! A present leaf is H(leaf-domain, 0u16-BE || key); an empty leaf is
//! H(empty-domain, 0u16-BE). At height h=1..256, both ordinary and empty
//! subtrees use H(node-domain, h:u16-BE || left:32 || right:32), with empty
//! children recursively defined from height h-1. Thus height means distance
//! above leaves, and the root has height 256. Domains end in `/v1`.
//!
//! Proof siblings are root-to-leaf: siblings[d] is the opposite subtree at
//! depth d+1. Exactly 256 are required, including default hashes. Proofs
//! authenticate set presence/absence only, never native admission or a summary.
//!
//! Internally a Patricia tree elides unary paths. Cached hashes describe each
//! node at its branching depth; unary hashes are reconstructed when needed.
//! There are at most 2n-1 retained nodes for n distinct keys. Cloning shares
//! the root and empty-hash table; insertion copies only the searched branch
//! path. A frozen snapshot cannot change when its descendants are edited.
use crate::{hash, Error, Hash, Result};
use alloc::{sync::Arc, vec::Vec};
use serde::{Deserialize, Serialize};

const DEPTH: usize = 256;
const KEY: &[u8] = b"cbcl/checkpoint/coverage/key/v1";
const LEAF: &[u8] = b"cbcl/checkpoint/coverage/leaf/v1";
const NODE: &[u8] = b"cbcl/checkpoint/coverage/node/v1";
const EMPTY: &[u8] = b"cbcl/checkpoint/coverage/empty/v1";
fn key(id: &str) -> Hash {
    hash(KEY, id.as_bytes())
}
fn bit(key: &Hash, depth: usize) -> bool {
    key[depth / 8] & (0x80 >> (depth % 8)) != 0
}
fn leaf(key: &Hash) -> Hash {
    let mut bytes = [0; 34];
    bytes[2..].copy_from_slice(key);
    hash(LEAF, &bytes)
}
fn branch(depth: usize, left: Hash, right: Hash) -> Hash {
    let mut bytes = [0; 66];
    bytes[..2].copy_from_slice(&((DEPTH - depth) as u16).to_be_bytes());
    bytes[2..34].copy_from_slice(&left);
    bytes[34..].copy_from_slice(&right);
    hash(NODE, &bytes)
}
fn empties() -> [Hash; DEPTH + 1] {
    let mut out = [[0; 32]; DEPTH + 1];
    out[DEPTH] = hash(EMPTY, &0u16.to_be_bytes());
    for d in (0..DEPTH).rev() {
        out[d] = branch(d, out[d + 1], out[d + 1]);
    }
    out
}
fn common(a: &Hash, b: &Hash) -> usize {
    for i in 0..32 {
        let xor = a[i] ^ b[i];
        if xor != 0 {
            return i * 8 + xor.leading_zeros() as usize;
        }
    }
    DEPTH
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Proof {
    pub present: bool,
    pub siblings: Vec<Hash>,
}
impl Proof {
    fn root_for(&self, id: &str, present: bool) -> Result<Hash> {
        if self.siblings.len() != DEPTH {
            return Err(Error::Invalid("coverage proof length"));
        }
        let k = key(id);
        let mut h = if present {
            leaf(&k)
        } else {
            hash(EMPTY, &0u16.to_be_bytes())
        };
        for d in (0..DEPTH).rev() {
            h = if bit(&k, d) {
                branch(d, self.siblings[d], h)
            } else {
                branch(d, h, self.siblings[d])
            };
        }
        Ok(h)
    }
    /// Check either presence or absence against this exact immutable root.
    pub fn verify(&self, root: Hash, native_id: &str) -> Result<()> {
        if self.root_for(native_id, self.present)? != root {
            return Err(Error::Invalid("coverage proof root"));
        }
        Ok(())
    }
    /// Authenticate the pre-root, then insert using only this path. A covered
    /// duplicate preserves the root. No provider index is required by clients.
    pub fn updated_root(&self, root: Hash, native_id: &str) -> Result<Hash> {
        self.verify(root, native_id)?;
        if self.present {
            Ok(root)
        } else {
            self.root_for(native_id, true)
        }
    }
}

#[derive(Debug)]
struct Node {
    key: Hash,    // representative key, also commits the unary prefix
    depth: usize, // first branching bit, or 256 for a leaf
    hash: Hash,
    children: Option<(Arc<Node>, Arc<Node>)>,
}
#[derive(Clone, Debug)]
pub struct Coverage {
    tree: Option<Arc<Node>>,
    root: Hash,
    empty: Arc<[Hash; DEPTH + 1]>,
    #[cfg(test)]
    work: Work,
}
// Counters measure actual maintained-index operations, not prefix size or time.
#[derive(Default, Clone, Debug)]
struct Work {
    #[cfg(test)]
    visits: usize,
    #[cfg(test)]
    allocations: usize,
    #[cfg(test)]
    hashes: usize,
}
impl Work {
    fn visit(&mut self) {
        #[cfg(test)]
        {
            self.visits += 1;
        }
    }
    fn allocation(&mut self) {
        #[cfg(test)]
        {
            self.allocations += 1;
        }
    }
    fn hashed(&mut self) {
        #[cfg(test)]
        {
            self.hashes += 1;
        }
    }
}
impl Default for Coverage {
    fn default() -> Self {
        let empty = Arc::new(empties());
        Self {
            tree: None,
            root: empty[0],
            empty,
            #[cfg(test)]
            work: Work::default(),
        }
    }
}
fn lifted(node: &Node, depth: usize, empty: &[Hash; DEPTH + 1], work: &mut Work) -> Hash {
    let mut h = node.hash;
    for d in (depth..node.depth).rev() {
        work.hashed();
        h = if bit(&node.key, d) {
            branch(d, empty[d + 1], h)
        } else {
            branch(d, h, empty[d + 1])
        };
    }
    h
}
fn new_leaf(k: Hash, work: &mut Work) -> Arc<Node> {
    work.allocation();
    work.hashed();
    Arc::new(Node {
        key: k,
        depth: DEPTH,
        hash: leaf(&k),
        children: None,
    })
}
fn joined(
    depth: usize,
    left: Arc<Node>,
    right: Arc<Node>,
    empty: &[Hash; DEPTH + 1],
    work: &mut Work,
) -> Arc<Node> {
    let l = lifted(&left, depth + 1, empty, work);
    let r = lifted(&right, depth + 1, empty, work);
    work.allocation();
    work.hashed();
    Arc::new(Node {
        key: left.key,
        depth,
        hash: branch(depth, l, r),
        children: Some((left, right)),
    })
}
fn inserted(node: &Arc<Node>, k: Hash, empty: &[Hash; DEPTH + 1], work: &mut Work) -> Arc<Node> {
    work.visit();
    let split = common(&node.key, &k);
    if split < node.depth {
        let added = new_leaf(k, work);
        return if bit(&k, split) {
            joined(split, node.clone(), added, empty, work)
        } else {
            joined(split, added, node.clone(), empty, work)
        };
    }
    let Some((left, right)) = &node.children else {
        return node.clone();
    };
    if bit(&k, node.depth) {
        let next = inserted(right, k, empty, work);
        if Arc::ptr_eq(&next, right) {
            return node.clone();
        }
        joined(node.depth, left.clone(), next, empty, work)
    } else {
        let next = inserted(left, k, empty, work);
        if Arc::ptr_eq(&next, left) {
            return node.clone();
        }
        joined(node.depth, next, right.clone(), empty, work)
    }
}
impl Coverage {
    pub fn root(&self) -> Hash {
        self.root
    }
    pub fn contains(&self, native_id: &str) -> bool {
        let k = key(native_id);
        let mut cur = self.tree.as_deref();
        while let Some(node) = cur {
            if common(&node.key, &k) < node.depth {
                return false;
            }
            match &node.children {
                None => return true,
                Some((left, right)) => cur = Some(if bit(&k, node.depth) { right } else { left }),
            }
        }
        false
    }
    pub fn proof(&self, native_id: &str) -> Proof {
        let k = key(native_id);
        let mut siblings = self.empty[1..].to_vec();
        let mut cur = self.tree.as_deref();
        let mut present = false;
        while let Some(node) = cur {
            let split = common(&node.key, &k);
            if split < node.depth {
                siblings[split] = lifted(node, split + 1, &self.empty, &mut Work::default());
                break;
            }
            match &node.children {
                None => {
                    present = true;
                    break;
                }
                Some((left, right)) => {
                    let (next, opposite) = if bit(&k, node.depth) {
                        (right, left)
                    } else {
                        (left, right)
                    };
                    siblings[node.depth] =
                        lifted(opposite, node.depth + 1, &self.empty, &mut Work::default());
                    cur = Some(next);
                }
            }
        }
        Proof { present, siblings }
    }
    /// Copy only the changed branch path. Existing clones remain immutable.
    /// Native address spelling is opaque; the caller must recognize it first.
    pub fn insert(&mut self, native_id: &str) -> Hash {
        let k = key(native_id);
        let mut work = Work::default();
        work.hashed();
        let tree = match &self.tree {
            None => new_leaf(k, &mut work),
            Some(node) => inserted(node, k, &self.empty, &mut work),
        };
        if !self
            .tree
            .as_ref()
            .is_some_and(|old| Arc::ptr_eq(old, &tree))
        {
            self.root = lifted(&tree, 0, &self.empty, &mut work);
            self.tree = Some(tree);
        }
        #[cfg(test)]
        {
            self.work = work;
        }
        self.root
    }
}

#[cfg(test)]
#[path = "coverage_tests.rs"]
mod tests;
