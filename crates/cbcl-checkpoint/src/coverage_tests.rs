//! Coverage-only evidence for [[SPEC-035-cached-state-checkpoints#TEST-3505]],
//! [[SPEC-035-cached-state-checkpoints#TEST-3507]],
//! [[SPEC-035-cached-state-checkpoints#TEST-3514]] and
//! [[SPEC-035-cached-state-checkpoints#TEST-3515]]. Host installation, byte
//! budgets and full opening timing are deliberately outside these tests.
//!
//! Local evidence (2026-11-07, isolated harness importing coverage.rs unchanged):
//! `CARGO_PROFILE_DEV_DEBUG=0 CARGO_INCREMENTAL=0 CARGO_PROFILE_TEST_OPT_LEVEL=2
//! cargo test --manifest-path /tmp/cbcl-coverage-check/Cargo.toml --offline -- --nocapture`
//! passed all five coverage tests in 13.44s. A separate `cargo check
//! --no-default-features` passed. No complete checkpoint-crate or full-open
//! conformance claim follows from this isolated run.
//! For the 32-insert deltas, measured (visits, allocations, hashes) were
//! 600: (306,338,18605); 6000: (422,454,21187);
//! 60000: (514,546,17616). Proof siblings occupy 8192 bytes at every size;
//! retained Patricia nodes were 1199,11999,119999 respectively.
//! An external copy with root comparison bypassed failed at the wrong-root
//! assertion in `presence_absence_updates_and_mutated_paths` (exit 101).
use super::*;
use alloc::{format, vec};
fn id(i: usize) -> alloc::string::String {
    format!("sha256:{i:064x}")
}
fn hex(h: Hash) -> alloc::string::String {
    h.iter().map(|b| format!("{b:02x}")).collect()
}

#[test]
fn fixed_cross_language_vectors() {
    // Independently calculated with Python hashlib.sha256, u32/u16 big endian.
    let mut set = Coverage::default();
    assert_eq!(
        hex(set.root()),
        "fcdf015ebfce0a2fd45233623f65f7a11201c7ededfd96a063ef92c2c7ad74fc"
    );
    assert_eq!(
        hex(key(&id(0))),
        "985aabd2c6e6a4ae012477c0df8bd9ddcc045e660f3fdcf4f19e92c24ad38c3a"
    );
    assert_eq!(
        hex(set.insert(&id(0))),
        "94998fe7390b19a09a319b25120f69e92356fadb71b733ffc3138b9679b11eaa"
    );
}
#[test]
fn presence_absence_updates_and_mutated_paths() {
    let mut set = Coverage::default();
    for i in 0..40 {
        let absent = set.proof(&id(i));
        assert!(!absent.present);
        assert_eq!(absent.siblings.len(), 256);
        let expected = absent.updated_root(set.root(), &id(i)).unwrap();
        assert_eq!(set.insert(&id(i)), expected);
        assert!(set.contains(&id(i)));
        let proof = set.proof(&id(i));
        assert!(proof.present);
        proof.verify(set.root(), &id(i)).unwrap();
        assert_eq!(proof.updated_root(set.root(), &id(i)).unwrap(), set.root());
        let old = set.root();
        assert_eq!(set.insert(&id(i)), old);
        assert_eq!(set.work.allocations, 0);
    }
    for i in 0..80 {
        let p = set.proof(&id(i));
        assert_eq!(p.present, i < 40);
        p.verify(set.root(), &id(i)).unwrap();
        let mut wrong_root = set.root();
        wrong_root[0] ^= 1;
        assert!(p.verify(wrong_root, &id(i)).is_err());
        assert!(p.updated_root(wrong_root, &id(i)).is_err());
        let mut wrong = p.clone();
        wrong.present = !wrong.present;
        assert!(wrong.verify(set.root(), &id(i)).is_err());
        for d in [0, 1, 127, 254, 255] {
            let mut wrong = p.clone();
            wrong.siblings[d][d % 32] ^= 1;
            assert!(wrong.verify(set.root(), &id(i)).is_err());
        }
        for len in [0, 1, 255, 257, 512] {
            let bad = Proof {
                present: p.present,
                siblings: vec![[0; 32]; len],
            };
            assert!(bad.verify(set.root(), &id(i)).is_err());
            assert!(bad.updated_root(set.root(), &id(i)).is_err());
        }
    }
    let p = set.proof(&id(1));
    assert!(p.verify(set.root(), &id(2)).is_err());
    let mut reversed = p;
    reversed.siblings.reverse();
    assert!(reversed.verify(set.root(), &id(1)).is_err());
}
#[test]
fn snapshot_descendants_order_and_root_history() {
    let mut current = Coverage::default();
    let mut snapshots = vec![current.clone()];
    for i in 0..100 {
        let proof = current.proof(&id(i));
        let previous = current.root();
        let root = current.insert(&id(i));
        assert_eq!(proof.updated_root(previous, &id(i)).unwrap(), root);
        if i % 10 == 9 {
            snapshots.push(current.clone());
        }
    }
    for (i, snap) in snapshots.iter().enumerate() {
        let frozen = snap.root();
        let mut child = snap.clone();
        assert!(match (&snap.tree, &child.tree) {
            (Some(a), Some(b)) => Arc::ptr_eq(a, b),
            (None, None) => true,
            _ => false,
        });
        assert!(Arc::ptr_eq(&snap.empty, &child.empty));
        child.insert(&id(1000 + i));
        let mut grandchild = child.clone();
        grandchild.insert(&id(2000 + i));
        assert_eq!(snap.root(), frozen);
        assert!(!snap.contains(&id(1000 + i)));
        assert!(!child.contains(&id(2000 + i)));
        for j in 0..100 {
            assert_eq!(snap.contains(&id(j)), j < i * 10);
            snap.proof(&id(j)).verify(frozen, &id(j)).unwrap();
        }
    }
    let mut reverse = Coverage::default();
    for i in (0..100).rev() {
        reverse.insert(&id(i));
    }
    assert_eq!(current.root(), reverse.root());
    // A proof rooted in an older cut cannot be used at the descendant root.
    assert!(snapshots[1]
        .proof(&id(0))
        .verify(current.root(), &id(0))
        .is_err());
}

// An independent explicit sparse-tree oracle; no Patricia insertion code.
#[test]
fn compressed_index_matches_explicit_tree() {
    use alloc::collections::BTreeMap;
    let empty = empties();
    let mut nodes = BTreeMap::<(usize, Hash), Hash>::new();
    let prefix = |mut k: Hash, depth: usize| {
        for d in depth..256 {
            k[d / 8] &= !(128 >> (d % 8));
        }
        k
    };
    let mut set = Coverage::default();
    for i in 0..80 {
        let k = key(&id(i));
        let mut h = leaf(&k);
        nodes.insert((256, k), h);
        for d in (0..256).rev() {
            let mut opposite = prefix(k, d + 1);
            opposite[d / 8] ^= 128 >> (d % 8);
            let s = nodes
                .get(&(d + 1, opposite))
                .copied()
                .unwrap_or(empty[d + 1]);
            h = if bit(&k, d) {
                branch(d, s, h)
            } else {
                branch(d, h, s)
            };
            nodes.insert((d, prefix(k, d)), h);
        }
        assert_eq!(set.insert(&id(i)), h);
    }
}
#[test]
fn maintained_delta_work_600_6000_60000() {
    let mut set = Coverage::default();
    let mut next = 0;
    for size in [600, 6000, 60000] {
        while next < size {
            set.insert(&id(next));
            next += 1;
        }
        let frozen = set.clone();
        let old_root = frozen.root();
        let mut descendant = frozen.clone();
        let mut visits = 0;
        let mut allocations = 0;
        let mut hashes = 0;
        let mut client_root = old_root;
        for i in size..size + 32 {
            let proof = descendant.proof(&id(i));
            assert_eq!(proof.siblings.len() * 32, 8192); // fixed-width proof
            client_root = proof.updated_root(client_root, &id(i)).unwrap();
            descendant.insert(&id(i));
            assert_eq!(client_root, descendant.root());
            visits += descendant.work.visits;
            allocations += descendant.work.allocations;
            hashes += descendant.work.hashes;
        }
        assert_eq!(frozen.root(), old_root);
        assert!(visits <= 32 * 257, "prefix rescan: {visits}");
        assert!(allocations <= 32 * 258, "prefix copy: {allocations}");
        assert!(hashes <= 32 * 2048, "unexpected hashing work: {hashes}");
        let retained = count_nodes(frozen.tree.as_deref());
        assert_eq!(retained, 2 * size - 1);
        #[cfg(feature = "std")]
        std::println!("coverage size={size} tail=32 proof_bytes=8192 visits={visits} allocations={allocations} hashes={hashes} retained_nodes={retained}");
    }
}
fn count_nodes(node: Option<&Node>) -> usize {
    match node {
        None => 0,
        Some(n) => {
            1 + n
                .children
                .as_ref()
                .map(|(l, r)| count_nodes(Some(l)) + count_nodes(Some(r)))
                .unwrap_or(0)
        }
    }
}
