//! Experimental fold checkpoints. Inputs are PREACCEPTED acts, not wire messages.
//! This does not replace CBCL authentication, causal admission, or equivocation.
use cbcl_core::{
    message::{CausedBy, Message, Performative},
    sexpr::{Atom, SExpr},
    state::{self, Act, Entry, Rule, StateClause},
};
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::time::Instant;

mod drawing;
mod drawing_fixture;

type Hash = [u8; 32];
type Result<T> = std::result::Result<T, String>;
const SCOPE: &str = "drawing-probe/replacement-map/v1";

fn digest(domain: &[u8], bytes: &[u8]) -> Hash {
    let mut h = Sha256::new();
    h.update((domain.len() as u64).to_be_bytes());
    h.update(domain);
    h.update(bytes);
    h.finalize().into()
}
fn encoded<T: Serialize>(v: &T) -> Vec<u8> {
    serde_json::to_vec(v).unwrap()
}
fn branch(left: Hash, right: Hash) -> Hash {
    digest(b"branch", &[left.as_slice(), right.as_slice()].concat())
}
fn bit(key: Hash, depth: usize) -> bool {
    key[depth / 8] & (128 >> (depth % 8)) != 0
}
fn prefix(mut key: Hash, depth: usize) -> Hash {
    for i in depth..256 {
        key[i / 8] &= !(128 >> (i % 8));
    }
    key
}
fn sibling(mut key: Hash, depth: usize) -> Hash {
    key[depth / 8] ^= 128 >> (depth % 8);
    prefix(key, depth + 1)
}
fn defaults() -> Vec<Hash> {
    let mut out = vec![[0; 32]; 257];
    out[256] = digest(b"empty", b"");
    for d in (0..256).rev() {
        out[d] = branch(out[d + 1], out[d + 1]);
    }
    out
}

/// Sparse set of accepted identities. Provider storage grows with history.
/// Client witnesses omit default siblings; clients never receive this index.
#[derive(Clone)]
struct Coverage {
    nodes: HashMap<(usize, Hash), Hash>,
    empty: Vec<Hash>,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
struct Proof {
    present: bool,
    siblings: Vec<(usize, Hash)>,
}
impl Proof {
    fn root(&self, id: &str, present: bool) -> Result<Hash> {
        let empty = defaults();
        let key = digest(b"identity", id.as_bytes());
        let mut last = None;
        for (d, h) in &self.siblings {
            if *d >= 256 || last.is_some_and(|p| p >= *d) || *h == empty[d + 1] {
                return Err("noncanonical coverage witness".into());
            }
            last = Some(*d);
        }
        let siblings: BTreeMap<_, _> = self.siblings.iter().copied().collect();
        let mut h = if present {
            digest(b"leaf", &key)
        } else {
            empty[256]
        };
        for d in (0..256).rev() {
            let s = siblings.get(&d).copied().unwrap_or(empty[d + 1]);
            h = if bit(key, d) {
                branch(s, h)
            } else {
                branch(h, s)
            };
        }
        Ok(h)
    }
    fn check(&self, root: Hash, id: &str) -> Result<()> {
        if self.root(id, self.present)? != root {
            return Err("coverage witness does not match root".into());
        }
        Ok(())
    }
}
impl Coverage {
    fn new() -> Self {
        Self {
            nodes: HashMap::new(),
            empty: defaults(),
        }
    }
    fn root(&self) -> Hash {
        self.nodes
            .get(&(0, [0; 32]))
            .copied()
            .unwrap_or(self.empty[0])
    }
    fn proof(&self, id: &str) -> Proof {
        let key = digest(b"identity", id.as_bytes());
        Proof {
            present: self.nodes.contains_key(&(256, key)),
            siblings: (0..256)
                .filter_map(|d| self.nodes.get(&(d + 1, sibling(key, d))).map(|h| (d, *h)))
                .collect(),
        }
    }
    fn insert(&mut self, id: &str) {
        let key = digest(b"identity", id.as_bytes());
        let mut h = digest(b"leaf", &key);
        self.nodes.insert((256, key), h);
        for d in (0..256).rev() {
            let s = self
                .nodes
                .get(&(d + 1, sibling(key, d)))
                .copied()
                .unwrap_or(self.empty[d + 1]);
            h = if bit(key, d) {
                branch(s, h)
            } else {
                branch(h, s)
            };
            self.nodes.insert((d, prefix(key, d)), h);
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct Write {
    key: String,
    value: String,
}
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
struct Summary {
    live: BTreeMap<String, Write>,
    // References to identities NOT YET covered: cannot GC these tombstones.
    pending: BTreeSet<(String, String)>,
}
impl Summary {
    fn hash(&self) -> Hash {
        digest(b"summary", &encoded(self))
    }
    fn apply(&mut self, op: &Op, refs: &[Proof], root: Hash) -> Result<()> {
        if refs.len() != op.replaces.len() {
            return Err("missing replacement evidence".into());
        }
        // Validate before mutating: a rejected continuation must be retryable.
        for (id, proof) in op.replaces.iter().zip(refs) {
            proof.check(root, id)?;
        }
        let suppressed = self.pending.contains(&(op.key.clone(), op.id.clone()));
        // An arriving identity resolves pending references under EVERY key.
        // Only its own key suppresses the write; cross-key references are inert.
        self.pending.retain(|(_, id)| id != &op.id);
        if !op.delete && !suppressed {
            self.live.insert(
                op.id.clone(),
                Write {
                    key: op.key.clone(),
                    value: op.value.clone(),
                },
            );
        }
        for (id, proof) in op.replaces.iter().zip(refs) {
            if self.live.get(id).is_some_and(|w| w.key == op.key) {
                self.live.remove(id);
            }
            if !proof.present {
                self.pending.insert((op.key.clone(), id.clone()));
            }
        }
        Ok(())
    }
    fn render(&self) -> String {
        // Reuse the REAL kernel to project only the compact live rows.
        let acts: Vec<_> = self
            .live
            .iter()
            .map(|(id, w)| {
                let mut act = operation(&w.key, &w.value, false, &[], 0).act();
                act.address = id.clone();
                act
            })
            .collect();
        state::render_json(&state::fold(&clause(), None, &acts))
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct Op {
    id: String,
    key: String,
    value: String,
    delete: bool,
    replaces: Vec<String>,
    nonce: u64,
}
impl Op {
    fn act(&self) -> Act {
        let strval = |s: &str| SExpr::Atom(Atom::Str(s.into()));
        let fields = [
            ("shape", strval(&self.key)),
            ("value", strval(&self.value)),
            ("nonce", strval(&self.nonce.to_string())),
            (
                "replaces",
                SExpr::List(self.replaces.iter().map(|s| strval(s)).collect()),
            ),
        ];
        Act::from_message(
            Message::Simple {
                performative: Performative::Custom(
                    if self.delete { "erase" } else { "paint" }.into(),
                ),
                recipient: None,
                content: SExpr::List(vec![]),
                params: fields
                    .into_iter()
                    .flat_map(|(k, v)| [SExpr::Atom(Atom::Keyword(k.into())), v])
                    .collect(),
                thread: Some(SCOPE.into()),
                sender: None,
                caused_by: Some(CausedBy::Begin),
            },
            "@artist",
        )
        .unwrap()
    }
    fn validate(&self) -> Result<()> {
        if self.id != self.act().address {
            return Err("operation identity mismatch".into());
        }
        Ok(())
    }
}
fn operation(key: &str, value: &str, delete: bool, replaces: &[String], nonce: u64) -> Op {
    let mut op = Op {
        id: String::new(),
        key: key.into(),
        value: value.into(),
        delete,
        replaces: replaces.into(),
        nonce,
    };
    op.id = op.act().address;
    op
}
fn clause() -> StateClause {
    StateClause {
        entries: vec![
            // The upstream v4 kernel retired hash-arbitrated registers. Keep
            // this historical probe's multi-value/set oracles buildable; the
            // production checkpoint crate tests explicit HLC map semantics.
            Entry::Field {
                name: "values".into(),
                rule: Rule::ValuesPerKey {
                    verb: "paint".into(),
                    key: "shape".into(),
                    value: "value".into(),
                    delete: Some("erase".into()),
                },
            },
            Entry::Field {
                name: "set".into(),
                rule: Rule::ObservedSet {
                    add: "paint".into(),
                    remove: "erase".into(),
                    key: "shape".into(),
                },
            },
        ],
    }
}
fn oracle(ops: &[Op]) -> String {
    state::render_json(&state::fold(
        &clause(),
        None,
        &ops.iter().map(Op::act).collect::<Vec<_>>(),
    ))
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct Step {
    op: Op,
    identity: Proof,
    replacements: Vec<Proof>,
}
#[derive(Clone)]
struct Replica {
    summary: Summary,
    coverage: Coverage,
}
impl Replica {
    fn new() -> Self {
        Self {
            summary: Summary::default(),
            coverage: Coverage::new(),
        }
    }
    fn apply(&mut self, op: &Op) -> Result<Step> {
        op.validate()?;
        let identity = self.coverage.proof(&op.id);
        if !identity.present {
            self.coverage.insert(&op.id);
        }
        let replacements: Vec<_> = op
            .replaces
            .iter()
            .map(|id| self.coverage.proof(id))
            .collect();
        if !identity.present {
            self.summary
                .apply(op, &replacements, self.coverage.root())?;
        }
        Ok(Step {
            op: op.clone(),
            identity,
            replacements,
        })
    }
}
#[derive(Clone, Debug, Serialize, Deserialize)]
struct Descriptor {
    scope: String,
    member: usize,
    coverage: Hash,
    summary: Hash,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
struct Anchor {
    descriptor: Descriptor,
    signature: Vec<u8>,
    state: Summary,
    bridge: Vec<Step>,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
struct Snapshot {
    target_coverage: Hash,
    target_summary: Hash,
    anchors: Vec<Anchor>,
}
fn anchor(replica: &Replica, member: usize, key: &SigningKey) -> Anchor {
    let descriptor = Descriptor {
        scope: SCOPE.into(),
        member,
        coverage: replica.coverage.root(),
        summary: replica.summary.hash(),
    };
    Anchor {
        signature: key.sign(&encoded(&descriptor)).to_bytes().to_vec(),
        descriptor,
        state: replica.summary.clone(),
        bridge: vec![],
    }
}
fn advance(state: &mut Summary, root: &mut Hash, step: &Step) -> Result<()> {
    step.op.validate()?;
    if step.replacements.len() != step.op.replaces.len() {
        return Err("replacement witness arity".into());
    }
    step.identity.check(*root, &step.op.id)?;
    if !step.identity.present {
        let next_root = step.identity.root(&step.op.id, true)?;
        state.apply(&step.op, &step.replacements, next_root)?;
        *root = next_root;
    } else if !step.replacements.is_empty() {
        // Duplicate steps are no-ops, but all attached evidence still recognizes.
        for (id, p) in step.op.replaces.iter().zip(&step.replacements) {
            p.check(*root, id)?;
        }
    }
    Ok(())
}
fn verify(snapshot: &Snapshot, roster: &[VerifyingKey]) -> Result<Summary> {
    if roster.is_empty() || snapshot.anchors.len() != roster.len() {
        return Err("incomplete pinned roster".into());
    }
    let mut members = BTreeSet::new();
    let mut result = None;
    for a in &snapshot.anchors {
        let d = &a.descriptor;
        if d.scope != SCOPE || !members.insert(d.member) {
            return Err("scope or duplicate member".into());
        }
        let key = roster.get(d.member).ok_or("unknown member")?;
        let signature =
            Signature::from_slice(&a.signature).map_err(|_| "bad signature encoding")?;
        key.verify_strict(&encoded(d), &signature)
            .map_err(|_| "bad signature")?;
        if a.state.hash() != d.summary {
            return Err("member state mismatch".into());
        }
        let mut state = a.state.clone();
        let mut root = d.coverage;
        for step in &a.bridge {
            advance(&mut state, &mut root, step)?;
        }
        if root != snapshot.target_coverage || state.hash() != snapshot.target_summary {
            return Err("incomplete or incorrect reconstruction".into());
        }
        result = Some(state);
    }
    result.ok_or("no anchor".into())
}

fn workload(n: usize) -> Vec<Op> {
    let mut heads: BTreeMap<String, String> = BTreeMap::new();
    (0..n)
        .map(|i| {
            let k = format!("shape-{}", i % 8);
            let refs: Vec<_> = heads.get(&k).cloned().into_iter().collect();
            let op = operation(
                &k,
                &format!("colour-{}", i % 3),
                i % 13 == 0,
                &refs,
                i as u64,
            );
            heads.insert(k, op.id.clone());
            op
        })
        .collect()
}
fn build(ops: &[Op], cuts: &[usize], keys: &[SigningKey]) -> (Snapshot, Replica) {
    let mut replica = Replica::new();
    let mut anchors = Vec::new();
    for i in 0..=ops.len() {
        for (member, cut) in cuts.iter().enumerate() {
            if *cut == i {
                anchors.push(anchor(&replica, member, &keys[member]));
            }
        }
        if let Some(op) = ops.get(i) {
            let step = replica.apply(op).unwrap();
            for a in &mut anchors {
                a.bridge.push(step.clone());
            }
        }
    }
    (
        Snapshot {
            target_coverage: replica.coverage.root(),
            target_summary: replica.summary.hash(),
            anchors,
        },
        replica,
    )
}

fn main() {
    if std::env::args().nth(1).as_deref() == Some("cached") {
        drawing::cached::run();
        return;
    }
    if std::env::args().nth(1).as_deref() == Some("admission") {
        drawing::run();
        return;
    }
    let keys: Vec<_> = (1..=3).map(|i| SigningKey::from_bytes(&[i; 32])).collect();
    let roster: Vec<_> = keys.iter().map(SigningKey::verifying_key).collect();
    let mut rows = Vec::new();
    for (n, lag, pattern) in [
        (100, 2, "overwrite"),
        (1000, 2, "overwrite"),
        (3000, 2, "overwrite"),
        (1000, 100, "overwrite"),
        (1000, 2, "concurrent-identical"),
        (1000, 2, "unseen-references"),
    ] {
        let ops = match pattern {
            "concurrent-identical" => (0..n)
                .map(|i| operation("x", "red", false, &[], i as u64))
                .collect(),
            "unseen-references" => (0..n)
                .map(|i| {
                    let future = operation("x", "red", false, &[], (n + i) as u64);
                    operation("x", "", true, &[future.id], i as u64)
                })
                .collect(),
            _ => workload(n),
        };
        let start = Instant::now();
        let (snapshot, provider) = build(&ops, &[n - lag, n - 1, n], &keys);
        let producer_build_us = start.elapsed().as_micros();
        let full = oracle(&ops);
        let bytes = encoded(&snapshot);
        let replay_bytes = encoded(&ops.iter().map(Op::act).collect::<Vec<_>>());
        let mut replay = Vec::new();
        let mut verification = Vec::new();
        for _ in 0..5 {
            let start = Instant::now();
            let acts: Vec<Act> = serde_json::from_slice(&replay_bytes).unwrap();
            assert_eq!(
                state::render_json(&state::fold(&clause(), None, &acts)),
                full
            );
            replay.push(start.elapsed().as_micros());
            let start = Instant::now();
            let received: Snapshot = serde_json::from_slice(&bytes).unwrap();
            let client = verify(&received, &roster).unwrap();
            assert_eq!(client.render(), full);
            verification.push(start.elapsed().as_micros());
        }
        replay.sort();
        verification.sort();
        rows.push(serde_json::json!({
            "pattern": pattern,
            "history_acts": n,
            "oldest_member_lag_acts": lag,
            "live_writes": provider.summary.live.len(),
            "pending_references": provider.summary.pending.len(),
            "replay_act_json_bytes": replay_bytes.len(),
            "replay_lean_op_json_bytes": encoded(&ops).len(),
            "snapshot_json_bytes": bytes.len(),
            "bridge_acts": snapshot.anchors.iter().map(|a|a.bridge.len()).sum::<usize>(),
            "coverage_proof_json_bytes": snapshot.anchors.iter().flat_map(|a| &a.bridge).map(|s|encoded(&s.identity).len()+encoded(&s.replacements).len()).sum::<usize>(),
            "provider_index_nodes": provider.coverage.nodes.len(),
            "producer_build_us": producer_build_us,
            "client_archive_interface": "none; verify receives snapshot and pinned keys only",
            "median_replay_decode_fold_render_us": replay[2],
            "median_snapshot_decode_verify_render_us": verification[2],
        }));
    }
    println!("{}",serde_json::to_string_pretty(&serde_json::json!({"status":"experimental fold-only; preaccepted inputs; no causal-admission claim", "encoding":"JSON for both paths, not an optimized wire format", "timing":"local medians of five runs; both paths decode and render; replay input acts are preaccepted; snapshot additionally checks member signatures; producer construction reported separately", "rows":rows})).unwrap());
}

#[cfg(test)]
mod tests;
