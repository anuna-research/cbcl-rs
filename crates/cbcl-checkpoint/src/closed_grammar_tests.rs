//! TEST-3516: bounded deterministic hostile inputs at all closed codec boundaries.
//! Recognition is deliberately separate from certificate authority/admission.
use crate::{
    certificate::{Certificate, SignedMessage},
    codec,
    host::{Limits, Offer},
    member::Client,
    summary::Summary,
    test_support::Fixture,
    Error,
};
use cbcl_core::{
    protocol::CausalProtocol,
    state::{Entry, Rule, StateClause},
};
use std::{
    collections::BTreeSet,
    panic::{catch_unwind, AssertUnwindSafe},
};

const MAX_CASE: usize = 96 * 1024;
#[derive(Clone, Copy, Debug)]
enum Kind {
    Certificate,
    Offer,
    Summary,
    Native,
}
impl Kind {
    fn index(self) -> usize {
        self as usize
    }
}
#[derive(Default)]
struct Stats {
    profiles: Vec<([u8; 32], StateClause, Option<CausalProtocol>)>,
    attempted: [usize; 4],
    recognized: [usize; 4],
    rejected: [usize; 4],
}
impl Stats {
    fn check(&mut self, f: &Fixture, kind: Kind, bytes: &[u8]) -> bool {
        assert!(bytes.len() <= MAX_CASE, "test corpus exceeds its own bound");
        if self.profiles.is_empty() {
            let basic = f.context.target().state.as_ref().unwrap().clone();
            let protocol = f.context.target().causal_protocol.clone();
            for (clause, p) in [
                (basic.clone(), protocol.clone()),
                (basic, None),
                (all_rules(), protocol),
            ] {
                let hash = Summary::new(&clause, p.as_ref()).unwrap().schema_hash();
                self.profiles.push((hash, clause, p));
            }
        }
        let number = self.attempted[kind.index()];
        self.attempted[kind.index()] += 1;
        let attempt = catch_unwind(AssertUnwindSafe(|| match kind {
            Kind::Certificate => match Certificate::decode(bytes, &f.context) {
                Ok(value) => {
                    let encoded = value.encode(&f.context);
                    assert_eq!(
                        encoded, bytes,
                        "recognized certificate must consume/canonicalize exactly"
                    );
                    assert_eq!(Certificate::decode(&encoded, &f.context).unwrap(), value);
                    true
                }
                Err(_) => false,
            },
            Kind::Offer => match Offer::decode(bytes, &Limits::default()) {
                Ok(value) => {
                    let encoded = value.encode();
                    assert_eq!(
                        encoded, bytes,
                        "recognized offer must consume/canonicalize exactly"
                    );
                    assert_eq!(
                        Offer::decode(&encoded, &Limits::default())
                            .unwrap()
                            .encode(),
                        encoded
                    );
                    true
                }
                Err(_) => false,
            },
            Kind::Summary => {
                let Some((_, clause, protocol)) = self
                    .profiles
                    .iter()
                    .find(|(hash, _, _)| bytes.get(4..36) == Some(hash.as_slice()))
                else {
                    return false;
                };
                match Summary::decode_for(bytes, clause, protocol.as_ref()) {
                    Ok(value) => {
                        let encoded = value.encode();
                        assert_eq!(
                            encoded, bytes,
                            "recognized v2 summary must consume/canonicalize exactly"
                        );
                        assert_eq!(
                            Summary::decode_for(&encoded, clause, protocol.as_ref()).unwrap(),
                            value
                        );
                        true
                    }
                    Err(_) => false,
                }
            }
            Kind::Native => match codec::decode_message(bytes) {
                Ok(value) => {
                    let encoded = codec::message_bytes(&value);
                    assert_eq!(
                        encoded, bytes,
                        "recognized native message must consume/canonicalize exactly"
                    );
                    assert_eq!(codec::decode_message(&encoded).unwrap(), value);
                    assert_eq!(SignedMessage::decode(bytes).unwrap().encode(), bytes);
                    true
                }
                Err(_) => false,
            },
        }));
        let recognized=attempt.unwrap_or_else(|_|panic!("{kind:?} codec panicked or violated roundtrip: case {number}, length {}, prefix {:?}",bytes.len(),&bytes[..bytes.len().min(24)]));
        if recognized {
            self.recognized[kind.index()] += 1;
        } else {
            self.rejected[kind.index()] += 1;
        }
        recognized
    }
}
struct Noise(u64);
impl Noise {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn bytes(&mut self, n: usize) -> Vec<u8> {
        (0..n).map(|_| (self.next() >> 24) as u8).collect()
    }
}
/// Record offsets from known-good models only, to corrupt REAL nested lengths,
/// counts and proof tags rather than solely fail the first random header byte.
#[derive(Default)]
struct Layout {
    at: usize,
    lengths: Vec<usize>,
    tags: Vec<usize>,
    byte_tags: Vec<usize>,
    row_tags: BTreeSet<usize>,
    helpers: Vec<(&'static str, usize, usize)>,
}
impl Layout {
    fn count(&mut self) {
        self.lengths.push(self.at);
        self.at += 4;
    }
    fn bytes(&mut self, n: usize) {
        self.count();
        self.at += n;
    }
    fn proof(&mut self, n: usize) {
        self.tags.push(self.at);
        self.at += 4;
        self.count();
        self.at += 32 * n;
    }
    fn read_count(&mut self, good: &[u8]) -> usize {
        let n = u32::from_be_bytes(good[self.at..self.at + 4].try_into().unwrap()) as usize;
        self.count();
        n
    }
    fn read_bytes(&mut self, good: &[u8]) {
        let n = self.read_count(good);
        self.at += n;
        assert!(self.at <= good.len());
    }
    fn tag(&mut self, good: &[u8]) -> usize {
        self.tags.push(self.at);
        let n = u32::from_be_bytes(good[self.at..self.at + 4].try_into().unwrap()) as usize;
        self.at += 4;
        n
    }
    fn contributions(&mut self, good: &[u8]) {
        for _ in 0..self.read_count(good) {
            self.read_bytes(good);
            self.read_bytes(good);
            for _ in 0..3 {
                if self.tag(good) == 1 {
                    self.read_bytes(good);
                }
            }
        }
    }
    fn progress(&mut self, good: &[u8]) {
        let n = self.read_count(good);
        let start = self.at;
        let end = self.at + n;
        self.at += 36;
        self.read_bytes(good);
        if self.tag(good) == 1 {
            self.read_bytes(good);
            self.read_bytes(good);
            for _ in 0..self.read_count(good) {
                self.read_bytes(good);
                self.read_bytes(good);
                match self.tag(good) {
                    0 | 1 => {}
                    2 => self.read_bytes(good),
                    3 => {
                        for _ in 0..self.read_count(good) {
                            self.read_bytes(good);
                        }
                    }
                    _ => panic!("known progress tag"),
                }
            }
        }
        assert_eq!(self.at, end);
        self.helpers.push(("progress", start, end));
    }
    fn resource(&mut self, good: &[u8]) {
        let n = self.read_count(good);
        let start = self.at;
        let end = self.at + n;
        self.at += 4;
        self.byte_tags.push(self.at);
        let bound = good[self.at];
        self.at += 1;
        if bound == 1 {
            self.at += 32;
        }
        for _ in 0..self.read_count(good) {
            self.read_bytes(good);
        }
        for _ in 0..self.read_count(good) {
            self.read_bytes(good);
        }
        assert_eq!(self.at, end);
        self.helpers.push(("resource", start, end));
    }
    fn summary(good: &[u8]) -> Self {
        assert_eq!(u32::from_be_bytes(good[..4].try_into().unwrap()), 2);
        let mut l = Self {
            at: 36,
            ..Self::default()
        };
        if l.tag(good) == 1 {
            l.progress(good);
        }
        let rows = l.read_count(good);
        let mut row_tags = BTreeSet::new();
        for _ in 0..rows {
            let tag = l.tag(good);
            row_tags.insert(tag);
            match tag {
                0 | 2 => l.contributions(good),
                1 => {
                    l.contributions(good);
                    for _ in 0..l.read_count(good) {
                        l.read_bytes(good);
                        l.read_bytes(good);
                    }
                }
                3 => {
                    l.tag(good);
                }
                4 => l.at += 8,
                5 => l.at += 16,
                6 => {
                    for _ in 0..l.read_count(good) {
                        l.read_bytes(good);
                    }
                }
                7 => {
                    for _ in 0..l.read_count(good) {
                        l.read_bytes(good);
                        l.read_bytes(good);
                        l.read_bytes(good);
                    }
                }
                8 => {}
                9 => l.progress(good),
                10 => l.resource(good),
                _ => panic!("known summary row tag"),
            }
        }
        assert_eq!(l.at, good.len());
        if rows == 16 {
            assert_eq!(row_tags, (0..=10).collect());
        }
        l.row_tags = row_tags;
        l
    }
}
struct Seed {
    kind: Kind,
    bytes: Vec<u8>,
    layout: Layout,
}
fn all_rules() -> StateClause {
    use cbcl_core::escrow::{CounterRule, Ownership};
    let resource = CounterRule {
        ownership: Ownership::Account,
        certification: Default::default(),
        floor: 0,
        ceiling: None,
        initial_verb: "open".into(),
        initial_key: "allocations".into(),
        headroom_key: None,
        issuer: "member".into(),
        increment: ("mint".into(), "amount".into()),
        decrement: ("burn".into(), "amount".into()),
        transfer: None,
        transfer_headroom: None,
    };
    let rules = vec![
        Rule::Initial {
            verb: "open".into(),
            key: "title".into(),
        },
        Rule::Values {
            verb: "write".into(),
            key: "value".into(),
        },
        Rule::ValuesPerKey {
            verb: "write".into(),
            key: "item".into(),
            value: "value".into(),
            delete: Some("drop".into()),
        },
        Rule::ObservedSet {
            add: "write".into(),
            remove: "drop".into(),
            key: "item".into(),
        },
        Rule::LwwMap {
            verb: "write".into(),
            key: "item".into(),
            value: "value".into(),
            clock: "clock".into(),
            delete: Some("drop".into()),
        },
        Rule::LwwRegister {
            verb: "write".into(),
            key: "value".into(),
            clock: "clock".into(),
        },
        Rule::LwwPerSigner {
            verb: "write".into(),
            key: "value".into(),
            clock: "clock".into(),
        },
        Rule::Exists {
            verb: "write".into(),
        },
        Rule::Count {
            verb: "write".into(),
        },
        Rule::Events {
            verb: "write".into(),
            key: "value".into(),
        },
        Rule::SetUnion {
            verb: "write".into(),
            key: "tags".into(),
        },
        Rule::Counter {
            inc: "write".into(),
            dec: "drop".into(),
            key: "value".into(),
        },
        Rule::Histogram { field: "f4".into() },
        Rule::Sum { field: "f4".into() },
        Rule::Progress {
            verb: "write".into(),
        },
        Rule::BoundedCounter(Box::new(resource)),
    ];
    assert_eq!(rules.len(), 16);
    StateClause {
        entries: rules
            .into_iter()
            .enumerate()
            .map(|(i, rule)| Entry::Field {
                name: format!("f{i}"),
                rule,
            })
            .collect(),
    }
}
fn seeds(f: &Fixture) -> Vec<Seed> {
    let first = f.write("first", 1, &[], "@m0");
    let second = f.write(
        "second",
        2,
        &[first.authenticate(&f.keys).unwrap().address],
        "@m1",
    );
    let future = f.write("unseen", 10, &[], "@m3");
    let pending = f.write(
        "pending",
        3,
        &[future.authenticate(&f.keys).unwrap().address],
        "@m2",
    );
    let mut members = f.members(&[first, second, pending.clone()]);
    let cert = f.certificate(&members);
    cert.verify(&f.context, &f.keys).unwrap();
    assert!(members[0].client().summary.pending_references() > 0);
    let tail = f.write(
        "tail",
        4,
        &[pending.authenticate(&f.keys).unwrap().address],
        "@m0",
    );
    let step = members[0].step(&tail).unwrap();
    let mut client = Client::from_certificate(&f.context, &cert, &f.keys).unwrap();
    let floor = client.floor();
    client.apply(&step, &f.context, &f.keys).unwrap();
    members[0].accept(&tail, &f.context, &f.keys).unwrap();
    let proofs = floor
        .frontier
        .iter()
        .map(|id| (id.clone(), members[0].coverage().proof(id)))
        .collect();
    let offer = Offer {
        blob: cert.blob_id(&f.context),
        tail: vec![step],
        floor_proofs: proofs,
    };
    client.check_floor(&floor, &offer.floor_proofs).unwrap();
    let mut l = Layout {
        at: 4,
        ..Layout::default()
    };
    l.bytes(cert.manifest.target.len());
    l.at += 32;
    l.bytes(cert.manifest.companion.len());
    l.at += 128;
    l.count();
    for id in &cert.manifest.frontier {
        l.bytes(id.len());
    }
    l.bytes(cert.summary.len());
    l.bytes(f.context.companion_root().encode().len());
    l.bytes(cert.opener.encode().len());
    l.count();
    for e in &cert.endorsements {
        l.bytes(e.encode().len());
    }
    let bytes = cert.encode(&f.context);
    assert_eq!(l.at, bytes.len());
    let mut out = vec![Seed {
        kind: Kind::Certificate,
        bytes,
        layout: l,
    }];
    for offer in [
        offer,
        Offer {
            blob: cert.blob_id(&f.context),
            tail: vec![],
            floor_proofs: vec![],
        },
    ] {
        let mut l = Layout {
            at: 32,
            ..Layout::default()
        };
        l.count();
        for s in &offer.tail {
            l.bytes(s.message.encode().len());
            l.count();
            for (m, p) in &s.ancestry {
                l.bytes(m.encode().len());
                l.proof(p.siblings.len());
            }
            l.proof(s.identity.siblings.len());
            l.count();
            for (id, p) in &s.replacements {
                l.bytes(id.len());
                l.proof(p.siblings.len());
            }
        }
        l.count();
        for (id, p) in &offer.floor_proofs {
            l.bytes(id.len());
            l.proof(p.siblings.len());
        }
        let bytes = offer.encode();
        assert_eq!(l.at, bytes.len());
        out.push(Seed {
            kind: Kind::Offer,
            bytes,
            layout: l,
        });
    }
    let clause = all_rules();
    let protocol = f.context.target().causal_protocol.as_ref();
    let mut full = Summary::new(&clause, protocol).unwrap();
    let mut seen = BTreeSet::new();
    let projected=SignedMessage::sign(crate::test_support::parse(&format!(
        "(lang {} (write (@m0 @m1 @m2 @m3) :item \"all\" :value 7 :clock \"hlc-0000000000000002-00000000\" :tags (\"a\" \"b\") :from @m0 :sender @m0 :thread \"target\" :caused-by \"{}\"))",
        f.context.target().name,f.target_open.id().unwrap())),"@m0",&f.keys).unwrap();
    for m in [f.context.target_root(), &f.target_open, &projected] {
        let a = m.authenticate(&f.keys).unwrap();
        full.apply(&a, |id| seen.contains(id)).unwrap();
        seen.insert(a.address);
    }
    for bytes in [
        cert.summary.clone(),
        Summary::new(f.context.target().state.as_ref().unwrap(), None)
            .unwrap()
            .encode(),
        Summary::new(&clause, protocol).unwrap().encode(),
        full.encode(),
    ] {
        let l = Layout::summary(&bytes);
        out.push(Seed {
            kind: Kind::Summary,
            bytes,
            layout: l,
        });
    }
    for m in [
        f.context.target_root(),
        f.context.companion_root(),
        &f.opener,
        &tail,
        &cert.endorsements[0],
    ] {
        out.push(Seed {
            kind: Kind::Native,
            bytes: m.encode(),
            layout: Layout::default(),
        });
    }
    assert!(out.iter().all(|s| s.bytes.len() < MAX_CASE - 32));
    out
}

fn emit_v2_vectors(f: &Fixture, seeds: &[Seed], stats: &Stats) {
    use sha2::{Digest, Sha256};
    let Some(path) = std::env::var_os("CHECKPOINT_V2_VECTORS_OUT") else {
        return;
    };
    let vectors:Vec<_>=seeds.iter().filter(|s|matches!(s.kind,Kind::Summary)).map(|seed|{
        let (_,clause,protocol)=stats.profiles.iter().find(|(hash,_,_)|seed.bytes.get(4..36)==Some(hash.as_slice())).unwrap();
        let summary=Summary::decode_for(&seed.bytes,clause,protocol.as_ref()).unwrap();
        serde_json::json!({
            "version":2,"byte_length":seed.bytes.len(),"hex":crate::hex(&seed.bytes),
            "clause":clause,"protocol":protocol,
            "schema_hash":crate::hex(&summary.schema_hash()),"profile_hash":crate::hex(&summary.profile_hash()),
            "surface_rule_count":clause.fields().count(),"binary_row_tags":seed.layout.row_tags,
            "nested_helpers":seed.layout.helpers.iter().map(|(kind,start,end)|serde_json::json!({"kind":kind,"offset":start,"byte_length":end-start,"hex":crate::hex(&seed.bytes[*start..*end])})).collect::<Vec<_>>(),
        })
    }).collect();
    assert!(vectors
        .iter()
        .any(|v| v["surface_rule_count"] == 16
            && v["binary_row_tags"].as_array().unwrap().len() == 11));
    let sources: [(&str, &[u8]); 5] = [
        (
            "crates/cbcl-core/src/escrow.rs",
            include_bytes!("../../cbcl-core/src/escrow.rs"),
        ),
        (
            "crates/cbcl-checkpoint/src/summary.rs",
            include_bytes!("summary.rs"),
        ),
        (
            "crates/cbcl-checkpoint/src/resource_resume.rs",
            include_bytes!("resource_resume.rs"),
        ),
        (
            "crates/cbcl-checkpoint/src/progress_resume.rs",
            include_bytes!("progress_resume.rs"),
        ),
        (
            "crates/cbcl-checkpoint/src/closed_grammar_tests.rs",
            include_bytes!("closed_grammar_tests.rs"),
        ),
    ];
    let source_hashes: serde_json::Map<String, serde_json::Value> = sources
        .into_iter()
        .map(|(name, bytes)| {
            (
                name.into(),
                serde_json::json!(crate::hex(&Sha256::digest(bytes))),
            )
        })
        .collect();
    let value = serde_json::json!({
        "format":"cbcl/checkpoint/v2-wire-test-vectors/1",
        "claim":"Canonical closed-recognizer seeds from actual Rust v2 encoders. Recognition is not snapshot truth, native admission, extraction correctness, or resource finality authority.",
        "fixture_context_hash":crate::hex(&f.context.hash()),"fixture_profile_hash":crate::hex(&f.context.profile()),
        "source_sha256":source_hashes,"vectors":vectors,
    });
    let path = std::path::PathBuf::from(path);
    if let Some(parent) = path.parent() {
        if !parent.as_os_str().is_empty() {
            std::fs::create_dir_all(parent).unwrap();
        }
    }
    std::fs::write(path, serde_json::to_vec_pretty(&value).unwrap()).unwrap();
}

#[test]
fn test_3516_fixed_seed_random_noise_is_total_for_all_four_codecs() {
    let f = Fixture::new();
    let mut stats = Stats::default();
    for seed in seeds(&f) {
        assert!(stats.check(&f, seed.kind, &seed.bytes));
    }
    let mut noise = Noise(0x3516_f00d_9804_2026);
    for n in 0..768 {
        let len = if n < 32 {
            n
        } else {
            (noise.next() % 1025) as usize
        };
        let bytes = noise.bytes(len);
        for kind in [Kind::Certificate, Kind::Offer, Kind::Summary, Kind::Native] {
            stats.check(&f, kind, &bytes);
        }
    }
    for i in 0..4 {
        assert!(stats.attempted[i] >= 769);
        assert!(stats.recognized[i] > 0);
        assert!(stats.rejected[i] >= 700);
    }
}

#[test]
fn test_3516_structured_truncation_lengths_tags_splices_and_roundtrips() {
    let f = Fixture::new();
    let mut stats = Stats::default();
    let mut noise = Noise(0xc105_ed35_1600_0001);
    let corpus = seeds(&f);
    for seed in &corpus {
        let raw = &seed.bytes;
        assert!(stats.check(&f, seed.kind, raw));
        let mut cuts = BTreeSet::new();
        if raw.len() <= 1024 {
            cuts.extend(0..raw.len());
        } else {
            cuts.extend(0..128);
            cuts.extend(raw.len() - 128..raw.len());
            cuts.extend((0..256).map(|i| i * raw.len() / 256));
        }
        for at in seed.layout.lengths.iter().chain(&seed.layout.tags) {
            for delta in 0..5 {
                if at + delta < raw.len() {
                    cuts.insert(at + delta);
                }
            }
        }
        for cut in cuts {
            assert!(
                !stats.check(&f, seed.kind, &raw[..cut]),
                "proper truncation recognized: {:?} at {cut}",
                seed.kind
            );
        }
        for &at in &seed.layout.lengths {
            let original = u32::from_be_bytes(raw[at..at + 4].try_into().unwrap());
            for n in [
                0,
                1,
                255,
                256,
                4096,
                65536,
                u32::MAX,
                original.saturating_sub(1),
                original.saturating_add(1),
            ] {
                let mut bytes = raw.clone();
                bytes[at..at + 4].copy_from_slice(&n.to_be_bytes());
                stats.check(&f, seed.kind, &bytes);
            }
        }
        for &at in &seed.layout.tags {
            for tag in [255u32, u32::MAX] {
                let mut bytes = raw.clone();
                bytes[at..at + 4].copy_from_slice(&tag.to_be_bytes());
                assert!(
                    !stats.check(&f, seed.kind, &bytes),
                    "unknown typed codec tag recognized"
                );
            }
        }
        for &at in &seed.layout.byte_tags {
            let mut bytes = raw.clone();
            bytes[at] = 255;
            assert!(
                !stats.check(&f, seed.kind, &bytes),
                "unknown resource bound flag recognized"
            );
        }
        for suffix in [&b"\0"[..], &b"()"[..], &b"\xff\xff\xff\xff"[..]] {
            let mut bytes = raw.clone();
            bytes.extend_from_slice(suffix);
            assert!(
                !stats.check(&f, seed.kind, &bytes),
                "trailing data recognized"
            );
        }
        for _ in 0..96 {
            let at = (noise.next() as usize) % raw.len();
            let mut bytes = raw.clone();
            bytes[at] ^= 1 << ((noise.next() % 8) as u32);
            stats.check(&f, seed.kind, &bytes);
            let end = at + ((noise.next() as usize) % ((raw.len() - at).min(8) + 1));
            let mut splice = raw.clone();
            let inserted = (noise.next() % 9) as usize;
            splice.splice(at..end, noise.bytes(inserted));
            stats.check(&f, seed.kind, &splice);
        }
    }
    for i in 0..4 {
        assert!(stats.attempted[i] > 256);
        assert!(stats.recognized[i] > 0);
        assert!(stats.rejected[i] > 128);
    }
    emit_v2_vectors(&f, &corpus, &stats);
}

#[test]
fn test_3516_native_decimal_lengths_utf8_and_nesting_are_bounded() {
    let f = Fixture::new();
    let mut stats = Stats::default();
    for bytes in [
        &b"999999999999999999999999999999:Qx"[..],
        &b"01:Sx"[..],
        &b"2:Q\xff"[..],
        &b"1:X"[..],
        &b"2:N+"[..],
        &b")"[..],
        &b"("[..],
    ] {
        assert!(!stats.check(&f, Kind::Native, bytes));
    }
    for depth in [0, 1, 63, 64, 65, 66, 128] {
        let mut bytes = vec![b'('; depth];
        bytes.extend_from_slice(b"1:Q");
        bytes.extend(vec![b')'; depth]);
        stats.check(&f, Kind::Native, &bytes);
        if depth > 64 {
            assert!(matches!(codec::decode_message(&bytes), Err(Error::Budget)));
        }
    }
    for seed in seeds(&f)
        .into_iter()
        .filter(|s| matches!(s.kind, Kind::Native))
    {
        let mut atoms = 0;
        for colon in 1..seed.bytes.len() {
            if seed.bytes[colon] != b':' || !seed.bytes[colon - 1].is_ascii_digit() {
                continue;
            }
            let mut start = colon - 1;
            while start > 0 && seed.bytes[start - 1].is_ascii_digit() {
                start -= 1;
            }
            for length in ["0", "01", "999999999999999999999999999999"] {
                let mut bytes = seed.bytes.clone();
                bytes.splice(start..colon, length.bytes());
                stats.check(&f, Kind::Native, &bytes);
            }
            atoms += 1;
            if atoms == 64 {
                break;
            }
        }
        assert!(atoms > 0);
    }
    assert!(stats.rejected[Kind::Native.index()] > 64);
}
