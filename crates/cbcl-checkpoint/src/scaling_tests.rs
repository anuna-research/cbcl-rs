//! Native fixed-context, fixed-frontier covered-message scaling fixture.
//!
//! [[SPEC-035-cached-state-checkpoints#TEST-3514]]: these are covered MESSAGES,
//! not state edits. Only `open` contributes state. Every tick has a real native
//! signature, a distinct native identity and one authenticated causal parent.
//! Eight concurrent lanes reuse fixed tick types: cuts at depths 75/750/7500
//! cover 600/6000/60000 tick messages with frontier width eight. The two-message
//! tail advances lane zero twice. All cuts use ONE installed code/context.
//! The opening-only rig has 7502 types; the combined publication rig has 7506
//! so its maintained cut can additionally admit 32 messages (four per lane).
//! Each prior client is imported with Client::from_certificate: its floor names
//! the certified cut and its retained evidence contains only the target root.
//! The covered signed archive is NOT preloaded into this client's disk store.
//! Retained-archive persistence scaling is tested separately in evidence.rs.
//! Only the small fixtures run by default; the full rig is release-only/ignored.
#![cfg(feature = "std")]

use crate::{
    certificate::{Certificate, Context, KeySigner, KeyVerifier, SignedMessage},
    hash, hex,
    host::{publish, Cache, DurableClient, Limits, Mode, Offer, Provider},
    member::{Client, Member},
    summary::Summary,
    test_support::{parse, Fixture, Keys},
    Error, Hash, Result,
};
use cbcl_core::{
    admission::{AdmissionGate, AdmissionMonitor, AdmissionState},
    canonical::{dialect_hash, dialect_name},
    dialect::{Dialect, DialectInstallError, DialectRegistry, PerformativeDef},
    message::Message,
    protocol::{CausalProtocol, NodeRef, StepDecl},
    r4::{dialect_sign_body, R4Result, Signer},
    role::{AgentKey, Endpoint},
    sexpr::{Atom, SExpr},
    shape::{ShapeConstraint, ShapeRule, TypeConstraint},
    state::{self, Entry, Rule, StateClause},
    store::ContentHash,
};
use std::{
    cell::Cell,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
    time::Instant,
};

const STACK_BYTES: usize = 64 * 1024 * 1024;

fn large_stack(f: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .name("checkpoint-native-scaling".into())
        .stack_size(STACK_BYTES)
        .spawn(f)
        .expect("spawn scaling worker")
        .join()
        .unwrap_or_else(|panic| std::panic::resume_unwind(panic));
}

fn tick_name(i: usize) -> String {
    format!("tick{i:05}")
}

/// Construct the same complete target once, never a different dialect per cut.
/// No repeat copies, All clauses, inherited history, or fabricated receipts.
fn chain_draft(ticks: usize) -> Dialect {
    assert!(ticks > 0);
    let mut d = Fixture::new().context.target().clone();
    let open = d.find_performative("open").unwrap().clone();
    let annotation = open.role.clone();
    d.performatives = vec![open];
    d.shapes.retain(|s| s.performative == "open");
    d.state = Some(StateClause {
        entries: vec![Entry::Field {
            name: "title".into(),
            rule: Rule::Initial {
                verb: "open".into(),
                key: "title".into(),
            },
        }],
    });
    d.resources.max_expansion_size = 8192; // Maximum LEGAL native R2 bound.
    let mut names = vec!["begin".to_owned(), "open".to_owned()];
    for i in 1..=ticks {
        let name = tick_name(i);
        d.performatives.push(PerformativeDef {
            name: name.clone(),
            params: vec![
                SExpr::Atom(Atom::Symbol("to".into())),
                SExpr::Atom(Atom::Symbol("lane".into())),
            ],
            template: cbcl_parser::parse("(tell to :lane lane)").unwrap(),
            role: annotation.clone(),
        });
        d.shapes.push(ShapeConstraint {
            performative: name.clone(),
            rules: vec![ShapeRule::Require {
                keyword: "lane".into(),
                type_constraint: Some(TypeConstraint::Number),
                children: vec![],
            }],
        });
        names.push(name);
    }
    d.causal_protocol = Some(CausalProtocol {
        steps: names
            .iter()
            .enumerate()
            .map(|(i, name)| {
                (
                    name.clone(),
                    StepDecl {
                        performative: name.clone(),
                        predecessors: i
                            .checked_sub(1)
                            .map(|p| NodeRef::Single(names[p].clone()))
                            .into_iter()
                            .collect(),
                        successors: names
                            .get(i + 1)
                            .map(|n| NodeRef::Single(n.clone()))
                            .into_iter()
                            .collect(),
                    },
                )
            })
            .collect(),
    });
    d.hash = None;
    d.signature = None;
    // Put selected tail types first to avoid lookup-position growth between cuts.
    // This ordering is fixed before the ONE code identity is computed.
    d.performatives.sort_by_key(|p| {
        let selected = [
            "open",
            "tick00076",
            "tick00077",
            "tick00751",
            "tick00752",
            "tick07501",
            "tick07502",
        ];
        (
            selected
                .iter()
                .position(|n| *n == p.name)
                .unwrap_or(selected.len()),
            p.name.clone(),
        )
    });
    d.name = "checkpoint-scaling-draft".into();
    d
}

struct Authority;
impl Signer for Authority {
    fn sign(&self, bytes: &[u8]) -> Vec<u8> {
        KeySigner::sign(&Keys, "@init", bytes).unwrap()
    }
    fn verify(&self, bytes: &[u8], signature: &[u8]) -> bool {
        KeyVerifier::verify(&Keys, "@init", bytes, signature)
    }
}

fn install_chain(ticks: usize) -> std::result::Result<Dialect, DialectInstallError> {
    let mut d = chain_draft(ticks);
    d.name = dialect_name(&d);
    d.signature = Some(Authority.sign(&dialect_sign_body(&d)));
    let mut registry = DialectRegistry::new();
    assert_eq!(
        registry.install_with_signer(d, &Authority)?,
        R4Result::Valid
    );
    let installed = registry.iter().last().unwrap().clone();
    assert_eq!(
        installed.hash.as_deref(),
        Some(dialect_hash(&installed).as_str())
    );
    Ok(installed)
}

fn fixture(target: Dialect) -> Fixture {
    let base = Fixture::new();
    let keys = Keys;
    let target_root = SignedMessage::sign(parse(&format!(
        "(with-roles ((member @m0 @m1 @m2 @m3)) :dialect {} (hello :sender @m0 :thread \"target\" :caused-by begin))",
        target.hash.as_ref().unwrap()
    )), "@m0", &keys).unwrap();
    let profile = Summary::expected_profile_hash_for(
        target.state.as_ref().unwrap(),
        target.causal_protocol.as_ref(),
    )
    .unwrap();
    let context = Context::new(
        target,
        target_root,
        base.context.companion_root().clone(),
        base.context.policy().clone(),
        profile,
        &keys,
    )
    .unwrap();
    let companion = cbcl_parser::checkpoint_dialect::builtin().unwrap();
    let opener = SignedMessage::sign(parse(&format!(
        "(lang {} (open (@init @m0 @m1 @m2 @m3) :target \"{}\" :context \"{}\" :policy \"{}\" :profile \"{}\" :version 1 :sender @init :thread \"checkpoint\" :caused-by \"{}\"))",
        companion.name, context.target_root().id().unwrap(), hex(&context.hash()),
        hex(&context.policy().hash()), hex(&context.profile()), context.companion_root().id().unwrap()
    )), "@init", &keys).unwrap();
    let target_open = SignedMessage::sign(parse(&format!(
        "(lang {} (open (@m0 @m1 @m2 @m3) :title \"constant\" :sender @m0 :thread \"target\" :caused-by \"{}\"))",
        context.target().name, context.target_root().id().unwrap()
    )), "@m0", &keys).unwrap();
    Fixture {
        context,
        keys,
        opener,
        target_open,
    }
}

fn tick(f: &Fixture, i: usize, parent: &str) -> SignedMessage {
    tick_lane(f, i, 0, parent)
}

fn tick_lane(f: &Fixture, i: usize, lane: usize, parent: &str) -> SignedMessage {
    SignedMessage::sign(
        parse(&format!(
            "(lang {} ({} (@m0 @m1 @m2 @m3) :lane {} :sender @m0 :thread \"target\" :caused-by \"{}\"))",
            f.context.target().name,
            tick_name(i),
            lane,
            parent
        )),
        "@m0",
        &f.keys,
    )
    .unwrap()
}

/// The timed opener receives ONLY the certificate. It has no target-history or
/// companion-history provider API. Finite target dependencies are in the offer.
struct CertificateOnly {
    id: Hash,
    bytes: Vec<u8>,
    requests: usize,
    fetched: usize,
}
impl Provider for CertificateOnly {
    fn get(&mut self, id: Hash, max: usize, deadline: Instant) -> Result<Vec<u8>> {
        self.requests += 1;
        if id != self.id {
            return Err(Error::Invalid("scaling opener attempted history fetch"));
        }
        if Instant::now() >= deadline {
            return Err(Error::Cancelled);
        }
        if self.bytes.len() > max {
            return Err(Error::Budget);
        }
        self.fetched += self.bytes.len();
        Ok(self.bytes.clone())
    }
}

struct Temp(PathBuf);
impl Temp {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "cbcl-native-scaling-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }
}
impl Drop for Temp {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

struct NativeGate;
impl AdmissionGate for NativeGate {
    fn authenticate(&self, m: &Message) -> std::result::Result<ContentHash, String> {
        let signed = SignedMessage::from_message(m.clone());
        signed.authenticate(&Keys).map_err(|e| e.to_string())?;
        signed.id().map(ContentHash).map_err(|e| e.to_string())
    }
}

#[derive(Default)]
struct OpenKeys {
    signatures: Cell<usize>,
    signed_preimage_bytes: Cell<usize>,
}
impl KeyVerifier for OpenKeys {
    fn verify(&self, key: &str, preimage: &[u8], signature: &[u8]) -> bool {
        self.signatures.set(self.signatures.get() + 1);
        self.signed_preimage_bytes
            .set(self.signed_preimage_bytes.get() + preimage.len());
        KeyVerifier::verify(&Keys, key, preimage, signature)
    }
}

fn admit_tick(
    f: &Fixture,
    message: &SignedMessage,
    members: &mut [Member],
    oracle: &mut AdmissionMonitor<NativeGate>,
    acts: &mut Vec<state::Act>,
) -> String {
    for member in members {
        member.accept(message, &f.context, &f.keys).unwrap();
    }
    oracle.receive(message.message().clone()).unwrap();
    oracle.drain_ready();
    let id = message.id().unwrap();
    assert_eq!(
        oracle.state(&ContentHash(id.clone())),
        Some(&AdmissionState::Accepted)
    );
    acts.push(message.authenticate(&f.keys).unwrap());
    id
}

#[cfg(unix)]
fn thread_cpu_ns() -> u128 {
    let time = rustix::time::clock_gettime(rustix::time::ClockId::ThreadCPUTime);
    u128::try_from(time.tv_sec).unwrap() * 1_000_000_000 + u128::try_from(time.tv_nsec).unwrap()
}

/// One maintained native oracle and three independently deriving members.
/// Construction, native full-history admission and certificate publication are
/// outside open timing. Every cut uses the identical installed target/context.
fn exercise(prefixes: &[usize], total_ticks: usize, repetitions: usize) {
    exercise_lanes(prefixes, total_ticks, repetitions, 1);
}

fn exercise_lanes(prefixes: &[usize], total_ticks: usize, repetitions: usize, lanes: usize) {
    exercise_lanes_with_publication(prefixes, total_ticks, repetitions, lanes, false);
}

fn exercise_lanes_with_publication(
    prefixes: &[usize],
    total_ticks: usize,
    repetitions: usize,
    lanes: usize,
    publication: bool,
) {
    assert!(lanes > 0 && repetitions > 0);
    let setup = Instant::now();
    let target = install_chain(total_ticks)
        .unwrap_or_else(|e| panic!("native scaling fixture is BLOCKED, not accepted: {e}"));
    let f = fixture(target);
    let context = f.context.hash();
    let code = f.context.target().hash.clone();
    let mut members: Vec<_> = (0..3)
        .map(|i| {
            let mut m = Member::new(&f.context, &format!("@m{i}"), &f.keys).unwrap();
            m.accept(&f.target_open, &f.context, &f.keys).unwrap();
            m
        })
        .collect();
    let mut oracle = AdmissionMonitor::new(
        f.context.target().clone(),
        Endpoint {
            role: "member".into(),
            occupant: Some(AgentKey("@m0".into())),
        },
        f.context.target_root().message().clone(),
        NativeGate,
    )
    .unwrap();
    oracle.drain_ready();
    oracle.receive(f.target_open.message().clone()).unwrap();
    oracle.drain_ready();
    let mut acts = vec![
        f.context.target_root().authenticate(&f.keys).unwrap(),
        f.target_open.authenticate(&f.keys).unwrap(),
    ];
    let expected_render = members[0].client().summary.render();
    let expected_summary = members[0].client().summary.encode();
    let mut depths = vec![0; lanes];
    let mut parents = vec![f.target_open.id().unwrap(); lanes];
    let mut certificate_size = None;
    let mut offer_size = None;
    let mut signature_work = None;
    #[cfg(unix)]
    let mut cpu_medians = Vec::new();
    println!(
        "native-scaling setup_context_us={} tick_types={} lanes={} target_root={} companion_root={} context={} code={} covered_messages_not_state_edits=true",
        setup.elapsed().as_micros(),
        total_ticks, lanes, f.context.target_root().id().unwrap(), f.context.companion_root().id().unwrap(), hex(&context), code.as_deref().unwrap()
    );
    for &prefix in prefixes {
        assert_eq!(prefix % lanes, 0);
        let depth = prefix / lanes;
        assert!(depth + 2 <= total_ticks && depths.iter().all(|d| *d <= depth));
        let admission_start = Instant::now();
        for lane in 0..lanes {
            while depths[lane] < depth {
                let i = depths[lane] + 1;
                let message = tick_lane(&f, i, lane, &parents[lane]);
                parents[lane] = admit_tick(&f, &message, &mut members, &mut oracle, &mut acts);
                depths[lane] = i;
            }
        }
        assert_eq!(depths.iter().sum::<usize>(), prefix);
        assert_eq!(acts.len(), prefix + 2); // Shared target root and opener.
        println!(
            "native-scaling coveredMessages={prefix} background_admit_and_oracle_us={}",
            admission_start.elapsed().as_micros()
        );
        let cert: Certificate = f.certificate(&members);
        assert_eq!(cert.manifest.frontier.len(), lanes);
        assert_eq!(cert.summary, expected_summary);
        let previous = Client::from_certificate(&f.context, &cert, &f.keys).unwrap();
        let floor = previous.floor();
        let mut tail = Vec::new();
        for _ in 0..2 {
            let i = depths[0] + 1;
            let message = tick_lane(&f, i, 0, &parents[0]);
            tail.push(members[0].step(&message).unwrap());
            parents[0] = admit_tick(&f, &message, &mut members, &mut oracle, &mut acts);
            depths[0] = i;
        }
        // Oracle is evaluated outside timing and is not passed into the opener.
        assert_eq!(
            state::fold(
                f.context.target().state.as_ref().unwrap(),
                f.context.target().causal_protocol.as_ref(),
                &acts
            ),
            expected_render
        );
        let mut expected_frontier = parents.clone();
        expected_frontier.sort();
        assert_eq!(members[0].client().frontier, expected_frontier);
        for member in &members {
            assert_eq!(member.coverage().root(), members[0].coverage().root());
            assert_eq!(member.client().frontier, expected_frontier);
            assert_eq!(member.client().summary.encode(), expected_summary);
        }
        let bytes = cert.encode(&f.context);
        let blob = hash(b"cbcl/checkpoint/blob/v1", &bytes);
        let offer = Offer {
            blob,
            tail,
            floor_proofs: floor
                .frontier
                .iter()
                .map(|id| (id.clone(), members[0].coverage().proof(id)))
                .collect(),
        };
        let wire = offer.encode();
        assert_eq!(*certificate_size.get_or_insert(bytes.len()), bytes.len());
        assert_eq!(*offer_size.get_or_insert(wire.len()), wire.len());
        assert_eq!(context, f.context.hash());
        assert_eq!(code, f.context.target().hash);
        let existing_blobs = previous
            .evidence
            .iter()
            .map(|(_, message)| hash(b"cbcl/checkpoint/blob/v1", &message.encode()))
            .collect::<std::collections::BTreeSet<_>>();
        let mut new_bodies = std::collections::BTreeMap::new();
        for message in offer.tail.iter().flat_map(|step| {
            std::iter::once(&step.message).chain(step.ancestry.iter().map(|(message, _)| message))
        }) {
            let encoded = message.encode();
            let blob = hash(b"cbcl/checkpoint/blob/v1", &encoded);
            if !existing_blobs.contains(&blob) {
                new_bodies.insert(blob, encoded.len());
            }
        }
        for member in &mut members {
            member.reset_work();
        }
        let mut walls = Vec::new();
        #[cfg(unix)]
        let mut cpus = Vec::new();
        for repetition in 0..repetitions {
            let temp = Temp::new();
            let mut disk = DurableClient::create(&temp.0, previous.clone(), Mode::Enabled).unwrap();
            let mut provider = CertificateOnly {
                id: blob,
                bytes: bytes.clone(),
                requests: 0,
                fetched: 0,
            };
            let open_keys = OpenKeys::default();
            let start = Instant::now();
            #[cfg(unix)]
            let cpu_start = thread_cpu_ns();
            let prepared = disk
                .prepare(
                    &mut provider,
                    std::slice::from_ref(&wire),
                    &f.context,
                    &open_keys,
                    &Limits::default(),
                )
                .unwrap();
            let metrics = disk.install(prepared).unwrap();
            #[cfg(unix)]
            let cpu_elapsed = thread_cpu_ns() - cpu_start;
            let wall = start.elapsed();
            let persist = disk.last_persist_work();
            assert_eq!(
                persist.value_encodes,
                new_bodies.len(),
                "warm install must encode only newly retained signed bodies"
            );
            assert_eq!(persist.value_bytes, new_bodies.values().sum::<usize>());
            println!("native-persist coveredMessages={prefix} repetition={repetition} expected_new_bodies={} persist_work={}", new_bodies.len(),
                serde_json::json!({"trusted_checks":persist.trusted_checks,"new_nodes":persist.new_nodes,
                    "node_bytes":persist.node_bytes,"value_encodes":persist.value_encodes,"value_bytes":persist.value_bytes}));
            #[cfg(unix)]
            {
                cpus.push(cpu_elapsed);
                println!("native-scaling coveredMessages={prefix} repetition={repetition} thread_cpu_ns={cpu_elapsed}");
            }
            let render_start = Instant::now();
            assert_eq!(disk.client().summary.render(), expected_render);
            let render = render_start.elapsed();
            assert_eq!(disk.client().coverage, members[0].coverage().root());
            assert_eq!(disk.client().frontier, expected_frontier);
            assert_eq!(provider.requests, 1);
            assert_eq!(provider.fetched, bytes.len());
            assert_eq!(metrics.tail_steps, 2);
            assert_eq!(offer.floor_proofs.len(), lanes);
            assert_eq!(
                offer.tail.iter().map(|s| s.ancestry.len()).sum::<usize>(),
                2
            );
            assert_eq!(metrics.proof_paths, lanes + 4);
            assert_eq!(
                *signature_work.get_or_insert(open_keys.signatures.get()),
                open_keys.signatures.get()
            );
            walls.push(wall.as_nanos());
            println!("native-scaling coveredMessages={prefix} repetition={repetition} frontier={} wall_ns={} render_ns={} certificate_bytes={} offer_bytes={} tail_signed_bytes={} dependency_signed_bytes={} floor_bytes={} finite_dependency_bodies={} proof_paths={} signatures_checked={} signed_preimage_bytes={} metrics={}",
                lanes,
                wall.as_nanos(), render.as_nanos(), bytes.len(), wire.len(),
                offer.tail.iter().map(|s| s.message.encode().len()).sum::<usize>(),
                offer.tail.iter().flat_map(|s| &s.ancestry).map(|(m, _)| m.encode().len()).sum::<usize>(),
                offer.floor_proofs.iter().map(|(id, _)| 4 + id.len() + 8 + 256 * 32).sum::<usize>(),
                offer.tail.iter().map(|s| s.ancestry.len()).sum::<usize>(),
                offer.floor_proofs.len() + offer.tail.iter().map(|s| 1 + s.ancestry.len() + s.replacements.len()).sum::<usize>(),
                open_keys.signatures.get(), open_keys.signed_preimage_bytes.get(),
                serde_json::to_string(&metrics).unwrap());
        }
        walls.sort();
        #[cfg(unix)]
        {
            cpus.sort();
            let median = cpus[cpus.len() / 2];
            cpu_medians.push(median);
            println!("native-scaling coveredMessages={prefix} median_thread_cpu_ns={median}");
        }
        println!(
            "native-scaling coveredMessages={prefix} median_wall_ns={}",
            walls[walls.len() / 2]
        );
        for member in &members {
            let work = member.work();
            assert_eq!(work.prefix_reconstruction_body_reads, 0);
            assert_eq!(work.snapshot_body_records, 0);
            assert_eq!(
                work.dependency_body_lookups, 0,
                "foreground must use supplied finite openings"
            );
        }
        println!(
            "native-opening-work coveredMessages={prefix} member_archive_work={}",
            serde_json::to_string(&members.iter().map(Member::work).collect::<Vec<_>>()).unwrap()
        );
        if publication {
            publish_delta32(
                &f,
                prefix,
                &mut members,
                &mut parents,
                &mut depths,
                &mut oracle,
                &mut acts,
            );
        }
    }
    #[cfg(unix)]
    if prefixes == [600, 6000, 60000] {
        let ratio = cpu_medians[2] as f64 / cpu_medians[0] as f64;
        println!("native-scaling provisional_median_thread_cpu_ratio={ratio:.6} cpu_medians_ns={cpu_medians:?} member_archive_work=checked");
        assert!(
            cpu_medians[2] <= cpu_medians[0] * 2,
            "provisional CPU target exceeded: largest/smallest={ratio:.6}"
        );
    }
    #[cfg(not(unix))]
    println!("native-scaling cpu_target=unverified clock=wall_only");
}

/// Entire maintained-member delta -> freeze -> independent endorsements ->
/// durable immutable publication. Full native replay oracle runs OUTSIDE timing.
fn publish_delta32(
    f: &Fixture,
    prefix: usize,
    members: &mut [Member],
    parents: &mut Vec<String>,
    depths: &mut Vec<usize>,
    oracle: &mut AdmissionMonitor<NativeGate>,
    acts: &mut Vec<state::Act>,
) {
    assert_eq!(parents.len(), 8);
    let total_ticks = f
        .context
        .target()
        .causal_protocol
        .as_ref()
        .unwrap()
        .expansion_size() as usize
        - 1;
    let generation = Instant::now();
    let mut new_parents = parents.clone();
    let mut new_depths = depths.clone();
    let mut messages = Vec::new();
    for lane in 0..8 {
        for _ in 0..4 {
            new_depths[lane] += 1;
            assert!(new_depths[lane] <= total_ticks);
            let message = tick_lane(f, new_depths[lane], lane, &new_parents[lane]);
            new_parents[lane] = message.id().unwrap();
            messages.push(message);
        }
    }
    let generate_us = generation.elapsed().as_micros();
    assert_eq!(messages.len(), 32);
    for member in members.iter_mut() {
        member.reset_work();
    }
    let total = Instant::now();
    let phase = Instant::now();
    for message in &messages {
        for member in members.iter_mut() {
            member.accept(message, &f.context, &f.keys).unwrap();
        }
    }
    let admission_us = phase.elapsed().as_micros();
    let phase = Instant::now();
    let manifests = members
        .iter()
        .map(|m| m.manifest(&f.context).unwrap())
        .collect::<Vec<_>>();
    assert!(manifests.iter().all(|m| *m == manifests[0]));
    let freeze_us = phase.elapsed().as_micros();
    let phase = Instant::now();
    let endorsements = members
        .iter()
        .map(|m| f.endorsement(m, &manifests[0]))
        .collect();
    let cert = Certificate {
        manifest: manifests[0].clone(),
        summary: members[0].client().summary.encode(),
        opener: f.opener.clone(),
        endorsements,
    };
    let endorsement_us = phase.elapsed().as_micros();
    let temp = Temp::new();
    let cache = Cache::open(temp.0.join("published")).unwrap();
    let raw = cert.encode(&f.context);
    let expected_blob = hash(b"cbcl/checkpoint/blob/v1", &raw);
    let phase = Instant::now();
    let mut before_advertise_us = None;
    let mut readback_us = None;
    let blob = publish(&cache, &cert, &f.context, &f.keys, |blob| {
        before_advertise_us = Some(phase.elapsed().as_micros());
        let readback = Instant::now();
        assert_eq!(blob, expected_blob);
        assert_eq!(
            cache.read_once(blob, Limits::default().certificate_bytes)?,
            raw
        );
        readback_us = Some(readback.elapsed().as_micros());
        Ok(())
    })
    .unwrap();
    let publish_us = phase.elapsed().as_micros();
    let total_us = total.elapsed().as_micros();
    assert_eq!(blob, expected_blob);
    assert!(before_advertise_us.is_some());
    let work = members.iter().map(Member::work).collect::<Vec<_>>();
    for w in &work {
        assert_eq!(w.prefix_reconstruction_body_reads, 0);
        assert_eq!(w.snapshot_body_records, 0);
        assert_eq!(
            w.dependency_body_lookups, 32,
            "one finite accepted-parent lookup per delta message/member"
        );
    }
    println!("native-publication checkpointCoveredMessages={prefix} baseCoveredMessages={} delta=32 generate_signed_us={generate_us} admit_and_summary_us={admission_us} freeze_us={freeze_us} independently_endorse_us={endorsement_us} verify_store_and_directory_sync_us={} readback_advertise_us={} publish_us={publish_us} maintained_to_publication_us={total_us} certificate_bytes={} work={}",
        prefix + 2, before_advertise_us.unwrap(), readback_us.unwrap(), raw.len(), serde_json::to_string(&work).unwrap());
    // The native monitor is an independently admitted full-history oracle; it
    // and the full fold do not enter any publication/open timing interval.
    for message in messages {
        oracle.receive(message.message().clone()).unwrap();
        oracle.drain_ready();
        assert_eq!(
            oracle.state(&ContentHash(message.id().unwrap())),
            Some(&AdmissionState::Accepted)
        );
        acts.push(message.authenticate(&f.keys).unwrap());
    }
    assert_eq!(
        members[0].client().summary.render(),
        state::fold(
            f.context.target().state.as_ref().unwrap(),
            f.context.target().causal_protocol.as_ref(),
            acts
        )
    );
    *parents = new_parents;
    *depths = new_depths;
    // Actual whole-prefix replay exercises the very same archive counters.
    // Keep the negative control small; the depth run measures steady-state work.
    if prefix <= 600 {
        assert_eq!(
            members[0].audit_replay(&f.context, &f.keys).unwrap(),
            manifests[0]
        );
        assert!(
            members[0].work().prefix_reconstruction_body_reads > 0,
            "whole-prefix negative control must make the no-reconstruction assertion fail"
        );
    }
}

#[test]
fn native_eight_lane_small_delta32_publication_work() {
    large_stack(|| exercise_lanes_with_publication(&[48, 192, 368], 54, 1, 8, true));
}

#[test]
#[ignore = "release-only native publication depth rig"]
fn native_eight_lane_600_6000_60000_delta32_publication_work() {
    #[cfg(debug_assertions)]
    panic!("do not run the 60000-message rig in debug mode");
    #[cfg(not(debug_assertions))]
    large_stack(|| exercise_lanes_with_publication(&[600, 6000, 60000], 7506, 3, 8, true));
}

#[test]
fn native_eight_lane_48_depth_fixed_context_full_open() {
    large_stack(|| exercise_lanes(&[48, 192, 368], 48, 1, 8));
}

#[test]
#[ignore = "release-only native depth rig: explicitly run with --release --ignored --nocapture"]
fn native_eight_lane_600_6000_60000_full_open() {
    #[cfg(debug_assertions)]
    panic!("do not run the 60000-message rig in debug mode");
    #[cfg(not(debug_assertions))]
    large_stack(|| exercise_lanes(&[600, 6000, 60000], 7502, 3, 8));
}

#[test]
fn native_48_tick_fixed_context_chain_opens_tail_floor_and_durable_generation() {
    large_stack(|| exercise(&[6, 24, 46], 48, 1));
}

#[test]
fn native_48_tick_definition_installs_and_constructs_validated_context() {
    large_stack(|| {
        let target = install_chain(48).expect("48-tick native R1-R7/R4 installation");
        let protocol = target.causal_protocol.as_ref().unwrap();
        assert_eq!(protocol.expansion_size(), 49); // open plus 48 ticks.
        assert!(protocol.steps.keys().all(|name| !name.contains('#')));
        assert!(protocol.steps.values().all(|step| step
            .predecessors
            .iter()
            .chain(&step.successors)
            .all(|node| !matches!(node, NodeRef::All(_)))));
        let f = fixture(target); // Calls the real Context::new factory.
        crate::member::validate_profile(&f.context).unwrap();
        let mut member = Member::new(&f.context, "@m0", &f.keys).unwrap();
        member.accept(&f.target_open, &f.context, &f.keys).unwrap();
        let context = f.context.hash();
        let mut parent = f.target_open.id().unwrap();
        for i in 1..=48 {
            let message = tick(&f, i, &parent);
            member.accept(&message, &f.context, &f.keys).unwrap();
            parent = message.id().unwrap();
            assert_eq!(member.client().frontier, vec![parent.clone()]);
            assert_eq!(f.context.hash(), context);
        }
        assert_eq!(
            member.client().summary.render_json(),
            "{\"title\":\"constant\"}"
        );
    });
}
