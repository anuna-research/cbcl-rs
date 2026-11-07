//! Prototype P1–P6: semantic differential checks and dishonest circuit witnesses.
use crate::*;
use cbcl_core::{
    attest::sign_attestation_v2,
    equivocation::attestation_header_for,
    message::Message,
    r4::Signer,
    serializer::serialize,
    sexpr::SExpr,
    state::{fold, render_json, Act},
};
use cbcl_parser::{parse, parse_and_install_dialect, parse_message};
use ff::Field;
use halo2_proofs::dev::MockProver;
use serde_json::Value as Json;

pub(crate) fn fixture() -> (String, String, Vec<Candidate>) {
    let v: Json = serde_json::from_str(include_str!(
        "../../../test-vectors/state/signer-supersession.json"
    ))
    .unwrap();
    let candidates = v["messages"].as_array().unwrap()[..3]
        .iter()
        .map(|m| {
            Candidate::unauthenticated(
                m["canonical"].as_str().unwrap().into(),
                m["signer"].as_str().unwrap().into(),
            )
        })
        .collect();
    (
        v["contract"].as_str().unwrap().into(),
        "s1".into(),
        candidates,
    )
}
fn address(c: &Candidate) -> String {
    Act::from_message(parse_message(&parse(c.text()).unwrap()).unwrap(), c.label())
        .unwrap()
        .address
}
/// Same text, new label.
fn relabel(c: &Candidate, label: &str) -> Candidate {
    Candidate::unauthenticated(c.text().into(), label.into())
}
/// Same label, new text.
fn retext(c: &Candidate, text: String) -> Candidate {
    Candidate::unauthenticated(text, c.label().into())
}
pub(crate) fn masks(p: &Profile, c: &[Candidate]) -> (u16, u16) {
    (
        p.mask(&[&address(&c[0]), &address(&c[1])]).unwrap(),
        p.mask(
            &c.iter()
                .map(address)
                .collect::<Vec<_>>()
                .iter()
                .map(String::as_str)
                .collect::<Vec<_>>(),
        )
        .unwrap(),
    )
}
fn raw_statement(p: &Profile, before: u16, after: u16) -> Statement {
    Statement {
        profile: p.id(),
        before: p.rows[before as usize].checkpoint,
        after: p.rows[after as usize].checkpoint,
        batch: p.rows[(after & !before) as usize].checkpoint.accepted,
    }
}
fn mock(p: &Profile, before: u16, after: u16, statement: &Statement) -> bool {
    let c = StateCircuit::witness(p, before, after);
    MockProver::run(c.k(), &c, vec![statement.instance()])
        .unwrap()
        .verify()
        .is_ok()
}
/// Accepted, distinct messages of a state fixture, with its dialect and thread.
pub(crate) fn corpus(text: &str) -> (String, String, Vec<Candidate>) {
    let v: Json = serde_json::from_str(text).unwrap();
    let mut candidates = Vec::new();
    let mut seen = std::collections::BTreeSet::new();
    for m in v["messages"].as_array().unwrap() {
        let c = Candidate::unauthenticated(
            m["canonical"].as_str().unwrap().into(),
            m["signer"].as_str().unwrap().into(),
        );
        let id = address(&c);
        if v["expect"]["verdicts"][&id] == "accepted" && seen.insert(id) {
            candidates.push(c);
        }
    }
    (
        v["contract"].as_str().unwrap().into(),
        v["thread"].as_str().unwrap().into(),
        candidates,
    )
}
/// REQ-3501: every valid subset's state JSON is the native fold of that subset.
fn assert_native_parity(source: &str, thread: &str, c: &[Candidate]) {
    let p = Profile::compile(source, thread, c).unwrap();
    let registry = parse_and_install_dialect(&parse(source).unwrap()).unwrap();
    let d = registry.iter().last().unwrap();
    let mut valid = 0;
    for mask in 0..p.rows.len() {
        if p.checkpoint(mask as u16).is_err() {
            continue;
        }
        valid += 1;
        let acts: Vec<_> = c
            .iter()
            .filter(|c| mask & p.mask(&[&address(c)]).unwrap() as usize != 0)
            .map(|c| {
                Act::from_message(parse_message(&parse(c.text()).unwrap()).unwrap(), c.label())
                    .unwrap()
            })
            .collect();
        assert_eq!(
            p.state_json(mask as u16).unwrap(),
            render_json(&fold(
                d.state.as_ref().unwrap(),
                d.causal_protocol.as_ref(),
                &acts
            ))
        );
    }
    assert!(valid > 1, "fixture has only the empty valid set");
}
#[test]
fn native_fold_and_replacement_match_for_every_valid_subset() {
    let (source, thread, c) = fixture();
    assert_native_parity(&source, &thread, &c);
    let p = Profile::compile(&source, &thread, &c).unwrap();
    let (old, new) = masks(&p, &c);
    let state: Json = serde_json::from_str(p.state_json(new).unwrap()).unwrap();
    assert_eq!(state["entries"]["@a"], "new");
    assert!(mock(&p, old, new, &p.statement(old, new).unwrap()));
}
#[test]
fn reordered_candidates_and_child_before_opener_use_the_same_relation() {
    let (source, thread, mut c) = fixture();
    let p = Profile::compile(&source, &thread, &c).unwrap();
    c.reverse();
    let q = Profile::compile(&source, &thread, &c).unwrap();
    assert_eq!(p.id(), q.id());
    assert_eq!(p.addresses(), q.addresses());
    assert_eq!(p.transitions, q.transitions);
    let root = p.mask(&[&address(c.last().unwrap())]).unwrap();
    // Derive the opener position from the native identity; hash ordering may
    // change when the pinned kernel or typed message identity changes.
    assert_eq!(root.count_ones(), 1);
    assert!(p.statement(0, root).is_ok());
    assert!(mock(&p, 0, 7, &p.statement(0, 7).unwrap()));
}
#[test]
fn pending_message_cannot_enter_committed_set_even_when_precheck_is_bypassed() {
    let (s, t, c) = fixture();
    let p = Profile::compile(&s, &t, &c).unwrap();
    let child = p.mask(&[&address(&c[1])]).unwrap();
    assert!(p.statement(0, child).is_err());
    assert!(!mock(&p, 0, child, &raw_statement(&p, 0, child)));
}
#[test]
fn invalid_shape_sender_thread_and_dialect_are_constrained() {
    let (s, t, c) = fixture();
    for mode in [
        "shape",
        "sender",
        "sender-field",
        "two-from",
        "thread",
        "dialect",
    ] {
        let mut candidates = c[..2].to_vec();
        match mode {
            "shape" => {
                let text = candidates[1].text().replace(":value \"old\"", ":value 42");
                candidates[1] = retext(&candidates[1], text);
            }
            "sender" => candidates[1] = relabel(&candidates[1], "@impostor"),
            // REQ-3512 (c): `:sender` present and different from the label.
            "sender-field" => {
                let text = with_sender(candidates[1].text(), "@impostor");
                candidates[1] = retext(&candidates[1], text);
            }
            // REQ-3512 (c): two `:from` fields are ambiguous.
            "two-from" => {
                let text = candidates[1]
                    .text()
                    .replace(":from @a", ":from @a :from @a");
                candidates[1] = retext(&candidates[1], text);
            }
            "thread" => {
                let text = candidates[1].text().replace("\"s1\"", "\"other\"");
                candidates[1] = retext(&candidates[1], text);
            }
            "dialect" => {
                let text = candidates[1]
                    .text()
                    .replace("lang signer-register", "lang other");
                candidates[1] = retext(&candidates[1], text);
            }
            _ => unreachable!(),
        }
        let p = Profile::compile(&s, &t, &candidates).unwrap();
        assert!(p.statement(0, 3).is_err(), "{mode}");
        assert!(!mock(&p, 0, 3, &raw_statement(&p, 0, 3)), "{mode}");
    }
}
#[test]
fn grow_only_and_exact_delta_are_circuit_obligations() {
    let (s, t, c) = fixture();
    let p = Profile::compile(&s, &t, &c).unwrap();
    let (old, new) = masks(&p, &c);
    assert!(!mock(&p, new, old, &raw_statement(&p, new, old)));
    let mut statement = p.statement(old, new).unwrap();
    statement.batch = p.rows[new as usize].checkpoint.accepted;
    assert!(!mock(&p, old, new, &statement));
    assert!(mock(&p, new, new, &p.statement(new, new).unwrap()));
}
#[test]
fn every_public_limb_is_constrained_without_the_host_precheck() {
    let (s, t, c) = fixture();
    let p = Profile::compile(&s, &t, &c).unwrap();
    let (old, new) = masks(&p, &c);
    let circuit = StateCircuit::witness(&p, old, new);
    for i in 0..12 {
        let mut public = p.statement(old, new).unwrap().instance();
        public[i] += halo2_proofs::pasta::Fp::ONE;
        assert!(
            MockProver::run(circuit.k(), &circuit, vec![public])
                .unwrap()
                .verify()
                .is_err(),
            "public limb {i}"
        );
    }
}
#[test]
fn previous_context_relation_is_enforced_independently_of_snapshot_and_growth_checks() {
    let (s, t, c) = fixture();
    let mut p = Profile::compile(&s, &t, &c).unwrap();
    let (old, new) = masks(&p, &c);
    let statement = p.statement(old, new).unwrap();
    // Remove this transition from the trusted compiled relation only. The
    // endpoints remain valid, grow-only, with otherwise correct public roots.
    p.transitions
        .retain(|pair| *pair != (old as usize, new as usize));
    let mut dishonest = StateCircuit::witness(&p, old, new);
    dishonest.forge_transition_sum = true;
    assert!(
        MockProver::run(dishonest.k(), &dishonest, vec![statement.instance()])
            .unwrap()
            .verify()
            .is_err()
    );
}
#[test]
fn candidate_and_parser_limits_fail_closed() {
    let (s, t, c) = fixture();
    assert!(
        Profile::compile(&s, &t, &vec![c[0].clone(); MAX_CANDIDATES + 1])
            .unwrap_err()
            .contains("limit")
    );
    assert!(Profile::compile(&s, &t, &[c[0].clone(), c[0].clone()])
        .unwrap_err()
        .contains("duplicate"));
    let nested = format!("{}{}", "(".repeat(10000), ")".repeat(10000));
    assert!(Profile::compile(&nested, &t, &[]).is_err());
    let bad = retext(&c[0], format!("{}{}", "(".repeat(3000), ")".repeat(3000)));
    assert!(Profile::compile(&s, &t, &[bad]).is_err());
    assert!(Profile::compile(&format!("{s} trailing"), &t, &c).is_err());
    let trailing = retext(&c[0], format!("{} trailing", c[0].text()));
    assert!(Profile::compile(&s, &t, &[trailing]).is_err());
    let p = Profile::compile(&s, &t, &[]).unwrap();
    assert!(mock(&p, 0, 0, &p.statement(0, 0).unwrap()));
}
#[test]
fn canonical_whitespace_and_unknown_candidates() {
    let (s, t, mut c) = fixture();
    let p = Profile::compile(&s, &t, &c).unwrap();
    for c in &mut c {
        // Reserialised through the typed message, then extra spaces and
        // newlines between tokens (REQ-3506 d); no fixture string contains a
        // space, so the message is unchanged.
        let text = serialize(&SExpr::from(
            &parse_message(&parse(c.text()).unwrap()).unwrap(),
        ))
        .replace(' ', " \n  ")
        .replace("((", "( (");
        assert_ne!(text, c.text());
        assert!(text.contains('\n'));
        *c = retext(c, text);
    }
    let q = Profile::compile(&s, &t, &c).unwrap();
    assert_eq!(p.id(), q.id());
    assert!(p.mask(&["sha256-unknown"]).is_err());
    assert!(p.checkpoint(8).is_err());
}
#[test]
fn actual_proof_roundtrip_tampering_and_independent_verifier() {
    let (s, t, c) = fixture();
    let p = Profile::compile(&s, &t, &c).unwrap();
    let (old, new) = masks(&p, &c);
    let expected = p.statement(old, new).unwrap();
    let prover = Prover::new(p).unwrap();
    let proof = prover.prove(old, new).unwrap();
    let verifier = Verifier::new(Profile::compile(&s, &t, &c).unwrap()).unwrap();
    let encoded = proof.to_json().unwrap();
    let proof = Proof::from_json(&encoded).unwrap();
    verifier.verify(&proof, &expected).unwrap();
    let stale_profile = Profile::compile(&s, &t, &c)
        .unwrap()
        .id_with_domain(&profile::relation_domain("c9093e8"));
    let mut stale = proof.clone();
    stale.statement.profile = stale_profile;
    assert!(
        verifier.verify(&stale, &stale.statement).is_err(),
        "even a matching stale caller expectation cannot bypass the pinned verifier profile"
    );
    // CON-3506: two proofs of one statement differ and both verify.
    let second = prover.prove(old, new).unwrap();
    assert_eq!(second.statement, expected);
    assert_ne!(second.transcript, proof.transcript);
    verifier.verify(&second, &expected).unwrap();
    // REQ-3502 (b): a foreign-profile expectation is rejected on the early path.
    let mut foreign = expected.clone();
    foreign.profile[0] ^= 1;
    let err = verifier.verify(&proof, &foreign).unwrap_err();
    assert!(err.contains("unexpected checkpoint statement"), "{err}");
    let err = verifier.verify(&second, &expected.clone()).err();
    assert_eq!(err, None);
    for field in 0..6 {
        let mut forged = proof.clone();
        let root = match field {
            0 => &mut forged.statement.profile,
            1 => &mut forged.statement.before.accepted,
            2 => &mut forged.statement.before.state,
            3 => &mut forged.statement.after.accepted,
            4 => &mut forged.statement.after.state,
            _ => &mut forged.statement.batch,
        };
        root[0] ^= 1;
        // Supply the forged roots as the expectation too: tests backend binding,
        // not merely equality between package and caller-owned statement.
        assert!(
            verifier.verify(&forged, &forged.statement).is_err(),
            "root {field}"
        );
    }
    let mut corrupt = proof.clone();
    corrupt.transcript[0] ^= 1;
    assert!(verifier.verify(&corrupt, &expected).is_err());
    for trim in [true, false] {
        let mut bad = proof.clone();
        if trim {
            bad.transcript.truncate(bad.transcript.len() - 32);
        } else {
            bad.transcript.extend([0; 32]);
        }
        assert!(verifier.verify(&bad, &expected).is_err());
    }
    let altered = Profile::compile(&s, &t, &c[..2]).unwrap();
    let another = Verifier::new(altered).unwrap();
    assert!(another.verify(&proof, &expected).is_err());
    let mut package: Json = serde_json::from_slice(&encoded).unwrap();
    package["unknown"] = Json::Bool(true);
    assert!(Proof::from_json(&serde_json::to_vec(&package).unwrap()).is_err());
    assert!(Proof::from_json(&vec![b' '; MAX_PACKAGE + 1]).is_err());
    assert!(Proof::from_json(&[encoded.as_slice(), b"x"].concat()).is_err());
    let pending = Profile::compile(&s, &t, &c)
        .unwrap()
        .mask(&[&address(&c[1])])
        .unwrap();
    assert!(prover.prove(0, pending).is_err()); // child without its opener
}

#[test]
fn complete_native_corpus_snapshots_match_recorded_results() {
    for text in [
        include_str!("../../../test-vectors/state/signer-supersession.json"),
        include_str!("../../../test-vectors/state/lunch-vote-domain.json"),
    ] {
        let v: Json = serde_json::from_str(text).unwrap();
        let (source, thread, candidates) = corpus(text);
        let p = Profile::compile(&source, &thread, &candidates).unwrap();
        let all = (1 << candidates.len()) - 1;
        let actual: Json = serde_json::from_str(p.state_json(all).unwrap()).unwrap();
        assert_eq!(actual, v["expect"]["state"]);
        assert!(mock(&p, 0, all, &p.statement(0, all).unwrap()));
    }
}

#[test]
fn register_deletion_preserves_history_and_unseen_concurrent_write() {
    use cbcl_core::sexpr::Atom;
    let json = serde_json::json!({"version":3,"kind":"contract","name":"proof-register", "verbs": {
        "open":{"after":["begin"],"fields":{"title":"string"}},
        "put":{"after":["open"],"fields":{"slot":"string","value":"string","clock":"hlc"}},
        "unset":{"after":["open"],"fields":{"slot":"string"}}
    },"state":{"properties":["lwwMap","put","slot","value","clock","unset"],"conflicts":["valuesPerKey","put","slot","value","unset"]}});
    let compiled: Json =
        serde_json::from_str(&cbcl_parser::compile_contract_str(&json.to_string()).unwrap())
            .unwrap();
    let name = compiled["name"].as_str().unwrap();
    let source = compiled["dialect"].as_str().unwrap();
    let symbol = |s: &str| SExpr::Atom(Atom::Symbol(s.into()));
    let string = |s: &str| SExpr::Atom(Atom::Str(s.into()));
    let make = |verb: &str, signer: &str, cause: &str, fields: Vec<(&str, SExpr)>| {
        let mut body = vec![symbol(verb), symbol("@room")];
        for (k, v) in fields.into_iter().chain([
            ("from", symbol(signer)),
            ("thread", string("t")),
            ("caused-by", symbol(cause)),
        ]) {
            body.push(SExpr::Atom(Atom::Keyword(k.into())));
            body.push(v);
        }
        Candidate::unauthenticated(
            serialize(&SExpr::List(vec![
                symbol("lang"),
                symbol(name),
                SExpr::List(body),
            ])),
            signer.into(),
        )
    };
    let root = make("open", "@a", "begin", vec![("title", string("Document"))]);
    let root_id = address(&root);
    let draft = make(
        "put",
        "@a",
        &root_id,
        vec![
            ("slot", string("n1.fill")),
            ("value", string("red")),
            ("clock", string("hlc-0000000000000010-00000000")),
            ("replaces", SExpr::List(vec![])),
        ],
    );
    let newer = make(
        "put",
        "@a",
        &root_id,
        vec![
            ("slot", string("n1.fill")),
            ("value", string("blue")),
            ("clock", string("hlc-0000000000000020-00000000")),
            ("replaces", SExpr::List(vec![symbol(&address(&draft))])),
        ],
    );
    let delete = make(
        "unset",
        "@a",
        &root_id,
        vec![
            ("slot", string("n1.fill")),
            ("replaces", SExpr::List(vec![symbol(&address(&newer))])),
        ],
    );
    let unseen = make(
        "put",
        "@b",
        &root_id,
        vec![
            ("slot", string("n1.fill")),
            ("value", string("green")),
            ("clock", string("hlc-0000000000000001-00000000")),
            ("replaces", SExpr::List(vec![])),
        ],
    );
    let c = vec![root, draft, newer, delete, unseen];
    let p = Profile::compile(source, "t", &c).unwrap();
    let selected = |n: usize| {
        p.mask(
            &c[..n]
                .iter()
                .map(address)
                .collect::<Vec<_>>()
                .iter()
                .map(String::as_str)
                .collect::<Vec<_>>(),
        )
        .unwrap()
    };
    let b = selected(3);
    let deleted = selected(4);
    let concurrent = selected(5);
    let state: Json = serde_json::from_str(p.state_json(deleted).unwrap()).unwrap();
    assert!(state["properties"].as_object().unwrap().is_empty());
    let state: Json = serde_json::from_str(p.state_json(concurrent).unwrap()).unwrap();
    assert_eq!(state["properties"]["n1.fill"], "green");
    assert!(mock(&p, b, deleted, &p.statement(b, deleted).unwrap()));
    assert!(mock(
        &p,
        deleted,
        concurrent,
        &p.statement(deleted, concurrent).unwrap()
    ));
    assert_ne!(
        p.checkpoint(deleted).unwrap().accepted,
        p.checkpoint(0).unwrap().accepted
    );
}

/// TEST-3505: the pinned vector and the compiled profile must agree on the
/// identity, every valid checkpoint, and the fixture's statement.
#[test]
fn golden_vector_matches_compiled_profile() {
    let (s, t, c) = fixture();
    let p = Profile::compile(&s, &t, &c).unwrap();
    let v: Json = serde_json::from_str(include_str!(
        "../../../test-vectors/state-proof/signer-supersession.json"
    ))
    .unwrap();
    let hex = |b: [u8; 32]| b.iter().map(|x| format!("{x:02x}")).collect::<String>();
    assert_eq!(v["version"], 1);
    assert_eq!(v["semantics_version"], SEMANTICS_VERSION);
    assert_eq!(v["thread"], t);
    assert_eq!(v["candidates"], c.len());
    assert_eq!(v["profile"], hex(p.id()));
    let checkpoints = v["checkpoints"].as_object().unwrap();
    let valid: Vec<u16> = (0..p.rows.len() as u16)
        .filter(|m| p.checkpoint(*m).is_ok())
        .collect();
    assert_eq!(
        checkpoints.len(),
        valid.len(),
        "every valid checkpoint is pinned"
    );
    for mask in valid {
        let cp = p.checkpoint(mask).unwrap();
        let pinned = &checkpoints[&mask.to_string()];
        assert_eq!(pinned["accepted"], hex(cp.accepted), "mask {mask}");
        assert_eq!(pinned["state"], hex(cp.state), "mask {mask}");
    }
    let (old, new) = masks(&p, &c);
    let statement = p.statement(old, new).unwrap();
    assert_eq!(v["statement"]["before"], old.to_string());
    assert_eq!(v["statement"]["after"], new.to_string());
    assert_eq!(v["statement"]["batch"], hex(statement.batch));
}

/// TEST-3505: the identity binds `SEMANTICS_VERSION` through `relation_domain`.
#[test]
fn semantics_version_changes_profile_identity() {
    let (s, t, c) = fixture();
    let p = Profile::compile(&s, &t, &c).unwrap();
    assert_eq!(
        profile::relation_domain(SEMANTICS_VERSION),
        b"cbcl-state-proof/relation-v1/d1a093d"
    );
    let same = p.id_with_domain(&profile::relation_domain(SEMANTICS_VERSION));
    let other = p.id_with_domain(&profile::relation_domain("other"));
    assert_eq!(same, p.id());
    assert_ne!(other, p.id());
    let stale = p.id_with_domain(&profile::relation_domain("c9093e8"));
    assert_ne!(
        stale,
        p.id(),
        "the previous semantics pin must not be reused"
    );
    assert_ne!(
        profile::relation_domain("other"),
        profile::relation_domain(SEMANTICS_VERSION)
    );
}

/// Regenerates the golden vector. Run after bumping `SEMANTICS_VERSION`:
/// `cargo test -p cbcl-state-proof -- --ignored write_golden_vector`.
#[test]
#[ignore]
fn write_golden_vector() {
    let (s, t, c) = fixture();
    let p = Profile::compile(&s, &t, &c).unwrap();
    let hex = |b: [u8; 32]| b.iter().map(|x| format!("{x:02x}")).collect::<String>();
    let mut checkpoints = serde_json::Map::new();
    for mask in 0..p.rows.len() as u16 {
        if let Ok(cp) = p.checkpoint(mask) {
            checkpoints.insert(
                mask.to_string(),
                serde_json::json!({"accepted": hex(cp.accepted), "state": hex(cp.state)}),
            );
        }
    }
    let (old, new) = masks(&p, &c);
    let statement = p.statement(old, new).unwrap();
    let v = serde_json::json!({
        "version": 1,
        "semantics_version": SEMANTICS_VERSION,
        "fixture": "test-vectors/state/signer-supersession.json",
        "thread": t,
        "candidates": c.len(),
        "profile": hex(p.id()),
        "checkpoints": checkpoints,
        "statement": {"before": old.to_string(), "after": new.to_string(), "batch": hex(statement.batch)},
    });
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../test-vectors/state-proof/signer-supersession.json"
    );
    std::fs::create_dir_all(std::path::Path::new(path).parent().unwrap()).unwrap();
    std::fs::write(
        path,
        format!("{}\n", serde_json::to_string_pretty(&v).unwrap()),
    )
    .unwrap();
}

/// Data-dependent test signer, as in `equivocation.rs`:
/// sig = SHA-256(secret ‖ data).
struct TestSigner {
    secret: &'static [u8],
}
impl Signer for TestSigner {
    fn sign(&self, data: &[u8]) -> Vec<u8> {
        use sha2::{Digest, Sha256};
        Sha256::new()
            .chain_update(self.secret)
            .chain_update(data)
            .finalize()
            .to_vec()
    }
    fn verify(&self, data: &[u8], sig: &[u8]) -> bool {
        self.sign(data) == sig
    }
}
const KEY: TestSigner = TestSigner { secret: b"key" };
/// Fixture texts end in `:from <key>))`; add a `:sender` string to the simple
/// message. A string because `@suite:name` does not tokenise as a symbol.
fn with_sender(text: &str, sender: &str) -> String {
    let body = text.strip_suffix("))").unwrap();
    format!("{body} :sender \"{sender}\"))")
}
/// Sign the innermost simple message's header (empty signature when it has
/// none) and build the attested candidate.
fn attest(text: &str, signer: &dyn Signer) -> std::result::Result<Candidate, String> {
    let message = parse_message(&parse(text).unwrap()).unwrap();
    let signature = attestation_header_for(message.innermost_simple().unwrap())
        .ok()
        .and_then(|h| sign_attestation_v2(signer, &h).ok())
        .unwrap_or_default();
    Candidate::attested(&message, &signature, signer)
}

/// TEST-3503 positive: attested labels are the `:from` text and the profile
/// identity matches the unauthenticated path.
#[test]
fn attested_candidates_bind_from_label_and_match_unauthenticated_profile() {
    let (s, t, c) = fixture();
    let mut attested = Vec::new();
    let mut plain = Vec::new();
    for c in &c {
        let text = with_sender(c.text(), c.label());
        let a = attest(&text, &KEY).unwrap();
        assert_eq!(a.label(), c.label());
        attested.push(a);
        plain.push(retext(c, text));
    }
    let p = Profile::compile(&s, &t, &attested).unwrap();
    let q = Profile::compile(&s, &t, &plain).unwrap();
    assert_eq!(p.id(), q.id());
    assert_eq!(p.addresses(), q.addresses());
    // `:sender` changes the addresses the fixture's children point at; the
    // opener stands alone and shows an attested candidate is admissible.
    let opener = p.mask(&[&address(&attested[0])]).unwrap();
    assert!(p.statement(0, opener).is_ok());
    // Alias spelling: `@a` and `@ed25519:a` are one key; the label keeps `@a`.
    let alias = attest(&with_sender(c[1].text(), "@ed25519:a"), &KEY).unwrap();
    assert_eq!(alias.label(), "@a");
    assert_eq!(
        address(&alias),
        address(&retext(&c[1], alias.text().into()))
    );
}

/// TEST-3503 prohibited actions: every forged, altered or mismatched input
/// is rejected by `attested`.
#[test]
fn attested_rejects_forged_altered_and_mismatched_candidates() {
    let (_, _, c) = fixture();
    let owner = with_sender(c[0].text(), "@owner");
    let message = parse_message(&parse(&owner).unwrap()).unwrap();
    let header = attestation_header_for(message.innermost_simple().unwrap()).unwrap();
    let signature = sign_attestation_v2(&KEY, &header).unwrap();
    assert!(Candidate::attested(&message, &signature, &KEY).is_ok());
    let mut wrong = signature.clone();
    wrong[0] ^= 1;
    assert!(Candidate::attested(&message, &wrong, &KEY).is_err());
    assert!(Candidate::attested(&message, &[], &KEY).is_err());
    let other = TestSigner { secret: b"other" };
    assert!(Candidate::attested(&message, &signature, &other).is_err());
    // Payload edited after signing.
    let write = with_sender(c[1].text(), "@a");
    let signed = parse_message(&parse(&write).unwrap()).unwrap();
    let header = attestation_header_for(signed.innermost_simple().unwrap()).unwrap();
    let signature = sign_attestation_v2(&KEY, &header).unwrap();
    let edited = write.replace(":value \"old\"", ":value \"new\"");
    let edited = parse_message(&parse(&edited).unwrap()).unwrap();
    assert!(Candidate::attested(&edited, &signature, &KEY).is_err());
    assert!(Candidate::attested(&signed, &signature, &KEY).is_ok());
    // Missing routing fields.
    assert!(attest(c[0].text(), &KEY).is_err());
    assert!(attest(&owner.replace(" :thread \"s1\"", ""), &KEY).is_err());
    // `:from` disagrees with the signed `:sender`, by key or by suite.
    assert!(attest(&owner.replace(":from @owner", ":from @impostor"), &KEY).is_err());
    assert!(attest(&with_sender(c[1].text(), "@ed25519:b"), &KEY).is_err());
    assert!(attest(&with_sender(c[1].text(), "@pq:a"), &KEY).is_err());
    assert!(attest(
        &owner.replace(":from @owner", ":from @owner :from @owner"),
        &KEY
    )
    .is_err());
}

/// NFR-3500: eight candidates fit in k <= 14, reported without proving.
#[test]
fn eight_candidate_profile_circuit_k_is_at_most_14() {
    let v: Json = serde_json::from_str(include_str!(
        "../../../test-vectors/state/tags-and-balance.json"
    ))
    .unwrap();
    let mut candidates = Vec::new();
    let mut seen = std::collections::BTreeSet::new();
    for m in v["messages"].as_array().unwrap() {
        let c = Candidate::unauthenticated(
            m["canonical"].as_str().unwrap().into(),
            m["signer"].as_str().unwrap().into(),
        );
        if seen.insert(address(&c)) && candidates.len() < MAX_CANDIDATES {
            candidates.push(c);
        }
    }
    assert_eq!(candidates.len(), MAX_CANDIDATES);
    let p = Profile::compile(
        v["contract"].as_str().unwrap(),
        v["thread"].as_str().unwrap(),
        &candidates,
    )
    .unwrap();
    assert!(p.circuit_k() <= 14, "k = {}", p.circuit_k());
    let (source, thread, three) = fixture();
    let small = Profile::compile(&source, &thread, &three).unwrap();
    assert!(small.circuit_k() < p.circuit_k());
}

/// REQ-3512 (b): only one `lang` wrapper naming the installed dialect directly
/// around a simple message binds a candidate. A nested wrapper or a `signed`
/// form between the wrapper and the simple message invalidates every set that
/// contains the candidate; compilation still succeeds.
#[test]
fn nested_or_wrapped_dialect_forms_invalidate_every_containing_set() {
    let (s, t, c) = fixture();
    let opener = c[0].text();
    let inner = opener.strip_prefix("(lang signer-register ").unwrap();
    for text in [
        format!("(lang signer-register (lang other {inner})"),
        format!("(lang signer-register (lang signer-register {inner})"),
        format!("(lang signer-register (signed @owner {inner})"),
    ] {
        let p = Profile::compile(&s, &t, &[retext(&c[0], text.clone())]).unwrap();
        assert!(p.statement(0, 1).is_err(), "{text}");
        assert!(!mock(&p, 0, 1, &raw_statement(&p, 0, 1)), "{text}");
    }
    // Control: the plain wrapper is bound.
    let p = Profile::compile(&s, &t, &c[..1]).unwrap();
    assert!(p.statement(0, 1).is_ok());
}

/// REQ-3504 (c): the `:from` scan advances like `keyword_fields`, so a second
/// `:from` after a stray positional param is still counted and rejected.
#[test]
fn attested_rejects_second_from_after_stray_positional_param() {
    use cbcl_core::sexpr::Atom;
    let (_, _, c) = fixture();
    let owner = with_sender(c[0].text(), "@owner");
    let mut message = parse_message(&parse(&owner).unwrap()).unwrap();
    let Message::Dialect { inner, .. } = &mut message else {
        unreachable!()
    };
    let Message::Simple { params, .. } = inner.as_mut() else {
        unreachable!()
    };
    let at = params
        .iter()
        .position(|p| matches!(p, SExpr::Atom(Atom::Keyword(k)) if k == "from"))
        .unwrap();
    params.insert(at + 2, SExpr::Atom(Atom::Symbol("junk".into())));
    params.insert(at + 3, SExpr::Atom(Atom::Keyword("from".into())));
    params.insert(at + 4, SExpr::Atom(Atom::Symbol("@other".into())));
    let header = attestation_header_for(message.innermost_simple().unwrap()).unwrap();
    let signature = sign_attestation_v2(&KEY, &header).unwrap();
    assert!(Candidate::attested(&message, &signature, &KEY).is_err());
    // Control: the same params without the second `:from` are accepted.
    let Message::Dialect { inner, .. } = &mut message else {
        unreachable!()
    };
    let Message::Simple { params, .. } = inner.as_mut() else {
        unreachable!()
    };
    params.truncate(at + 3);
    let header = attestation_header_for(message.innermost_simple().unwrap()).unwrap();
    let signature = sign_attestation_v2(&KEY, &header).unwrap();
    assert!(Candidate::attested(&message, &signature, &KEY).is_ok());
}

/// TEST-3506: every size bound and the roles rule fail before enumeration,
/// each naming the bound that tripped (REQ-3507 b, c, d, h; CON-3500).
#[test]
fn size_bounds_and_roles_fail_before_enumeration() {
    use std::time::{Duration, Instant};
    let (s, t, c) = fixture();
    let timed = |label: &str, compile: &dyn Fn() -> Result<Profile>| -> String {
        let start = Instant::now();
        let err = compile()
            .err()
            .unwrap_or_else(|| panic!("{label} accepted"));
        let elapsed = start.elapsed();
        assert!(elapsed < Duration::from_millis(100), "{label}: {elapsed:?}");
        err
    };
    let nine = timed("nine candidates", &|| {
        Profile::compile(&s, &t, &vec![c[0].clone(); MAX_CANDIDATES + 1])
    });
    assert!(nine.contains("more than 8 candidates"), "{nine}");
    let dialect = format!("{s}{}", " ".repeat(65_537 - s.len()));
    assert_eq!(dialect.len(), 65_537);
    let err = timed("dialect", &|| Profile::compile(&dialect, &t, &c));
    assert!(err.contains("dialect source over 65,536 bytes"), "{err}");
    let text = format!("{}{}", c[0].text(), " ".repeat(8_193 - c[0].text().len()));
    assert_eq!(text.len(), 8_193);
    let big = retext(&c[0], text);
    let err = timed("candidate", &|| {
        Profile::compile(&s, &t, std::slice::from_ref(&big))
    });
    assert!(err.contains("candidate text over 8,192 bytes"), "{err}");
    let labelled = relabel(&c[0], &"x".repeat(2_049));
    let err = timed("label", &|| {
        Profile::compile(&s, &t, std::slice::from_ref(&labelled))
    });
    assert!(err.contains("label over 2,048 bytes"), "{err}");
    let thread = "x".repeat(2_049);
    let err = timed("thread", &|| Profile::compile(&s, &thread, &c));
    assert!(err.contains("thread over 2,048 bytes"), "{err}");
    let roles: Json = serde_json::from_str(include_str!(
        "../../../test-vectors/state/checklist-roles.json"
    ))
    .unwrap();
    let err = Profile::compile(
        roles["contract"].as_str().unwrap(),
        roles["thread"].as_str().unwrap(),
        &[],
    )
    .unwrap_err();
    assert!(err.contains("role"), "{err}");
    // Controls: the bounds themselves are accepted.
    let at_bound = format!("{s}{}", " ".repeat(65_536 - s.len()));
    assert!(Profile::compile(&at_bound, &"x".repeat(2_048), &[]).is_ok());
}

/// REQ-3503 / REQ-3500: a selection bit of 2 is rejected, and the Boolean
/// gate itself is among the failures (not only the downstream sums).
#[test]
fn non_boolean_selection_bit_is_rejected_by_the_boolean_gate() {
    let (s, t, c) = fixture();
    let p = Profile::compile(&s, &t, &c).unwrap();
    let (old, new) = masks(&p, &c);
    let statement = p.statement(old, new).unwrap();
    let mut dishonest = StateCircuit::witness(&p, old, new);
    dishonest.forge_non_boolean_bit = true;
    let failures = MockProver::run(dishonest.k(), &dishonest, vec![statement.instance()])
        .unwrap()
        .verify()
        .unwrap_err();
    assert!(
        failures
            .iter()
            .any(|f| f.to_string().contains("Boolean selection")),
        "{failures:#?}"
    );
}

/// TEST-3502: with the pair removed from the compiled relation and an honest
/// (zero) transition total, the final-total constant constraint alone rejects.
#[test]
fn transition_total_must_equal_one_without_a_forged_sum() {
    let (s, t, c) = fixture();
    let mut p = Profile::compile(&s, &t, &c).unwrap();
    let (old, new) = masks(&p, &c);
    let statement = p.statement(old, new).unwrap();
    p.transitions
        .retain(|pair| *pair != (old as usize, new as usize));
    assert!(!mock(&p, old, new, &statement));
}

/// TEST-3500 (lunch-vote): per-subset parity for the second fixture.
#[test]
fn lunch_vote_native_fold_matches_for_every_valid_subset() {
    let (source, thread, c) = corpus(include_str!(
        "../../../test-vectors/state/lunch-vote-domain.json"
    ));
    assert!(c.len() > 1);
    assert_native_parity(&source, &thread, &c);
}

/// Current native heads without the role-bound resource adapter. Real candidate
/// identities and explicit typed clocks are used; no test-assigned hash ordering.
fn native_fifteen_fixture() -> (String, Vec<Candidate>) {
    let source = r#"(define proof-native-fifteen (cbcl) @a
      (:resource-requirements ((max-depth 12) (max-expansion-size 2048) (verification-time 200)))
      (extend open (to title) (tell to :title title))
      (extend put (to slot value clock) (tell to :slot slot :value value :clock clock))
      (extend drop (to slot) (tell to :slot slot))
      (extend down (to value) (tell to :value value))
      (shape open (require :title string))
      (shape put (require :slot string) (require :value number) (require :clock hlc))
      (shape drop (require :slot string))
      (shape down (require :value number))
      (protocol (then begin open) (then open put) (then open drop) (then open down))
      (state
        (title (initial open :title))
        (lww (lww-register put :value :clock))
        (own (lww-per-signer put :value :clock))
        (map (lww-map put :slot :value :clock drop))
        (values (values put :value))
        (conflicts (values-per-key put :slot :value drop))
        (members (observed-set put drop :slot))
        (exists (exists put))
        (count (count put))
        (progress (progress put))
        (events (events put :value))
        (tags (set-union put :value))
        (counter (counter put down :value))
        (histogram (histogram map))
        (sum (sum map))))"#
        .to_string();
    let make = |verb: &str, signer: &str, cause: &str, fields: &str| {
        Candidate::unauthenticated(format!(
            "(lang proof-native-fifteen ({verb} @room {fields} :from {signer} :thread \"native\" :caused-by {cause}))"), signer.into())
    };
    let opener = make("open", "@owner", "begin", ":title \"Immutable title\"");
    let root = address(&opener);
    let high = make(
        "put",
        "@a",
        &root,
        ":slot \"x\" :value 1 :clock \"hlc-0000000000000064-00000000\" :replaces ()",
    );
    let edit = make(
        "put",
        "@a",
        &root,
        &format!(
            ":slot \"x\" :value 2 :clock \"hlc-0000000000000001-00000000\" :replaces ({})",
            address(&high)
        ),
    );
    let delete = make(
        "drop",
        "@a",
        &root,
        &format!(":slot \"x\" :replaces ({})", address(&edit)),
    );
    (source, vec![opener, high, edit, delete])
}
fn selected_mask(p: &Profile, candidates: &[Candidate]) -> u16 {
    let ids: Vec<_> = candidates.iter().map(address).collect();
    p.mask(&ids.iter().map(String::as_str).collect::<Vec<_>>())
        .unwrap()
}
#[test]
fn current_fifteen_role_free_heads_match_native_fold_for_every_valid_subset() {
    let (source, candidates) = native_fifteen_fixture();
    let registry = parse_and_install_dialect(&parse(&source).unwrap()).unwrap();
    let dialect = registry.iter().last().unwrap();
    let actual_heads: std::collections::BTreeSet<_> = dialect
        .state
        .as_ref()
        .unwrap()
        .fields()
        .map(|(_, r)| r.head())
        .collect();
    let expected: std::collections::BTreeSet<_> = [
        "initial",
        "lww-register",
        "lww-per-signer",
        "lww-map",
        "values",
        "values-per-key",
        "observed-set",
        "exists",
        "count",
        "progress",
        "events",
        "set-union",
        "counter",
        "histogram",
        "sum",
    ]
    .into_iter()
    .collect();
    assert_eq!(actual_heads, expected);
    assert_native_parity(&source, "native", &candidates);
    let p = Profile::compile(&source, "native", &candidates).unwrap();
    let before = selected_mask(&p, &candidates[..2]);
    let retired = selected_mask(&p, &candidates[..3]);
    let all = selected_mask(&p, &candidates);
    let state: Json = serde_json::from_str(p.state_json(retired).unwrap()).unwrap();
    assert_eq!(state["title"], "Immutable title");
    assert_eq!(
        state["lww"], 1,
        "unkeyed LWW ignores replacement retirement"
    );
    assert_eq!(
        state["own"]["@a"], 2,
        "currentOwn retirement precedes HLC choice"
    );
    assert_eq!(
        state["map"]["x"], 2,
        "a low-clock replacement removes the former winner"
    );
    assert_eq!(state["count"], 2);
    assert_eq!(state["progress"], 1);
    assert_eq!(state["counter"], 3);
    assert_eq!(state["sum"], 2);
    let deleted: Json = serde_json::from_str(p.state_json(all).unwrap()).unwrap();
    assert!(deleted["map"].as_object().unwrap().is_empty());
    assert!(deleted["conflicts"].as_object().unwrap().is_empty());
    assert_eq!(deleted["events"].as_object().unwrap().len(), 2);
    assert_eq!(deleted["sum"], 0);
    assert!(mock(
        &p,
        before,
        retired,
        &p.statement(before, retired).unwrap()
    ));
    assert!(mock(&p, retired, all, &p.statement(retired, all).unwrap()));
}
#[test]
fn typed_hlc_order_and_malformed_clock_follow_native_admission() {
    let (source, candidates) = native_fifteen_fixture();
    let opener = &candidates[0];
    let old = &candidates[1];
    let mut newer = None;
    for nonce in 0..256 {
        let c = Candidate::unauthenticated(format!("(lang proof-native-fifteen (put @room \"{nonce}\" :slot \"x\" :value 3 :clock \"hlc-0000000000000065-00000001\" :replaces () :from @a :thread \"native\" :caused-by {}))",address(opener)), "@a".into());
        // Vary only the content nonce; no fake identities or undeclared fields.
        if address(&c) < address(old) {
            newer = Some(c);
            break;
        }
    }
    let newer = newer.expect("find a real lower-hash newer-clock candidate");
    assert!(address(&newer) < address(old));
    let c = vec![opener.clone(), old.clone(), newer.clone()];
    assert_native_parity(&source, "native", &c);
    let p = Profile::compile(&source, "native", &c).unwrap();
    let all = selected_mask(&p, &c);
    let state: Json = serde_json::from_str(p.state_json(all).unwrap()).unwrap();
    assert_eq!(
        state["lww"], 3,
        "typed HLC must win despite lower native content hash"
    );
    assert_eq!(state["map"]["x"], 3);
    assert_eq!(state["own"]["@a"], 3);
    let bad = retext(
        &newer,
        newer.text().replace(
            "hlc-0000000000000065-00000001",
            "hlc-0000000000000065-0000000A",
        ),
    );
    let bad_profile = Profile::compile(&source, "native", &[opener.clone(), bad.clone()]).unwrap();
    let mask = selected_mask(&bad_profile, &[opener.clone(), bad]);
    assert!(bad_profile.checkpoint(mask).is_err());
    assert!(!mock(
        &bad_profile,
        0,
        mask,
        &raw_statement(&bad_profile, 0, mask)
    ));
}
#[test]
fn initial_is_empty_or_sole_opener_and_never_lww_arbitrated() {
    let (source, candidates) = native_fifteen_fixture();
    let second = retext(
        &candidates[0],
        candidates[0]
            .text()
            .replace("Immutable title", "Another title"),
    );
    let c = vec![candidates[0].clone(), second];
    let p = Profile::compile(&source, "native", &c).unwrap();
    let empty: Json = serde_json::from_str(p.state_json(0).unwrap()).unwrap();
    assert!(empty["title"].is_null());
    for opener in &c {
        let only = p.mask(&[&address(opener)]).unwrap();
        let state: Json = serde_json::from_str(p.state_json(only).unwrap()).unwrap();
        assert!(state["title"].is_string());
    }
    let both = selected_mask(&p, &c);
    // Native admission may reject ambiguous opener evidence. If the role-free
    // history is admitted, initial itself must return absent, not pick a hash.
    if let Ok(json) = p.state_json(both) {
        let state: Json = serde_json::from_str(json).unwrap();
        assert!(state["title"].is_null());
    }
    assert_native_parity(&source, "native", &c);
}
#[test]
fn native_bounded_counter_cast_requirement_does_not_bypass_role_free_profile() {
    let source = include_str!("../../../dialects/example-quorum-coin.cbcl");
    let registry = parse_and_install_dialect(&parse(source).unwrap()).unwrap();
    assert!(!registry.iter().last().unwrap().roles.is_empty());
    let err = Profile::compile(source, "resource", &[]).unwrap_err();
    assert!(err.contains("role-free"), "{err}");
}
