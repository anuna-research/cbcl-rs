//! Prototype P1–P6: semantic differential checks and dishonest circuit witnesses.
use crate::*;
use cbcl_core::{
    serializer::serialize,
    sexpr::SExpr,
    state::{fold, render_json, Act},
};
use cbcl_parser::{parse, parse_and_install_dialect, parse_message};
use ff::Field;
use halo2_proofs::dev::MockProver;
use serde_json::Value as Json;

fn fixture() -> (String, String, Vec<Candidate>) {
    let v: Json = serde_json::from_str(include_str!(
        "../../../test-vectors/state/signer-supersession.json"
    ))
    .unwrap();
    let candidates = v["messages"].as_array().unwrap()[..3]
        .iter()
        .map(|m| Candidate {
            canonical: m["canonical"].as_str().unwrap().into(),
            signer: m["signer"].as_str().unwrap().into(),
        })
        .collect();
    (
        v["contract"].as_str().unwrap().into(),
        "s1".into(),
        candidates,
    )
}
fn address(c: &Candidate) -> String {
    Act::from_message(
        parse_message(&parse(&c.canonical).unwrap()).unwrap(),
        &c.signer,
    )
    .unwrap()
    .address
}
fn masks(p: &Profile, c: &[Candidate]) -> (u16, u16) {
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
#[test]
fn native_fold_and_replacement_match_for_every_valid_subset() {
    let (source, thread, c) = fixture();
    let p = Profile::compile(&source, &thread, &c).unwrap();
    let registry = parse_and_install_dialect(&parse(&source).unwrap()).unwrap();
    let d = registry.iter().last().unwrap();
    for mask in 0..p.rows.len() {
        if p.checkpoint(mask as u16).is_err() {
            continue;
        }
        let acts: Vec<_> = c
            .iter()
            .filter(|c| mask & p.mask(&[&address(c)]).unwrap() as usize != 0)
            .map(|c| {
                Act::from_message(
                    parse_message(&parse(&c.canonical).unwrap()).unwrap(),
                    &c.signer,
                )
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
    // Root sorts last in this corpus; children must remain pending until retried.
    assert_eq!(root, 4);
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
    for mode in ["shape", "sender", "thread", "dialect"] {
        let mut candidates = c[..2].to_vec();
        match mode {
            "shape" => {
                candidates[1].canonical = candidates[1]
                    .canonical
                    .replace(":value \"old\"", ":value 42")
            }
            "sender" => candidates[1].signer = "@impostor".into(),
            "thread" => {
                candidates[1].canonical = candidates[1].canonical.replace("\"s1\"", "\"other\"")
            }
            "dialect" => {
                candidates[1].canonical = candidates[1]
                    .canonical
                    .replace("lang signer-register", "lang other")
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
    let mut bad = c[0].clone();
    bad.canonical = format!("{}{}", "(".repeat(3000), ")".repeat(3000));
    assert!(Profile::compile(&s, &t, &[bad]).is_err());
    assert!(Profile::compile(&format!("{s} trailing"), &t, &c).is_err());
    assert!(Profile::compile(
        &s,
        &t,
        &[Candidate {
            canonical: format!("{} trailing", c[0].canonical),
            signer: c[0].signer.clone()
        }]
    )
    .is_err());
    let p = Profile::compile(&s, &t, &[]).unwrap();
    assert!(mock(&p, 0, 0, &p.statement(0, 0).unwrap()));
}
#[test]
fn canonical_whitespace_and_unknown_candidates() {
    let (s, t, mut c) = fixture();
    let p = Profile::compile(&s, &t, &c).unwrap();
    for c in &mut c {
        c.canonical = serialize(&SExpr::from(
            &parse_message(&parse(&c.canonical).unwrap()).unwrap(),
        ));
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
    assert!(prover.prove(0, 1).is_err()); // first sorted candidate is a pending write
}

#[test]
fn complete_native_corpus_snapshots_match_recorded_results() {
    for text in [
        include_str!("../../../test-vectors/state/signer-supersession.json"),
        include_str!("../../../test-vectors/state/lunch-vote-domain.json"),
    ] {
        let v: Json = serde_json::from_str(text).unwrap();
        let mut candidates = Vec::new();
        let mut seen = std::collections::BTreeSet::new();
        for m in v["messages"].as_array().unwrap() {
            let c = Candidate {
                canonical: m["canonical"].as_str().unwrap().into(),
                signer: m["signer"].as_str().unwrap().into(),
            };
            let id = address(&c);
            if v["expect"]["verdicts"][&id] == "accepted" && seen.insert(id) {
                candidates.push(c);
            }
        }
        let p = Profile::compile(
            v["contract"].as_str().unwrap(),
            v["thread"].as_str().unwrap(),
            &candidates,
        )
        .unwrap();
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
        "put":{"after":["open"],"fields":{"slot":"string","value":"string"}},
        "unset":{"after":["open"],"fields":{"slot":"string"}}
    },"state":{"properties":["registerPerKey","put","slot","value","unset"],"conflicts":["valuesPerKey","put","slot","value","unset"]}});
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
        Candidate {
            canonical: serialize(&SExpr::List(vec![
                symbol("lang"),
                symbol(name),
                SExpr::List(body),
            ])),
            signer: signer.into(),
        }
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
        b"cbcl-state-proof/relation-v1/c9093e8"
    );
    let same = p.id_with_domain(&profile::relation_domain(SEMANTICS_VERSION));
    let other = p.id_with_domain(&profile::relation_domain("other"));
    assert_eq!(same, p.id());
    assert_ne!(other, p.id());
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
