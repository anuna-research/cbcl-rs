//! TEST-3504: checkpoint chains from a receiver-pinned start (SPEC-035 REQ-3505).
use crate::*;
use cbcl_core::state::Act;
use cbcl_parser::{parse, parse_message};
use serde_json::Value as Json;
use std::sync::OnceLock;

/// One prover for the whole module: real proofs are slow.
struct Fixture {
    source: String,
    thread: String,
    candidates: Vec<Candidate>,
    profile: Profile,
    verifier: Verifier,
    /// Masks of the valid transitions empty → opener → {opener, first write} → all.
    steps: [u16; 4],
    /// Proofs for each consecutive step.
    links: [Proof; 3],
}
fn fixture() -> &'static Fixture {
    static F: OnceLock<Fixture> = OnceLock::new();
    F.get_or_init(|| {
        let v: Json = serde_json::from_str(include_str!(
            "../../../test-vectors/state/signer-supersession.json"
        ))
        .unwrap();
        let candidates: Vec<Candidate> = v["messages"].as_array().unwrap()[..3]
            .iter()
            .map(|m| {
                Candidate::unauthenticated(
                    m["canonical"].as_str().unwrap().into(),
                    m["signer"].as_str().unwrap().into(),
                )
            })
            .collect();
        let source: String = v["contract"].as_str().unwrap().into();
        let thread = "s1".to_string();
        let addr: Vec<String> = candidates
            .iter()
            .map(|c| {
                Act::from_message(parse_message(&parse(c.text()).unwrap()).unwrap(), c.label())
                    .unwrap()
                    .address
            })
            .collect();
        let profile = Profile::compile(&source, &thread, &candidates).unwrap();
        let opener = profile.mask(&[&addr[0]]).unwrap();
        let two = profile.mask(&[&addr[0], &addr[1]]).unwrap();
        let all = profile.mask(&[&addr[0], &addr[1], &addr[2]]).unwrap();
        let steps = [0, opener, two, all];
        for w in steps.windows(2) {
            profile.statement(w[0], w[1]).unwrap();
        }
        let prover = Prover::new(profile.clone()).unwrap();
        let links = std::array::from_fn(|i| prover.prove(steps[i], steps[i + 1]).unwrap());
        let verifier =
            Verifier::new(Profile::compile(&source, &thread, &candidates).unwrap()).unwrap();
        Fixture {
            source,
            thread,
            candidates,
            profile,
            verifier,
            steps,
            links,
        }
    })
}
fn chain(links: &[Proof]) -> Chain {
    Chain::new(fixture().profile.id(), links.to_vec()).unwrap()
}
fn ckpt(i: usize) -> Checkpoint {
    let f = fixture();
    f.profile.checkpoint(f.steps[i]).unwrap()
}
/// A syntactically valid link that never verifies.
fn fake_link() -> Proof {
    Proof {
        statement: fixture().profile.statement(0, 0).unwrap(),
        transcript: vec![0; 32],
    }
}

#[test]
fn genesis_is_the_empty_set_checkpoint() {
    let f = fixture();
    assert_eq!(f.profile.genesis(), f.profile.checkpoint(0).unwrap());
    let empty = Profile::compile(&f.source, &f.thread, &[]).unwrap();
    assert_eq!(empty.genesis(), empty.checkpoint(0).unwrap());
}
#[test]
fn two_link_chain_from_genesis_verifies() {
    let f = fixture();
    let c = chain(&f.links[..2]);
    assert_eq!(c.profile(), f.profile.id());
    assert_eq!(c.links().len(), 2);
    assert_eq!(
        c.verify(&f.verifier, f.profile.genesis(), None).unwrap(),
        ckpt(2)
    );
}
#[test]
fn one_link_chain_from_non_genesis_start_verifies() {
    let f = fixture();
    let c = chain(&f.links[2..]);
    assert_eq!(c.verify(&f.verifier, ckpt(2), None).unwrap(), ckpt(3));
}
#[test]
fn empty_chain_returns_start() {
    let f = fixture();
    let c = chain(&[]);
    assert_eq!(c.verify(&f.verifier, ckpt(2), None).unwrap(), ckpt(2));
    assert_eq!(
        c.verify(&f.verifier, ckpt(2), Some(ckpt(2))).unwrap(),
        ckpt(2)
    );
    assert!(c.verify(&f.verifier, ckpt(2), Some(ckpt(3))).is_err());
}
#[test]
fn matching_expected_end_is_accepted() {
    let f = fixture();
    let c = chain(&f.links);
    assert_eq!(
        c.verify(&f.verifier, f.profile.genesis(), Some(ckpt(3)))
            .unwrap(),
        ckpt(3)
    );
}
#[test]
fn expected_end_mismatch_is_rejected() {
    let f = fixture();
    let c = chain(&f.links[..2]);
    assert!(c
        .verify(&f.verifier, f.profile.genesis(), Some(ckpt(3)))
        .is_err());
    assert!(c
        .verify(&f.verifier, f.profile.genesis(), Some(f.profile.genesis()))
        .is_err());
}
#[test]
fn first_link_not_at_start_is_rejected() {
    let f = fixture();
    let c = chain(&f.links[1..2]);
    assert!(c.verify(&f.verifier, f.profile.genesis(), None).is_err());
    assert!(c.verify(&f.verifier, ckpt(1), None).is_ok());
}
#[test]
fn gap_between_links_is_rejected() {
    let f = fixture();
    let c = chain(&[f.links[0].clone(), f.links[2].clone()]);
    assert!(c.verify(&f.verifier, f.profile.genesis(), None).is_err());
}
#[test]
fn swapped_links_are_rejected() {
    let f = fixture();
    let c = chain(&[f.links[1].clone(), f.links[0].clone()]);
    assert!(c.verify(&f.verifier, f.profile.genesis(), None).is_err());
    assert!(c.verify(&f.verifier, ckpt(1), None).is_err());
}
#[test]
fn foreign_profile_in_header_is_rejected() {
    let f = fixture();
    let mut foreign = f.profile.id();
    foreign[0] ^= 1;
    let c = Chain::new(foreign, f.links[..2].to_vec()).unwrap();
    let err = c
        .verify(&f.verifier, f.profile.genesis(), None)
        .unwrap_err();
    assert!(err.contains("chain profile differs"), "{err}");
}
#[test]
fn foreign_profile_in_one_link_is_rejected() {
    let f = fixture();
    let mut links = f.links[..2].to_vec();
    links[1].statement.profile[0] ^= 1;
    let c = chain(&links);
    // REQ-3505: rejected on the early path, before the backend runs.
    let err = c
        .verify(&f.verifier, f.profile.genesis(), None)
        .unwrap_err();
    assert!(err.contains("link 1: foreign profile"), "{err}");
}
#[test]
fn corrupted_transcript_in_second_link_is_rejected() {
    let f = fixture();
    let mut links = f.links[..2].to_vec();
    links[1].transcript[0] ^= 1;
    let c = chain(&links);
    assert!(c.verify(&f.verifier, f.profile.genesis(), None).is_err());
}
#[test]
fn sixty_five_links_are_rejected_by_new_and_from_json() {
    let f = fixture();
    let links = vec![fake_link(); 64];
    let ok = Chain::new(f.profile.id(), links.clone()).unwrap();
    assert_eq!(ok.links().len(), 64);
    let json = ok.to_json().unwrap();
    assert_eq!(Chain::from_json(&json).unwrap(), ok);
    let mut links = links;
    links.push(fake_link());
    assert!(Chain::new(f.profile.id(), links).is_err());
    let mut v: Json = serde_json::from_slice(&json).unwrap();
    let extra = v["links"][0].clone();
    v["links"].as_array_mut().unwrap().push(extra);
    assert_eq!(v["links"].as_array().unwrap().len(), 65);
    assert!(Chain::from_json(&serde_json::to_vec(&v).unwrap()).is_err());
}
#[test]
fn json_round_trip_and_recogniser_limits() {
    let f = fixture();
    let c = chain(&f.links[..2]);
    let json = c.to_json().unwrap();
    assert_eq!(Chain::from_json(&json).unwrap(), c);
    assert!(json.len() <= MAX_PACKAGE);
    // Unknown member, trailing input, oversize package.
    let mut v: Json = serde_json::from_slice(&json).unwrap();
    v["extra"] = Json::Bool(true);
    assert!(Chain::from_json(&serde_json::to_vec(&v).unwrap()).is_err());
    assert!(Chain::from_json(&[json.as_slice(), b"x"].concat()).is_err());
    assert!(Chain::from_json(&[json.as_slice(), b" \n"].concat()).is_ok());
    assert!(Chain::from_json(&vec![b' '; MAX_CHAIN_PACKAGE + 1]).is_err());
    // Per-link transcript checks: a bad link is rejected by both directions.
    for n in [0usize, 31, MAX_TRANSCRIPT + 32] {
        let mut bad = fake_link();
        bad.transcript = vec![0; n];
        let c = Chain::new(f.profile.id(), vec![fixture().links[0].clone(), bad]).unwrap();
        assert!(c.to_json().is_err(), "{n}");
        let mut v: Json = serde_json::from_slice(&json).unwrap();
        v["links"][1]["transcript"] = Json::Array(vec![Json::from(0u8); n]);
        assert!(
            Chain::from_json(&serde_json::to_vec(&v).unwrap()).is_err(),
            "{n}"
        );
    }
    // Proof equality is structural.
    assert_eq!(f.links[0], f.links[0].clone());
    assert_ne!(f.links[0], f.links[1]);
    let _ = &f.candidates;
}

/// REQ-3505 / CON-3503: public serde deserialization bypasses constructors,
/// so verify must enforce the link bound before checking any proof.
#[test]
fn directly_deserialized_overlong_chain_is_rejected_before_verification() {
    let f = fixture();
    let value = serde_json::json!({
        "profile": f.profile.id(),
        "links": vec![fake_link(); 65],
    });
    let chain: Chain = serde_json::from_value(value).unwrap();
    let err = chain
        .verify(&f.verifier, f.profile.genesis(), None)
        .unwrap_err();
    assert_eq!(err, "chain exceeds link limit");
}

#[test]
fn stale_semantics_chain_is_rejected_before_verifying_links() {
    let f = fixture();
    let stale = f
        .profile
        .id_with_domain(&crate::profile::relation_domain("c9093e8"));
    assert_ne!(stale, f.profile.id());
    let chain = Chain::new(stale, f.links[..2].to_vec()).unwrap();
    let err = chain
        .verify(&f.verifier, f.profile.genesis(), None)
        .unwrap_err();
    assert!(err.contains("chain profile differs"), "{err}");
}
