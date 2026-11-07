//! Fuzz target: `Verifier::verify` with arbitrary transcript bytes against one
//! fixed verifier and the fixture's valid statement (SPEC-035 TEST-3507 depth
//! run). The call must return `Ok` or `Err` and never panic; the result is
//! otherwise ignored. The verifier is built once: key generation is slow.

#![no_main]

use cbcl_state_proof::{Candidate, Profile, Proof, Statement, Verifier};
use libfuzzer_sys::fuzz_target;
use std::sync::OnceLock;

/// Three-candidate fixture, selecting the first two and all three native IDs.
fn fixture() -> &'static (Verifier, Statement) {
    static F: OnceLock<(Verifier, Statement)> = OnceLock::new();
    F.get_or_init(|| {
        let v: serde_json::Value = serde_json::from_str(include_str!(
            "../../test-vectors/state/signer-supersession.json"
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
        let profile = Profile::compile(v["contract"].as_str().unwrap(), "s1", &candidates).unwrap();
        let ids: Vec<String> = candidates
            .iter()
            .map(|candidate| {
                let ast = cbcl_parser::parse(candidate.text()).unwrap();
                let message = cbcl_parser::parse_message(&ast).unwrap();
                cbcl_core::state::Act::from_message(message, candidate.label())
                    .unwrap()
                    .address
            })
            .collect();
        let before = profile
            .mask(&ids[..2].iter().map(String::as_str).collect::<Vec<_>>())
            .unwrap();
        let after = profile
            .mask(&ids.iter().map(String::as_str).collect::<Vec<_>>())
            .unwrap();
        let statement = profile.statement(before, after).unwrap();
        (Verifier::new(profile).unwrap(), statement)
    })
}

fuzz_target!(|data: &[u8]| {
    let (verifier, statement) = fixture();
    let proof = Proof {
        statement: statement.clone(),
        transcript: data.to_vec(),
    };
    let _ = verifier.verify(&proof, statement);
});
