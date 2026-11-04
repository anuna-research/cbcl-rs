//! Fuzz target: `Verifier::verify` with arbitrary transcript bytes against one
//! fixed verifier and the fixture's valid statement (SPEC-035 TEST-3507 depth
//! run). The call must return `Ok` or `Err` and never panic; the result is
//! otherwise ignored. The verifier is built once: key generation is slow.

#![no_main]

use cbcl_state_proof::{Candidate, Profile, Proof, Statement, Verifier};
use libfuzzer_sys::fuzz_target;
use std::sync::OnceLock;

/// Three-candidate signer-supersession fixture; masks 6 -> 7 are the golden
/// statement of `test-vectors/state-proof/signer-supersession.json`.
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
        let statement = profile.statement(6, 7).unwrap();
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
