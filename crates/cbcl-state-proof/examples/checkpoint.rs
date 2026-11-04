//! End-to-end proof over real CBCL conformance messages, with cached keys.
use cbcl_core::state::Act;
use cbcl_parser::{parse, parse_message};
use cbcl_state_proof::{Candidate, Profile, Proof, Prover, Verifier};
use serde_json::Value;
use std::time::Instant;

fn main() -> Result<(), String> {
    let fixture: Value = serde_json::from_str(include_str!(
        "../../../test-vectors/state/signer-supersession.json"
    ))
    .map_err(|e| e.to_string())?;
    let source = fixture["contract"].as_str().ok_or("missing contract")?;
    let candidates: Vec<_> = fixture["messages"].as_array().ok_or("missing messages")?[..3]
        .iter()
        .map(|m| {
            Candidate::unauthenticated(
                m["canonical"].as_str().unwrap().into(),
                m["signer"].as_str().unwrap().into(),
            )
        })
        .collect();
    let addresses: Vec<_> = candidates
        .iter()
        .map(|c| {
            let message = parse_message(&parse(c.text()).map_err(|e| e.to_string())?)
                .map_err(|e| e.to_string())?;
            Ok(Act::from_message(message, c.label())?.address)
        })
        .collect::<Result<_, String>>()?;
    let start = Instant::now();
    let profile = Profile::compile(source, "s1", &candidates)?;
    let compile_ms = start.elapsed().as_millis();
    let before = profile.mask(&[&addresses[0], &addresses[1]])?;
    let after = profile.mask(&addresses.iter().map(String::as_str).collect::<Vec<_>>())?;
    let expected = profile.statement(before, after)?;
    let state = profile.state_json(after)?.to_owned();
    let start = Instant::now();
    let prover = Prover::new(profile)?;
    let prover_setup_ms = start.elapsed().as_millis();
    // Independently rebuild the relation and verification key from expected inputs.
    let start = Instant::now();
    let verifier = Verifier::new(Profile::compile(source, "s1", &candidates)?)?;
    let verifier_setup_ms = start.elapsed().as_millis();
    let start = Instant::now();
    let proof = prover.prove(before, after)?;
    let prove_ms = start.elapsed().as_millis();
    let serialized = proof.to_json()?;
    let received = Proof::from_json(&serialized)?;
    let start = Instant::now();
    verifier.verify(&received, &expected)?;
    let verify_ms = start.elapsed().as_millis();
    // Rebinding both the package and caller expectation cannot change the proved state.
    let mut forged = received.clone();
    forged.statement.after.state[0] ^= 1;
    if verifier.verify(&forged, &forged.statement).is_ok() {
        return Err("tampered state verified".into());
    }
    println!(
        "{}",
        serde_json::json!({"candidates":candidates.len(),"compile_ms":compile_ms,"prover_setup_ms":prover_setup_ms,"verifier_setup_ms":verifier_setup_ms,"prove_ms":prove_ms,"cached_verify_ms":verify_ms,"transcript_bytes":proof.transcript.len(),"package_bytes":serialized.len(),"state":serde_json::from_str::<Value>(&state).map_err(|e|e.to_string())?,"tampered_state_rejected":true,"signature_verification":"external host precondition"})
    );
    Ok(())
}
