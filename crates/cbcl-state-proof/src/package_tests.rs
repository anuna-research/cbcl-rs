//! TEST-3507: package recognition is exactly the CON-3502 language
//! (SPEC-035 REQ-3508).
use crate::*;
use proptest::prelude::*;
use serde_json::Value as Json;
use std::sync::OnceLock;

/// One real proof; the prover is slow, so it is built once.
fn real_proof() -> &'static Proof {
    static P: OnceLock<Proof> = OnceLock::new();
    P.get_or_init(|| {
        let (source, thread, candidates) = crate::tests::fixture();
        let profile = Profile::compile(&source, &thread, &candidates).unwrap();
        let (old, new) = crate::tests::masks(&profile, &candidates);
        Prover::new(profile).unwrap().prove(old, new).unwrap()
    })
}
fn zero_statement() -> Statement {
    Statement {
        profile: [0; 32],
        before: Checkpoint {
            accepted: [0; 32],
            state: [0; 32],
        },
        after: Checkpoint {
            accepted: [0; 32],
            state: [0; 32],
        },
        batch: [0; 32],
    }
}
/// Syntactically valid proof with a 32-byte transcript. Never verifies.
fn small_proof() -> Proof {
    Proof {
        statement: zero_statement(),
        transcript: vec![7; 32],
    }
}
fn small_chain() -> Chain {
    Chain::new([1; 32], vec![small_proof(), small_proof()]).unwrap()
}
/// Replace the first occurrence of `from` in `text`; panics if absent.
fn edit(text: &str, from: &str, to: &str) -> Vec<u8> {
    assert!(text.contains(from), "{from}");
    text.replacen(from, to, 1).into_bytes()
}
fn proof_text() -> String {
    String::from_utf8(small_proof().to_json().unwrap()).unwrap()
}
fn chain_text() -> String {
    String::from_utf8(small_chain().to_json().unwrap()).unwrap()
}
fn pad(json: &[u8], len: usize) -> Vec<u8> {
    let mut v = json.to_vec();
    v.resize(len, b' ');
    v
}
fn h32_text(b: u8) -> String {
    serde_json::to_string(&[b; 32]).unwrap()
}

#[test]
fn writer_emits_members_in_grammar_order_without_whitespace() {
    let p = proof_text();
    assert!(p.starts_with(r#"{"statement":{"profile":[0,"#), "{p}");
    assert!(p.contains(r#"],"before":{"accepted":[0,"#));
    assert!(p.contains(r#"],"state":[0,"#));
    assert!(p.contains(r#"},"after":{"accepted":[0,"#));
    assert!(p.contains(r#"},"batch":[0,"#));
    assert!(p.contains(r#"},"transcript":[7,"#));
    assert!(!p.contains(' '));
    let c = chain_text();
    assert!(c.starts_with(r#"{"profile":[1,"#), "{c}");
    assert!(c.contains(r#"],"links":[{"statement":"#));
    assert!(!c.contains(' '));
}

#[test]
fn unknown_member_is_rejected() {
    let p = proof_text();
    assert!(Proof::from_json(&edit(&p, r#"{"statement":"#, r#"{"extra":1,"statement":"#)).is_err());
    assert!(Proof::from_json(&edit(&p, r#"{"profile":"#, r#"{"extra":1,"profile":"#)).is_err());
    assert!(Proof::from_json(&edit(&p, r#"{"accepted":"#, r#"{"extra":1,"accepted":"#)).is_err());
    let c = chain_text();
    assert!(Chain::from_json(&edit(&c, r#"{"profile":"#, r#"{"extra":1,"profile":"#)).is_err());
    assert!(Chain::from_json(&edit(&c, r#"{"statement":"#, r#"{"extra":1,"statement":"#)).is_err());
    // Controls: the unedited texts are in the language.
    assert!(Proof::from_json(p.as_bytes()).is_ok());
    assert!(Chain::from_json(c.as_bytes()).is_ok());
}

/// CON-3502: a positional array in any object position is rejected even
/// though serde would accept it for a struct.
#[test]
fn positional_arrays_are_rejected() {
    let h = h32_text(0);
    let t = serde_json::to_string(&[7u8; 32]).unwrap();
    let cp = format!("[{h},{h}]");
    let obj_cp = format!(r#"{{"accepted":{h},"state":{h}}}"#);
    let st = format!("[{h},{cp},{cp},{h}]");
    let obj_st = format!(r#"{{"profile":{h},"before":{obj_cp},"after":{obj_cp},"batch":{h}}}"#);
    // Control: the object text is in the language.
    let proof = format!(r#"{{"statement":{obj_st},"transcript":{t}}}"#);
    assert_eq!(Proof::from_json(proof.as_bytes()).unwrap(), small_proof());
    // Whole proof, statement, and one checkpoint as arrays.
    assert!(Proof::from_json(format!("[{st},{t}]").as_bytes()).is_err());
    assert!(
        Proof::from_json(format!(r#"{{"statement":{st},"transcript":{t}}}"#).as_bytes()).is_err()
    );
    let one_cp = format!(r#"{{"profile":{h},"before":{cp},"after":{obj_cp},"batch":{h}}}"#);
    assert!(
        Proof::from_json(format!(r#"{{"statement":{one_cp},"transcript":{t}}}"#).as_bytes())
            .is_err()
    );
    // Chain: whole chain, and one link, as arrays.
    let h1 = h32_text(1);
    assert!(Chain::from_json(format!("[{h1},[]]").as_bytes()).is_err());
    assert!(
        Chain::from_json(format!(r#"{{"profile":{h1},"links":[[{st},{t}]]}}"#).as_bytes()).is_err()
    );
    assert!(Chain::from_json(
        format!(r#"{{"profile":{h1},"links":[{{"statement":{st},"transcript":{t}}}]}}"#).as_bytes()
    )
    .is_err());
    // Control: the object form of the same chain is accepted.
    let chain = format!(r#"{{"profile":{h1},"links":[{proof}]}}"#);
    assert_eq!(Chain::from_json(chain.as_bytes()).unwrap().links().len(), 1);
}

#[test]
fn duplicate_member_is_rejected() {
    let p = proof_text();
    let t = format!(
        r#"{{"transcript":{},"statement":"#,
        serde_json::to_string(&[7u8; 32]).unwrap()
    );
    assert!(Proof::from_json(&edit(&p, r#"{"statement":"#, &t)).is_err());
    let b = format!(r#"{{"batch":{},"profile":"#, h32_text(0));
    assert!(Proof::from_json(&edit(&p, r#"{"profile":"#, &b)).is_err());
    let s = format!(r#"{{"state":{},"accepted":"#, h32_text(0));
    assert!(Proof::from_json(&edit(&p, r#"{"accepted":"#, &s)).is_err());
    let c = chain_text();
    let pr = format!(r#"{{"profile":{},"profile":"#, h32_text(1));
    assert!(Chain::from_json(&edit(&c, r#"{"profile":"#, &pr)).is_err());
    assert!(Chain::from_json(&edit(&c, r#"{"statement":"#, &t)).is_err());
    // Even an identical repeated member is a duplicate.
    let same = format!(r#"{{"profile":{},"profile":"#, h32_text(1));
    assert!(Chain::from_json(&edit(&c, r#"{"profile":"#, &same)).is_err());
}

#[test]
fn byte_values_outside_the_grammar_are_rejected() {
    let p = proof_text();
    let c = chain_text();
    for bad in [
        "256", "-1", "1.0", "1e0", "+1", "01", "\"1\"", "true", "null",
    ] {
        let at = format!(r#""transcript":[{bad},"#);
        assert!(
            Proof::from_json(&edit(&p, r#""transcript":[7,"#, &at)).is_err(),
            "{bad}"
        );
        let at = format!(r#""profile":[{bad},"#);
        assert!(
            Proof::from_json(&edit(&p, r#""profile":[0,"#, &at)).is_err(),
            "{bad}"
        );
        let at = format!(r#"{{"profile":[{bad},"#);
        assert!(
            Chain::from_json(&edit(&c, r#"{"profile":[1,"#, &at)).is_err(),
            "{bad}"
        );
        let at = format!(r#""transcript":[{bad},"#);
        assert!(
            Chain::from_json(&edit(&c, r#""transcript":[7,"#, &at)).is_err(),
            "{bad}"
        );
    }
    // Controls: the boundary values are in the language.
    assert!(Proof::from_json(&edit(&p, r#""transcript":[7,"#, r#""transcript":[255,"#)).is_ok());
    assert!(Proof::from_json(&edit(&p, r#""transcript":[7,"#, r#""transcript":[0,"#)).is_ok());
}

#[test]
fn h32_must_have_exactly_32_bytes() {
    let p = proof_text();
    assert!(Proof::from_json(&edit(&p, r#""profile":[0,"#, r#""profile":[0,0,"#)).is_err());
    assert!(Proof::from_json(&edit(&p, r#""profile":[0,"#, r#""profile":["#)).is_err());
    let c = chain_text();
    assert!(Chain::from_json(&edit(&c, r#"{"profile":[1,"#, r#"{"profile":[1,1,"#)).is_err());
    assert!(Chain::from_json(&edit(&c, r#"{"profile":[1,"#, r#"{"profile":["#)).is_err());
}

#[test]
fn trailing_input_other_than_json_whitespace_is_rejected() {
    let p = small_proof().to_json().unwrap();
    let c = small_chain().to_json().unwrap();
    for tail in [b"x".as_slice(), b"\n x", b"{}", b"\0", b",", b"\x0c"] {
        assert!(Proof::from_json(&[p.as_slice(), tail].concat()).is_err());
        assert!(Chain::from_json(&[c.as_slice(), tail].concat()).is_err());
    }
    for tail in [b"\n  ".as_slice(), b" ", b"\t\r\n", b""] {
        assert_eq!(
            Proof::from_json(&[p.as_slice(), tail].concat()).unwrap(),
            small_proof()
        );
        assert_eq!(
            Chain::from_json(&[c.as_slice(), tail].concat()).unwrap(),
            small_chain()
        );
    }
    // Whitespace between tokens is insignificant too.
    let spaced = proof_text().replace(',', " ,\n ").replace(':', " : ");
    assert_eq!(Proof::from_json(spaced.as_bytes()).unwrap(), small_proof());
    // Leading garbage and a truncated text are rejected.
    assert!(Proof::from_json(&[b"x", p.as_slice()].concat()).is_err());
    assert!(Proof::from_json(&p[..p.len() - 1]).is_err());
    assert!(Proof::from_json(b"").is_err());
    assert!(Chain::from_json(b"").is_err());
}

#[test]
fn proof_package_limit_is_100_000_bytes() {
    let p = small_proof().to_json().unwrap();
    assert_eq!(
        Proof::from_json(&pad(&p, MAX_PACKAGE)).unwrap(),
        small_proof()
    );
    assert!(Proof::from_json(&pad(&p, MAX_PACKAGE + 1)).is_err());
    assert!(Proof::from_json(&vec![b' '; MAX_PACKAGE + 1]).is_err());
    // The writer refuses too: a transcript at the length limit still fits, so
    // the package limit is reached only by an over-long transcript.
    let mut big = small_proof();
    big.transcript = vec![0; MAX_TRANSCRIPT];
    assert!(big.to_json().unwrap().len() <= MAX_PACKAGE);
}

#[test]
fn chain_package_limit_is_1_048_576_bytes() {
    assert_eq!(MAX_CHAIN_PACKAGE, 1_048_576);
    let c = small_chain().to_json().unwrap();
    assert_eq!(
        Chain::from_json(&pad(&c, MAX_CHAIN_PACKAGE)).unwrap(),
        small_chain()
    );
    assert!(Chain::from_json(&pad(&c, MAX_CHAIN_PACKAGE + 1)).is_err());
    assert!(Chain::from_json(&vec![b' '; MAX_CHAIN_PACKAGE + 1]).is_err());
    // A chain package may exceed the proof limit: four maximal links are
    // about 134,000 bytes.
    let mut p = small_proof();
    p.transcript = vec![0; MAX_TRANSCRIPT];
    let c = Chain::new([1; 32], vec![p.clone(); 4]).unwrap();
    let json = c.to_json().unwrap();
    assert!(
        json.len() > MAX_PACKAGE && json.len() <= MAX_CHAIN_PACKAGE,
        "{}",
        json.len()
    );
    assert_eq!(Chain::from_json(&json).unwrap(), c);
    // 64 maximal links overflow the chain limit and the writer refuses.
    let c = Chain::new([1; 32], vec![p; 64]).unwrap();
    assert!(c.to_json().is_err());
}

#[test]
fn sixty_four_real_links_round_trip_and_sixty_five_are_rejected() {
    let p = real_proof().clone();
    let c = Chain::new(p.statement.profile, vec![p.clone(); 64]).unwrap();
    let json = c.to_json().unwrap();
    assert!(json.len() <= MAX_CHAIN_PACKAGE);
    assert_eq!(Chain::from_json(&json).unwrap(), c);
    assert!(Chain::new(p.statement.profile, vec![p; 65]).is_err());
    let mut v: Json = serde_json::from_slice(&json).unwrap();
    let link = v["links"][0].clone();
    v["links"].as_array_mut().unwrap().push(link);
    assert!(Chain::from_json(&serde_json::to_vec(&v).unwrap()).is_err());
    // 0 links is in the language.
    let empty = Chain::new([1; 32], vec![]).unwrap();
    assert_eq!(Chain::from_json(&empty.to_json().unwrap()).unwrap(), empty);
}

#[test]
fn transcript_length_rule_is_enforced_by_both_recognisers() {
    for n in [0usize, 31, 33, 48, MAX_TRANSCRIPT - 1, MAX_TRANSCRIPT + 32] {
        let mut p = small_proof();
        p.transcript = vec![0; n];
        assert!(p.check_size().is_err(), "{n}");
        assert!(p.to_json().is_err(), "{n}");
        let mut v: Json = serde_json::from_slice(&small_proof().to_json().unwrap()).unwrap();
        v["transcript"] = Json::Array(vec![Json::from(0u8); n]);
        assert!(
            Proof::from_json(&serde_json::to_vec(&v).unwrap()).is_err(),
            "{n}"
        );
        let mut v: Json = serde_json::from_slice(&small_chain().to_json().unwrap()).unwrap();
        v["links"][1]["transcript"] = Json::Array(vec![Json::from(0u8); n]);
        assert!(
            Chain::from_json(&serde_json::to_vec(&v).unwrap()).is_err(),
            "{n}"
        );
    }
    for n in [32usize, 64, MAX_TRANSCRIPT] {
        let mut p = small_proof();
        p.transcript = vec![0; n];
        assert!(p.check_size().is_ok(), "{n}");
        assert_eq!(Proof::from_json(&p.to_json().unwrap()).unwrap(), p);
    }
}

/// REQ-3508 (d): the prover's output passes the same transcript rule, so a
/// 16,416-byte transcript can never leave `prove`.
#[test]
fn prove_output_rule_rejects_transcript_over_16_384_bytes() {
    let mut p = real_proof().clone();
    assert!(p.check_size().is_ok());
    p.transcript.resize(16_416, 0);
    assert_eq!(p.transcript.len(), MAX_TRANSCRIPT + 32);
    assert!(p.check_size().is_err());
    assert!(p.to_json().is_err());
}

#[test]
fn member_order_is_not_significant() {
    let p = small_proof();
    let mut v: Json = serde_json::from_slice(&p.to_json().unwrap()).unwrap();
    let st = v["statement"].take();
    let tr = v["transcript"].take();
    let text = format!(
        r#"{{"transcript":{tr},"statement":{{"batch":{},"after":{{"state":{},"accepted":{}}},"before":{},"profile":{}}}}}"#,
        st["batch"], st["after"]["state"], st["after"]["accepted"], st["before"], st["profile"]
    );
    assert!(!text.contains(r#"{"statement""#));
    assert_eq!(Proof::from_json(text.as_bytes()).unwrap(), p);
    let c = small_chain();
    let v: Json = serde_json::from_slice(&c.to_json().unwrap()).unwrap();
    let text = format!(r#"{{"links":{},"profile":{}}}"#, v["links"], v["profile"]);
    assert_eq!(Chain::from_json(text.as_bytes()).unwrap(), c);
    // A missing member is not an optional member.
    let text = format!(r#"{{"links":{}}}"#, v["links"]);
    assert!(Chain::from_json(text.as_bytes()).is_err());
    assert!(Proof::from_json(format!(r#"{{"transcript":{tr}}}"#).as_bytes()).is_err());
}

fn h32() -> impl Strategy<Value = [u8; 32]> {
    any::<[u8; 32]>()
}
fn checkpoint() -> impl Strategy<Value = Checkpoint> {
    (h32(), h32()).prop_map(|(accepted, state)| Checkpoint { accepted, state })
}
fn statement() -> impl Strategy<Value = Statement> {
    (h32(), checkpoint(), checkpoint(), h32()).prop_map(|(profile, before, after, batch)| {
        Statement {
            profile,
            before,
            after,
            batch,
        }
    })
}
/// Transcripts of every allowed length: 32..=16,384 in 32-byte steps.
fn proof() -> impl Strategy<Value = Proof> {
    (statement(), 1..=MAX_TRANSCRIPT / 32).prop_flat_map(|(statement, k)| {
        proptest::collection::vec(any::<u8>(), k * 32).prop_map(move |transcript| Proof {
            statement: statement.clone(),
            transcript,
        })
    })
}
proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]
    #[test]
    fn proof_round_trips(p in proof()) {
        let json = p.to_json().unwrap();
        prop_assert!(json.len() <= MAX_PACKAGE);
        prop_assert_eq!(Proof::from_json(&json).unwrap(), p);
    }
    #[test]
    fn chain_round_trips(profile in h32(), links in proptest::collection::vec(proof(), 0..=3)) {
        let c = Chain::new(profile, links).unwrap();
        let json = c.to_json().unwrap();
        prop_assert!(json.len() <= MAX_CHAIN_PACKAGE);
        prop_assert_eq!(Chain::from_json(&json).unwrap(), c);
    }
}
