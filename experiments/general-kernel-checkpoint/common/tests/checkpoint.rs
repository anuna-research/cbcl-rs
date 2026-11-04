use checkpoint_common::{compute, Input};
use std::{fs, path::Path};
fn fixture(name: &str) -> Input {
    serde_json::from_slice(
        &fs::read(
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../fixtures")
                .join(name),
        )
        .unwrap(),
    )
    .unwrap()
}
fn run(input: &Input) -> Result<checkpoint_common::Computed, String> {
    compute(&serde_json::to_vec(input).unwrap())
}
#[test]
fn fixtures_match_expected_bytes_and_permutations() {
    for name in [
        "drawing-0",
        "drawing-1",
        "drawing-8",
        "status-0",
        "status-1",
        "status-8",
        "checklist-role",
        "ancestor-status",
    ] {
        let mut input = fixture(&format!("{name}.json"));
        let original = run(&input).unwrap();
        let expected = fs::read_to_string(
            Path::new(env!("CARGO_MANIFEST_DIR")).join(format!("../fixtures/{name}-state.json")),
        )
        .unwrap();
        assert_eq!(
            original.state, expected,
            "canonical native bytes differ for {name}"
        );
        input.messages.reverse();
        let reversed = run(&input).unwrap();
        assert_eq!(original.journal, reversed.journal);
        assert_eq!(original.state, reversed.state);
    }
}
#[test]
fn mixed_thread_rejected() {
    let mut input = fixture("drawing-1.json");
    input.thread = "other-thread".into();
    assert!(run(&input)
        .err()
        .unwrap()
        .contains("thread context mismatch"));
}
#[test]
fn nested_dialect_mismatch_rejected() {
    let mut input = fixture("drawing-1.json");
    input.messages[1].canonical = format!("(lang other-dialect {})", input.messages[1].canonical);
    assert!(run(&input)
        .err()
        .unwrap()
        .contains("dialect context mismatch"));
}
#[test]
fn duplicate_addresses_rejected() {
    let mut input = fixture("drawing-1.json");
    input.messages.push(input.messages[0].clone());
    assert!(run(&input).err().unwrap().contains("duplicate act address"));
}
#[test]
fn unresolved_dependency_rejected() {
    let mut input = fixture("drawing-1.json");
    input.messages.remove(0);
    assert!(run(&input)
        .err()
        .unwrap()
        .contains("unresolved causal dependencies"));
}
#[test]
fn noncanonical_rejected() {
    let mut input = fixture("drawing-1.json");
    input.messages[0].canonical.push(' ');
    assert!(run(&input).err().unwrap().contains("noncanonical message"));
}
#[test]
fn invalid_shape_rejected() {
    let mut input = fixture("drawing-1.json");
    input.messages[1].canonical = input.messages[1]
        .canonical
        .replace(":data (", ":bad-data (");
    assert!(run(&input).err().unwrap().contains("rejected:"));
}
#[test]
fn invalid_dialect_rejected() {
    let mut input = fixture("drawing-1.json");
    input.dialect = "(not-a-definition)".into();
    assert!(run(&input).is_err());
}
#[test]
fn schema_and_byte_bounds_rejected() {
    assert!(compute(br#"{"dialect":"x","thread":"t","messages":[],"extra":true}"#).is_err());
    assert!(compute(&vec![b' '; checkpoint_common::MAX_INPUT + 1]).is_err());
    let mut input = fixture("drawing-1.json");
    input.messages[0].signer = "x".repeat(1025);
    assert!(run(&input).is_err());
}
#[test]
fn source_closure_and_message_set_bound() {
    let input = fixture("drawing-1.json");
    let baseline = run(&input).unwrap();
    let mut changed = input.clone();
    changed.dialect.push(' ');
    let other = run(&changed).unwrap();
    assert_eq!(baseline.state, other.state);
    assert_ne!(
        baseline.journal.dialect_sources_hash,
        other.journal.dialect_sources_hash
    );
    let mut changed = input.clone();
    changed.messages[1].signer = "@other".into();
    let other = run(&changed).unwrap();
    assert_ne!(baseline.journal.messages_hash, other.journal.messages_hash);
    assert_ne!(
        baseline.journal.state_hash,
        checkpoint_common::state_hash("{}")
    );
}

#[test]
fn missing_ancestor_rejected_and_ancestor_closure_committed() {
    let mut input = fixture("ancestor-status.json");
    let baseline = run(&input).unwrap();
    input.dialect = input.dialect.replace("@author", "@another-author");
    let changed = run(&input).unwrap();
    assert_eq!(baseline.state, changed.state);
    assert_ne!(
        baseline.journal.dialect_sources_hash,
        changed.journal.dialect_sources_hash
    );
    let mut source=cbcl_parser::parse(&input.dialect).unwrap();
    let cbcl_core::sexpr::SExpr::List(forms)=&mut source else {panic!("fixture must be a chain")};
    forms.remove(1); // remove the parent whose macro the leaf actually uses
    input.dialect=cbcl_core::serializer::serialize(&source);
    assert!(run(&input).is_err(), "missing ancestor was accepted");
}

#[test]
fn sender_outside_cast_rejected() {
    let mut input=fixture("checklist-role.json");
    input.messages[2].signer="@outside-cast".into();
    input.messages[2].canonical=input.messages[2].canonical.replace("signed @bo ","signed @outside-cast ").replace(":from @bo",":from @outside-cast");
    assert!(run(&input).is_err());
}
