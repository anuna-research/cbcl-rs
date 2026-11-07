mod support;
use private_vote_common::{compute, Input, MAX_INPUT};
fn run(i: &Input) -> Result<private_vote_common::Journal, String> {
    compute(&serde_json::to_vec(i).unwrap())
}
#[test]
fn mixed_and_replacement_native_tallies() {
    let i = support::fixture(false);
    let j = run(&i).unwrap();
    assert_eq!(j.ballot_count, 2);
    assert_eq!(j.covered_count, 4);
    assert_eq!(j.tally["yes"], 1);
    assert_eq!(j.tally["no"], 1);
    let j = run(&support::fixture(true)).unwrap();
    assert_eq!(j.ballot_count, 2);
    assert_eq!(j.tally["no"], 2);
    assert_eq!(j.tally.get("yes").copied().unwrap_or(0), 0);
}
#[test]
fn delivery_order_does_not_change_public_statement() {
    let mut i = support::fixture(false);
    let j = run(&i).unwrap();
    i.messages.reverse();
    assert_eq!(run(&i).unwrap(), j);
}
#[test]
fn authentication_and_exact_set_negatives() {
    let base = support::fixture(false);
    for mutation in 0..10 {
        let mut i = base.clone();
        match mutation {
            0 => i.messages[0].signature[0] ^= 1,
            1 => i.closure_signatures[0][0] ^= 1,
            2 => {
                i.closure_signatures.pop();
            }
            3 => {
                i.messages.pop();
            }
            4 => i.messages.push(i.messages[0].clone()),
            5 => i.participants[1].key = i.participants[0].key,
            6 => i.participants[1].label = i.participants[0].label.clone(),
            7 => i.thread.push('x'),
            8 => i.salt[0] ^= 1,
            _ => i.messages[0].signer = 2,
        }
        assert!(run(&i).is_err(), "mutation {mutation}");
    }
}
#[test]
fn deliberately_resigned_native_rule_negatives() {
    // Known synthetic keys allow these malformed histories to pass authentication;
    // adversaries without the keys cannot regenerate unanimous closure.
    for mutation in 0..7 {
        let mut i = support::fixture(false);
        match mutation {
            0 => {
                i.messages[2].canonical = i.messages[2]
                    .canonical
                    .replace("hlc-0000000000000001-00000000", "broken")
            }
            1 => {
                i.messages[2].canonical = i.messages[2]
                    .canonical
                    .replace(":from @alice", ":from @bob")
            }
            2 => {
                i.messages[2].canonical = i.messages[2]
                    .canonical
                    .replace("synthetic-vote-1", "other-thread")
            }
            3 => {
                i.messages[2].canonical = i.messages[2]
                    .canonical
                    .replace("lang private-vote", "lang other-vote")
            }
            4 => {
                i.messages.remove(0);
            }
            5 => i.messages.push(i.messages[2].clone()),
            _ => i.messages[2].canonical = i.messages[2].canonical.replace("\"yes\"", "\"maybe\""),
        }
        support::resign(&mut i);
        assert!(run(&i).is_err(), "native mutation {mutation}");
    }
}
#[test]
fn closed_json_and_size_boundary() {
    assert!(compute(&vec![b' '; MAX_INPUT + 1]).is_err());
    let mut v = serde_json::to_value(support::fixture(false)).unwrap();
    v["unexpected"] = true.into();
    assert!(compute(&serde_json::to_vec(&v).unwrap()).is_err());
}

#[test]
fn invalid_message_signature() {
    let mut input = support::fixture(false);
    input.messages[2].signature[0] ^= 1;
    assert_eq!(run(&input).unwrap_err(), "invalid signature");
}

#[test]
fn missing_closure_signer() {
    let mut input = support::fixture(false);
    input.closure_signatures.pop();
    assert_eq!(run(&input).unwrap_err(), "missing closure signer");
}

#[test]
fn concurrent_same_signer_votes_use_hlc_in_both_delivery_orders() {
    let mut input = support::fixture(true);
    // The lower clock votes yes; the higher clock votes no. Neither names
    // the other as a replacement, so HLC arbitration must decide the ballot.
    let last = input.messages.len() - 1;
    let parsed =
        cbcl_parser::parse_message(&cbcl_parser::parse(&input.messages[last].canonical).unwrap())
            .unwrap();
    let act = cbcl_core::state::Act::from_message(parsed, "@alice").unwrap();
    let replaces = cbcl_core::serializer::serialize(&act.fields["replaces"]);
    assert_ne!(
        replaces, "()",
        "fixture must include an explicit replacement"
    );
    input.messages[last].canonical = input.messages[last]
        .canonical
        .replace(&format!(":replaces {replaces}"), ":replaces ()");
    support::resign(&mut input);
    let expected = run(&input).unwrap();
    assert_eq!(expected.ballot_count, 2);
    assert_eq!(expected.tally["no"], 2);
    assert_eq!(expected.tally.get("yes").copied().unwrap_or(0), 0);
    input.messages.reverse();
    assert_eq!(run(&input).unwrap(), expected);
}

#[test]
fn explicit_replacement_retires_higher_clock_same_signer_ballot() {
    let mut input = support::fixture(true);
    // The original yes ballot has clock 1. Its explicit replacement has
    // clock zero, so only native retirement can make the no ballot prevail.
    let last = input.messages.len() - 1;
    input.messages[last].canonical = input.messages[last].canonical.replace(
        "hlc-0000000000000003-00000000",
        "hlc-0000000000000000-00000000",
    );
    support::resign(&mut input);
    let journal = run(&input).unwrap();
    assert_eq!(journal.ballot_count, 2);
    assert_eq!(journal.tally["no"], 2);
    assert_eq!(journal.tally.get("yes").copied().unwrap_or(0), 0);
}

#[test]
fn roster_member_can_abstain_and_still_sign_closure() {
    let mut input = support::fixture(false);
    input.messages.remove(3); // Bob retains discussion and closure, but no ballot.
    support::resign(&mut input);
    let journal = run(&input).unwrap();
    assert_eq!(journal.participants.len(), 2);
    assert_eq!(journal.covered_count, 3);
    assert_eq!(journal.ballot_count, 1);
    assert_eq!(journal.tally["yes"], 1);
    assert_eq!(journal.tally.get("no").copied().unwrap_or(0), 0);
}

#[test]
fn unanimously_closed_outsider_reaches_signer_guard() {
    use ed25519_dalek::Signer;
    let mut input = support::fixture(false);
    input.messages[2].signer = input.participants.len();
    // This is a deliberately signed synthetic closure over the outsider set.
    // Do not use resign(), whose message-signing key lookup requires a member.
    let digest = private_vote_common::closure_digest(&input).unwrap();
    input.closure_signatures = support::keys()
        .iter()
        .map(|key| key.sign(&digest).to_bytes().to_vec())
        .collect();
    assert_eq!(run(&input).unwrap_err(), "outsider signer");
}

#[test]
fn signed_dangling_predecessor_reaches_unresolved_causality() {
    let mut input = support::fixture(false);
    let message = &mut input.messages[2].canonical;
    let start = message.find(":caused-by ").unwrap() + ":caused-by ".len();
    let end = start
        + message[start..]
            .find(|c: char| c.is_whitespace() || c == ')')
            .unwrap();
    assert!(message[start..end].starts_with("sha256-"));
    message.replace_range(start..end, &format!("sha256-{}", "0".repeat(64)));
    support::resign(&mut input);
    assert_eq!(run(&input).unwrap_err(), "unresolved causality");
}
