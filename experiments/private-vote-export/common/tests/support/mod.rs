use cbcl_core::{
    intend::{canonical_text, intend, Instance},
    role::AgentKey,
    state::Act,
    store::ThreadId,
};
use ed25519_dalek::{Signer, SigningKey};
use private_vote_common::{closure_digest, message_digest, Input, Participant, Record, DIALECT};

pub fn resign(i: &mut Input) {
    let keys = keys();
    for n in 0..i.messages.len() {
        let digest = message_digest(i, &i.messages[n]).unwrap();
        i.messages[n].signature = keys[i.messages[n].signer].sign(&digest).to_bytes().to_vec();
    }
    let digest = closure_digest(i).unwrap();
    i.closure_signatures = keys
        .iter()
        .map(|k| k.sign(&digest).to_bytes().to_vec())
        .collect();
}
pub fn keys() -> [SigningKey; 2] {
    [
        SigningKey::from_bytes(&[11; 32]),
        SigningKey::from_bytes(&[22; 32]),
    ]
}
/// Public, deliberately known synthetic signing keys. Never use for real data.
pub fn fixture(replacement: bool) -> Input {
    let keys = keys();
    let mut i = Input {
        dialect: DIALECT.into(),
        thread: "synthetic-vote-1".into(),
        participants: ["@alice", "@bob"]
            .iter()
            .zip(&keys)
            .map(|(label, k)| Participant {
                label: (*label).into(),
                key: k.verifying_key().to_bytes(),
            })
            .collect(),
        messages: vec![],
        salt: [37; 32],
        closure_signatures: vec![],
    };
    let registry = cbcl_parser::state_exports::parse_and_install_dialect(
        &cbcl_parser::parse(DIALECT).unwrap(),
    )
    .unwrap();
    let d = registry.iter().last().unwrap();
    // intend() authors subsequent acts only; install a parsed native opener.
    let opener = cbcl_parser::parse_message(&cbcl_parser::parse(
        r#"(lang private-vote (open (@alice @bob) :question "Ship synthetic example?" :options ("yes" "no") :from @alice :thread "synthetic-vote-1" :caused-by begin))"#,
    ).unwrap()).unwrap();
    i.messages.push(Record {
        signer: 0,
        canonical: canonical_text(&opener),
        signature: vec![],
    });
    let mut acts = vec![Act::from_message(opener, "@alice").unwrap()];
    let mut issue = |signer: usize, verb: &str, fields: &[(&str, &str)]| {
        let inst = Instance::new(d, ThreadId(i.thread.clone()), &acts).unwrap();
        let fields = fields
            .iter()
            .map(|(k, v)| ((*k).into(), cbcl_parser::parse(v).unwrap()))
            .collect();
        let who = &i.participants[signer].label;
        let msg = intend(&inst, &AgentKey(who.clone()), verb, fields).unwrap();
        i.messages.push(Record {
            signer,
            canonical: canonical_text(&msg),
            signature: vec![],
        });
        acts.push(Act::from_message(msg, who).unwrap());
    };
    issue(
        1,
        "discuss",
        &[("text", "\"Private synthetic discussion\"")],
    );
    issue(
        0,
        "vote",
        &[
            ("choice", "\"yes\""),
            ("clock", "\"hlc-0000000000000001-00000000\""),
        ],
    );
    issue(
        1,
        "vote",
        &[
            ("choice", "\"no\""),
            ("clock", "\"hlc-0000000000000002-00000000\""),
        ],
    );
    if replacement {
        issue(
            0,
            "vote",
            &[
                ("choice", "\"no\""),
                ("clock", "\"hlc-0000000000000003-00000000\""),
            ],
        );
    }
    resign(&mut i);
    i
}
