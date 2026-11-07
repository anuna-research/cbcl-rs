//! Deterministic, authenticated inputs for the governed drawing experiment.
use super::{encoded, Result};
use cbcl_core::{
    admission::AdmissionGate,
    canonical::dialect_hash,
    dialect::{base_dialect, Dialect, PerformativeDef},
    equivocation::message_content_hash,
    message::{Message, WrapperType},
    protocol::{CausalProtocol, NodeRef, StepDecl},
    role::{parse_roles, AgentKey, Endpoint, RoleAnnotation},
    sexpr::SExpr,
    shape::{ShapeConstraint, ShapeRule, TypeConstraint},
    state::{Act, Entry, Rule, StateClause},
    store::ContentHash,
};
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

pub const THREAD: &str = "drawing-checkpoint/v1";
const DIALECT: &str = "drawing-checkpoint";
fn parse(s: &str) -> Message {
    Message::try_from(&s.parse::<SExpr>().expect("fixture syntax")).expect("fixture message")
}
pub fn signing_keys() -> Vec<SigningKey> {
    (1..=4).map(|i| SigningKey::from_bytes(&[i; 32])).collect()
}
pub fn roster(keys: &[SigningKey]) -> Vec<VerifyingKey> {
    keys.iter().map(SigningKey::verifying_key).collect()
}
pub fn endpoint() -> Endpoint {
    Endpoint {
        role: "editors".into(),
        occupant: Some(AgentKey("@m0".into())),
    }
}
#[derive(Clone, Debug, Serialize, Deserialize)]
pub(super) struct Wire {
    pub message: Message,
    pub signer: usize,
    pub signature: Vec<u8>,
    /// Emitted by the author at edit creation, so later redaction needs no key.
    pub root_signature: Vec<u8>,
}
impl Wire {
    pub fn signed(message: Message, signer: usize, keys: &[SigningKey]) -> Self {
        let signature = keys[signer].sign(&encoded(&message)).to_bytes().to_vec();
        let root = message_content_hash(message.innermost_simple().expect("simple fixture"));
        let root_signature = keys[signer]
            .sign(&cbcl_core::attest::attestation_v3_preimage(
                &cbcl_core::keyid::SignatureSuite::Ed25519,
                &root,
            ))
            .to_bytes()
            .to_vec();
        Self {
            message,
            signer,
            signature,
            root_signature,
        }
    }
    pub fn id(&self) -> String {
        message_content_hash(self.message.innermost_simple().expect("simple fixture"))
    }
    pub fn act(&self) -> Act {
        Act::from_message(self.message.clone(), &format!("@m{}", self.signer)).expect("fixture act")
    }
    pub fn authenticate(&self, d: &Dialect, keys: &[VerifyingKey]) -> Result<Act> {
        if keys.len() != 4
            || self.signer >= 4
            || d.hash.as_deref() != Some(dialect_hash(d).as_str())
            || !cbcl_core::r7::r7_violations(d).is_empty()
        {
            return Err("invalid roster or dialect pin".into());
        }
        let sig = Signature::from_slice(&self.signature).map_err(|e| e.to_string())?;
        keys[self.signer]
            .verify_strict(&encoded(&self.message), &sig)
            .map_err(|e| e.to_string())?;
        let simple = self
            .message
            .innermost_simple()
            .ok_or("simple payload required")?;
        let root_sig = Signature::from_slice(&self.root_signature).map_err(|e| e.to_string())?;
        keys[self.signer]
            .verify_strict(
                &cbcl_core::attest::attestation_v3_preimage(
                    &cbcl_core::keyid::SignatureSuite::Ed25519,
                    &message_content_hash(simple),
                ),
                &root_sig,
            )
            .map_err(|e| e.to_string())?;
        let mut cur = &self.message;
        let root = matches!(
            cur,
            Message::Wrapped {
                wrapper: WrapperType::WithRoles,
                ..
            }
        );
        if root {
            let Message::Wrapped {
                params, content, ..
            } = cur
            else {
                unreachable!()
            };
            let expected: Vec<SExpr> = vec![
                "((editors @m0 @m1 @m2 @m3))".parse().unwrap(),
                ":dialect".parse().unwrap(),
                d.hash.as_ref().unwrap().parse().unwrap(),
            ];
            if params != &expected || self.signer != 0 {
                return Err("invalid root cast".into());
            }
            cur = content;
        }
        let Message::Wrapped {
            wrapper: WrapperType::Signed,
            params,
            content,
        } = cur
        else {
            return Err("missing signed wrapper".into());
        };
        let expected: Vec<SExpr> = vec![
            format!("@m{}", self.signer).parse().unwrap(),
            "\"detached\"".parse().unwrap(),
        ];
        if params != &expected {
            return Err("wrapper signer mismatch".into());
        }
        cur = content;
        if !root {
            let Message::Dialect {
                dialect_name,
                inner,
            } = cur
            else {
                return Err("missing dialect wrapper".into());
            };
            if dialect_name != &d.name || dialect_name != DIALECT {
                return Err("wrong dialect".into());
            }
            cur = inner;
        }
        let Message::Simple {
            performative,
            sender,
            thread,
            caused_by,
            ..
        } = cur
        else {
            return Err("unexpected wrapper".into());
        };
        if sender.as_deref() != Some(format!("@m{}", self.signer).as_str())
            || thread.as_deref() != Some(THREAD)
        {
            return Err("sender or thread mismatch".into());
        }
        if root {
            if performative.name() != "hello"
                || !matches!(caused_by, Some(cbcl_core::message::CausedBy::Begin))
                || !cur.recipient_set().is_empty()
            {
                return Err("invalid root context".into());
            }
        } else {
            if !matches!(performative.name(), "open" | "paint" | "erase")
                || cur.recipient_set() != ["@m0", "@m1", "@m2", "@m3"].into_iter().collect()
            {
                return Err("invalid verb or recipients".into());
            }
            if !matches!(caused_by, Some(cbcl_core::message::CausedBy::Single(h)) if h.strip_prefix("sha256:").is_some_and(|s| s.len()==64 && s.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))))
            {
                return Err("explicit native predecessor required".into());
            }
        }
        cbcl_core::r7::verify_state_shape(d, cur).map_err(|e| format!("{e:?}"))?;
        for shape in d
            .shapes
            .iter()
            .filter(|s| s.performative == performative.name())
        {
            shape
                .check(&SExpr::from(cur.clone()))
                .map_err(|e| format!("{e:?}"))?;
        }
        Ok(self.act())
    }
    #[cfg(test)]
    pub fn envelope(&self, keys: &[SigningKey]) -> cbcl_core::envelope::RedactedEnvelope {
        let header = cbcl_core::equivocation::attestation_header_for(
            self.message.innermost_simple().expect("simple fixture"),
        )
        .expect("complete header");
        let signature = keys[self.signer]
            .sign(&cbcl_core::attest::attestation_preimage(&header))
            .to_bytes()
            .to_vec();
        cbcl_core::envelope::RedactedEnvelope { header, signature }
    }
}
// This fixture helper mirrors the independent fields of one signed drawing edit.
#[allow(clippy::too_many_arguments)]
pub fn edit(
    key: &str,
    value: &str,
    erase: bool,
    replaces: &[String],
    predecessor: &str,
    nonce: u64,
    signer: usize,
    keys: &[SigningKey],
) -> Wire {
    let refs = replaces
        .iter()
        .map(|s| serde_json::to_string(s).unwrap())
        .collect::<Vec<_>>()
        .join(" ");
    let value = if erase {
        String::new()
    } else {
        format!(" :value {}", serde_json::to_string(value).unwrap())
    };
    Wire::signed(parse(&format!("(signed @m{signer} \"detached\" (lang {DIALECT} ({} (@m0 @m1 @m2 @m3) \"{nonce}\" :shape {}{value} :replaces ({refs}) :sender @m{signer} :thread \"{THREAD}\" :caused-by {predecessor})))", if erase { "erase" } else { "paint" }, serde_json::to_string(key).unwrap())), signer, keys)
}
pub(super) struct Fixture {
    pub dialect: Dialect,
    pub root: Wire,
    pub edits: Vec<Wire>,
    pub keys: Vec<SigningKey>,
}
impl Fixture {
    pub fn new(n: usize, depth: usize, offline_lag: usize) -> Self {
        assert!(depth > 0, "depth must be positive");
        let keys = signing_keys();
        let mut d = base_dialect();
        d.name = DIALECT.into();
        d.roles = parse_roles(&"((* editors))".parse().unwrap()).unwrap();
        d.performatives = ["open", "paint", "erase"]
            .into_iter()
            .map(|name| PerformativeDef {
                name: name.into(),
                params: vec![],
                template: "t".parse().unwrap(),
                role: Some(RoleAnnotation {
                    from: "editors".into(),
                    to: ["editors".into()].into_iter().collect(),
                }),
            })
            .collect();
        d.state = Some(StateClause {
            entries: vec![Entry::Field {
                name: "drawing".into(),
                rule: Rule::ValuesPerKey {
                    verb: "paint".into(),
                    key: "shape".into(),
                    value: "value".into(),
                    delete: Some("erase".into()),
                },
            }],
        });
        d.shapes = ["paint", "erase"]
            .into_iter()
            .map(|verb| ShapeConstraint {
                performative: verb.into(),
                rules: [
                    ("shape", TypeConstraint::String),
                    ("replaces", TypeConstraint::List),
                ]
                .into_iter()
                .chain((verb == "paint").then_some(("value", TypeConstraint::String)))
                .map(|(keyword, ty)| ShapeRule::Require {
                    keyword: keyword.into(),
                    type_constraint: Some(ty),
                    children: vec![],
                })
                .collect(),
            })
            .collect();
        let mut steps = BTreeMap::new();
        let single = |s: &str| NodeRef::Single(s.into());
        let alternatives = |i| {
            NodeRef::Any(
                [format!("paint#{i}"), format!("erase#{i}")]
                    .into_iter()
                    .collect(),
            )
        };
        steps.insert(
            "begin".into(),
            StepDecl {
                performative: "begin".into(),
                predecessors: vec![],
                successors: vec![single("open")],
            },
        );
        steps.insert(
            "open".into(),
            StepDecl {
                performative: "open".into(),
                predecessors: vec![single("begin")],
                successors: vec![alternatives(1)],
            },
        );
        for i in 1..=depth {
            for verb in ["paint", "erase"] {
                let name = format!("{verb}#{i}");
                steps.insert(
                    name.clone(),
                    StepDecl {
                        performative: name,
                        predecessors: vec![if i == 1 {
                            single("open")
                        } else {
                            alternatives(i - 1)
                        }],
                        successors: if i == depth {
                            vec![]
                        } else {
                            vec![alternatives(i + 1)]
                        },
                    },
                );
            }
        }
        d.causal_protocol = Some(CausalProtocol { steps });
        d.hash = Some(dialect_hash(&d));
        let root = Wire::signed(parse(&format!("(with-roles ((editors @m0 @m1 @m2 @m3)) :dialect {} (signed @m0 \"detached\" (hello :sender @m0 :thread \"{THREAD}\" :caused-by begin)))", d.hash.as_ref().unwrap())), 0, &keys);
        let open = Wire::signed(parse(&format!("(signed @m0 \"detached\" (lang {DIALECT} (open (@m0 @m1 @m2 @m3) \"open\" :sender @m0 :thread \"{THREAD}\" :caused-by {})))", root.id())), 0, &keys);
        let mut edits = vec![open];
        let mut heads = BTreeMap::<String, String>::new();
        for i in 0..n {
            let key = format!("shape-{}", i % 8);
            let refs: Vec<_> = heads.get(&key).cloned().into_iter().collect();
            let pred = if i % depth == 0 {
                edits[0].id()
            } else {
                edits.last().unwrap().id()
            };
            let signer = i % if i < n.saturating_sub(offline_lag) {
                4
            } else {
                3
            };
            let wire = edit(
                &key,
                r##"{"points":[[10,20],[30,40]],"width":3,"color":"#3366cc"}"##,
                i % 13 == 0,
                &refs,
                &pred,
                i as u64,
                signer,
                &keys,
            );
            heads.insert(key, wire.act().address);
            edits.push(wire);
        }
        Self {
            dialect: d,
            root,
            edits,
            keys,
        }
    }
}
pub struct Gate {
    // Authenticate each immutable transport attempt once. Message-only lookup
    // cannot distinguish a valid replay from corrupt detached signature bytes.
    attempts: BTreeMap<Vec<u8>, Result<ContentHash>>,
    authenticated_messages: BTreeMap<Vec<u8>, ContentHash>,
}
impl Gate {
    pub fn new(dialect: &Dialect, roster: &[VerifyingKey], wires: &[Wire]) -> Self {
        let mut gate = Self {
            attempts: BTreeMap::new(),
            authenticated_messages: BTreeMap::new(),
        };
        for wire in wires {
            let attempt = encoded(wire);
            if gate.attempts.contains_key(&attempt) {
                continue;
            }
            let result = wire
                .authenticate(dialect, roster)
                .map(|_| ContentHash(wire.id()));
            if let Ok(hash) = &result {
                gate.authenticated_messages
                    .insert(encoded(&wire.message), hash.clone());
            }
            gate.attempts.insert(attempt, result);
        }
        gate
    }
    pub fn check_attempt(&self, wire: &Wire) -> Result<ContentHash> {
        self.attempts
            .get(&encoded(wire))
            .ok_or("unregistered transport attempt")?
            .clone()
    }
}
impl AdmissionGate for Gate {
    fn authenticate(&self, message: &Message) -> Result<ContentHash> {
        self.authenticated_messages
            .get(&encoded(message))
            .cloned()
            .ok_or("message absent from authenticated input set".into())
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use cbcl_core::admission::{AdmissionMonitor, AdmissionState};
    use cbcl_core::attest::attestation_preimage;
    #[test]
    fn full_core_replay() {
        for (n, depth, lag) in [(0, 1, 0), (40, 1, 9), (80, 7, 20)] {
            let f = Fixture::new(n, depth, lag);
            assert!(
                cbcl_core::r7::r7_violations(&f.dialect).is_empty(),
                "{:?}",
                cbcl_core::r7::r7_violations(&f.dialect)
            );
            let wires: Vec<_> = std::iter::once(f.root.clone())
                .chain(f.edits.clone())
                .collect();
            let gate = Gate::new(&f.dialect, &roster(&f.keys), &wires);
            let mut monitor =
                AdmissionMonitor::new(f.dialect.clone(), endpoint(), f.root.message.clone(), gate)
                    .unwrap();
            for wire in &f.edits {
                monitor.receive(wire.message.clone()).unwrap();
            }
            monitor.drain_ready();
            for wire in &wires {
                assert_eq!(
                    monitor.state(&ContentHash(wire.id())),
                    Some(&AdmissionState::Accepted)
                );
            }
        }
    }
    #[test]
    fn complete_message_signature_and_sender_binding() {
        let f = Fixture::new(1, 1, 0);
        let keys = roster(&f.keys);
        let mut bad = f.root.clone();
        if let Message::Wrapped { params, .. } = &mut bad.message {
            params[0] = "((editors @m0 @m1 @m2 @intruder))".parse().unwrap();
        }
        assert!(bad.authenticate(&f.dialect, &keys).is_err());
        let bad = Wire::signed(f.edits[1].message.clone(), 1, &f.keys);
        assert!(bad.authenticate(&f.dialect, &keys).is_err());
        let mut bad = f.edits[1].clone();
        fn simple_mut(message: &mut Message) -> &mut Message {
            match message {
                Message::Wrapped { content, .. } => simple_mut(content),
                Message::Dialect { inner, .. } => simple_mut(inner),
                _ => message,
            }
        }
        if let Message::Simple { sender, .. } = simple_mut(&mut bad.message) {
            *sender = Some("@m2".into());
        }
        let bad = Wire::signed(bad.message, 0, &f.keys);
        assert!(bad.authenticate(&f.dialect, &keys).is_err());
        let mut bad = f.edits[1].clone(); // first edit is erase: :value is forbidden
        if let Message::Simple { params, .. } = simple_mut(&mut bad.message) {
            params.extend([":value".parse().unwrap(), "\"extra\"".parse().unwrap()]);
        }
        let bad = Wire::signed(bad.message, 0, &f.keys);
        assert!(bad.authenticate(&f.dialect, &keys).is_err());
        let envelope = f.edits[1].envelope(&f.keys);
        keys[f.edits[1].signer]
            .verify_strict(
                &attestation_preimage(&envelope.header),
                &Signature::from_slice(&envelope.signature).unwrap(),
            )
            .unwrap();
        assert_eq!(envelope.header.content_hash, f.edits[1].id());
    }
}
