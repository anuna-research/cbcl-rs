use cbcl_core::{
    canonical::canonical_encode,
    dialect::DialectRegistry,
    intend::Instance,
    quorum::{Authentication, Certificate, Context, Limits, Vote, VoteKind},
    sexpr::{Atom, SExpr},
    state::Act,
    store::{MessageStore, ThreadId},
};
use cbcl_parser::{parse, parse_dialect, parse_message};
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
pub type Result<T> = std::result::Result<T, String>;
pub const VALIDATORS: [&str; 4] = ["@v0", "@v1", "@v2", "@v3"];
pub const THREAD: &str = "quorum-e2e";
const DIALECT: &str = include_str!("../../../dialects/example-collective-tickets.cbcl");

/// Explicit benchmark-only attacks by @v0, never used by the core protocol.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ByzantineMode {
    #[default]
    None,
    Withhold,
    Equivocate,
    InvalidFlood,
}

#[derive(Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SignedAct {
    pub act: Act,
    pub signature: Vec<u8>,
}
#[derive(Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Setup {
    pub public_keys: BTreeMap<String, [u8; 32]>,
    pub genesis: Vec<SignedAct>,
    pub transactions: usize,
    pub delay_ms: u64,
    pub silent_validators: usize,
    #[serde(default)]
    pub byzantine_mode: ByzantineMode,
    pub queue_capacity: usize,
    pub journal_batch_size: usize,
    pub journal_batch_wait_ms: u64,
}
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NodeConfig {
    pub setup: Setup,
    pub index: usize,
    pub secret: [u8; 32],
}

pub fn act_preimage(act: &Act) -> Vec<u8> {
    canonical_encode(&SExpr::List(vec![
        SExpr::Atom(Atom::Str("cbcl/quorum-e2e/act/v1".into())),
        SExpr::Atom(Atom::Str(act.signer.clone())),
        SExpr::from(&act.message),
    ]))
}
pub fn sign_act(act: Act, key: &SigningKey) -> SignedAct {
    let signature = key.sign(&act_preimage(&act)).to_bytes().to_vec();
    SignedAct { act, signature }
}
pub fn parse_act(source: &str, signer: &str) -> Result<Act> {
    Act::from_message(
        parse_message(&parse(source).map_err(|e| e.to_string())?).map_err(|e| e.to_string())?,
        signer,
    )
}
#[derive(Clone)]
pub struct Auth {
    pub costs: std::cell::RefCell<crate::profile::AuthCosts>,
    pub keys: BTreeMap<String, VerifyingKey>,
    signatures: BTreeMap<(String, String), Vec<u8>>,
    genesis: Vec<cbcl_core::state::Act>,
    dialect: cbcl_core::dialect::Dialect,
}
impl Auth {
    pub fn new(setup: &Setup) -> Result<Self> {
        let keys = setup
            .public_keys
            .iter()
            .map(|(id, bytes)| {
                VerifyingKey::from_bytes(bytes)
                    .map(|k| (id.clone(), k))
                    .map_err(|e| e.to_string())
            })
            .collect::<Result<_>>()?;
        let mut auth = Self {
            costs: Default::default(),
            keys,
            signatures: BTreeMap::new(),
            genesis: setup.genesis.iter().map(|s| s.act.clone()).collect(),
            dialect: parse_dialect(&parse(DIALECT).map_err(|e| e.to_string())?)
                .map_err(|e| e.to_string())?,
        };
        for signed in &setup.genesis {
            auth.remember(signed);
        }
        Ok(auth)
    }
    fn admitted(&self, act: &Act) -> bool {
        use cbcl_core::{
            message::{Message, WrapperType},
            projection::verify_causal_for_role,
            protocol::VerificationResult,
            role::{AgentKey, Endpoint},
            store::ContentHash,
        };
        let mut cursor = &act.message;
        let mut signed = false;
        loop {
            match cursor {
                Message::Wrapped {
                    wrapper,
                    params,
                    content,
                } => {
                    if *wrapper == WrapperType::Signed {
                        if signed
                            || params.as_slice() != [SExpr::Atom(Atom::Symbol(act.signer.clone()))]
                        {
                            return false;
                        }
                        signed = true;
                    }
                    cursor = content;
                }
                Message::Dialect { inner, .. } => cursor = inner,
                _ => break,
            }
        }
        let Ok(inst) = Instance::new(&self.dialect, ThreadId(THREAD.into()), &self.genesis) else {
            return false;
        };
        let (Some(cast), Some(root)) = (&inst.cast, inst.root) else {
            return false;
        };
        // The signature binds act.signer. Supply that authenticated identity to
        // the ordinary role/causal verifier, as intend does before host signing.
        let message = if act.message.wrapper_type() == Some(WrapperType::WithRoles)
            || act.message.wrapper_type() == Some(WrapperType::Signed)
        {
            act.message.clone()
        } else {
            Message::Wrapped {
                wrapper: WrapperType::Signed,
                params: vec![SExpr::Atom(Atom::Symbol(act.signer.clone()))],
                content: Box::new(act.message.clone()),
            }
        };
        let mut store = inst.store();
        store.append(
            ContentHash(act.address.clone()),
            inst.thread.clone(),
            message.clone(),
        );
        matches!(
            verify_causal_for_role(
                &message,
                &Endpoint {
                    role: String::new(),
                    occupant: Some(AgentKey(act.signer.clone()))
                },
                &self.dialect,
                cast,
                &store,
                &inst.thread,
                &ContentHash(root.address.clone())
            ),
            VerificationResult::Valid
        )
    }
    pub fn remember(&mut self, signed: &SignedAct) {
        self.signatures.insert(
            (signed.act.address.clone(), signed.act.signer.clone()),
            signed.signature.clone(),
        );
    }
}
impl Authentication for Auth {
    fn verify(&self, key: &str, preimage: &[u8], signature: &[u8]) -> bool {
        let start = std::time::Instant::now();
        let valid = self.keys.get(key).is_some_and(|k| {
            Signature::from_slice(signature)
                .is_ok_and(|sig| k.verify_strict(preimage, &sig).is_ok())
        });
        self.costs.borrow_mut().verify.record(start);
        valid
    }
    fn authenticate_act(&self, act: &Act) -> bool {
        let start = std::time::Instant::now();
        let admitted = self.admitted(act);
        self.costs.borrow_mut().admission.record(start);
        admitted
            && self
                .signatures
                .get(&(act.address.clone(), act.signer.clone()))
                .is_some_and(|sig| self.verify(&act.signer, &act_preimage(act), sig))
    }
}
pub fn context(setup: &Setup, auth: &Auth) -> Result<Context> {
    let d =
        parse_dialect(&parse(DIALECT).map_err(|e| e.to_string())?).map_err(|e| e.to_string())?;
    let mut registry = DialectRegistry::new();
    registry.install(d.clone()).map_err(|e| e.to_string())?;
    let acts: Vec<_> = setup.genesis.iter().map(|s| s.act.clone()).collect();
    let instance = Instance::new(&d, ThreadId(THREAD.into()), &acts)?;
    Context::from_instance(&instance, "tickets", None, auth)
}
pub fn limits(setup: &Setup) -> Limits {
    Limits {
        operations: setup.transactions,
        events: setup.transactions as u64 * 8 + 16,
        ..Limits::default()
    }
}
pub fn transaction(
    setup: &Setup,
    ctx: &Context,
    sequence: usize,
    key: &SigningKey,
) -> Result<SignedAct> {
    let root = ctx.root_epoch("@alice")?;
    let source = format!("(lang collective-tickets (sell (@alice @bob @treasury) :buyer @customer :amount 1 :escrow-prev {root} :escrow-deps () :escrow-nonce \"bench-{sequence}\" :from @alice :thread \"{THREAD}\" :caused-by {}))", setup.genesis[1].act.address);
    Ok(sign_act(parse_act(&source, "@alice")?, key))
}
/// Client-side QC verification; no local validator state or fictitious client vote.
fn vote_domain_matches(ctx: &Context, vote: &Vote, kind: VoteKind, payload: &str) -> bool {
    vote.context == ctx.id()
        && vote.kind == kind
        && vote.payload == payload
        && ctx.committee().contains(&vote.signer)
}
pub fn verify_vote(
    auth: &Auth,
    ctx: &Context,
    vote: &Vote,
    kind: VoteKind,
    payload: &str,
) -> Result<()> {
    if !vote_domain_matches(ctx, vote, kind, payload)
        || !auth.verify(&vote.signer, &vote.preimage(), &vote.signature)
    {
        return Err("invalid quorum vote".into());
    }
    Ok(())
}
/// Process-local evidence of one strict signature check. Private fields and
/// immutable access prevent changes underneath that evidence. Never deserialized.
pub struct VerifiedVote {
    vote: Vote,
    verified_key: [u8; 32],
}
impl VerifiedVote {
    pub fn verify(
        auth: &Auth,
        ctx: &Context,
        vote: Vote,
        kind: VoteKind,
        payload: &str,
    ) -> Result<Self> {
        verify_vote(auth, ctx, &vote, kind, payload)?;
        let verified_key = auth
            .keys
            .get(&vote.signer)
            .ok_or("unknown verifying key")?
            .to_bytes();
        Ok(Self { vote, verified_key })
    }
    pub fn vote(&self) -> &Vote {
        &self.vote
    }
}
/// Construct and verify a local QC from strictly verified immutable votes.
/// Domain, quorum, distinct signers and current public-key bindings are checked
/// again, but the unchanged signatures do not need a second curve operation.
/// Certificates received from outside must use verify_certificate below.
pub fn certificate_from_verified(
    auth: &Auth,
    ctx: &Context,
    kind: VoteKind,
    payload: &str,
    votes: &BTreeMap<String, VerifiedVote>,
) -> Result<Certificate> {
    if votes.len() < ctx.committee().quorum || votes.len() > ctx.committee().validators.len() {
        return Err("invalid quorum certificate".into());
    }
    let mut signers = BTreeSet::new();
    for (key, verified) in votes {
        let vote = verified.vote();
        if key != &vote.signer
            || !signers.insert(&vote.signer)
            || !vote_domain_matches(ctx, vote, kind, payload)
            || auth.keys.get(&vote.signer).map(|k| k.to_bytes()) != Some(verified.verified_key)
        {
            return Err("verified vote context, signer or key mismatch".into());
        }
    }
    Ok(Certificate {
        kind,
        payload: payload.into(),
        votes: votes.values().map(|v| v.vote().clone()).collect(),
    })
}
pub fn verify_certificate(
    auth: &Auth,
    ctx: &Context,
    cert: &Certificate,
    kind: VoteKind,
    payload: &str,
) -> Result<()> {
    if cert.kind != kind
        || cert.payload != payload
        || cert.votes.len() < ctx.committee().quorum
        || cert.votes.len() > ctx.committee().validators.len()
    {
        return Err("invalid quorum certificate".into());
    }
    let mut signers = BTreeSet::new();
    for vote in &cert.votes {
        if !signers.insert(&vote.signer) {
            return Err("duplicate quorum signer".into());
        }
        verify_vote(auth, ctx, vote, kind, payload)?;
    }
    Ok(())
}
