use super::types::{digest, text};
use super::*;
use crate::{
    certification::{Certification, Committee},
    dialect::Dialect,
    escrow::{CounterRule, Outcome},
    intend::Instance,
    role::AgentKey,
    sexpr::{Atom, SExpr},
    state::{Act, Rule},
    store::ThreadId,
};
use alloc::{
    collections::{BTreeMap, BTreeSet},
    string::{String, ToString},
    vec::Vec,
};
#[derive(Debug, Clone)]
pub struct Context {
    pub(crate) id: String,
    pub(crate) field: String,
    pub(crate) dialect: Dialect,
    pub(crate) thread: ThreadId,
    pub(crate) genesis: Vec<Act>,
    pub(crate) opener: String,
    pub(crate) rule: CounterRule,
    pub(crate) committee: Committee,
    pub(crate) initial: BTreeMap<String, Resources>,
    pub(crate) issuers: BTreeSet<String>,
}
impl Context {
    pub fn from_instance<A: Authentication>(
        inst: &Instance,
        field: &str,
        validators: Option<&[String]>,
        auth: &A,
    ) -> Result<Self> {
        // Instance caches are public convenience fields, not authentication.
        let accepted = Instance::new(inst.dialect, inst.thread.clone(), inst.acts)?;
        let inst = &accepted;
        if !crate::r7::r7_violations(inst.dialect).is_empty() {
            return Err("invalid bounded-counter dialect".into());
        }
        let Some(Rule::BoundedCounter(rule)) =
            inst.dialect.state.as_ref().and_then(|s| s.rule_of(field))
        else {
            return Err("unknown bounded-counter field".into());
        };
        let committee = rule.certification.resolve(validators)?;
        let opener = inst.opener.ok_or("missing opener")?;
        let root = inst.root.ok_or("missing root")?;
        if inst
            .acts
            .iter()
            .any(|a| a.verb == rule.initial_verb && a.address != opener.address)
        {
            return Err("multiple resource openers in accepted history".into());
        }

        // Only genesis is imported. Accepted-but-uncertified history is never a
        // budget or finality authority for this engine.
        let genesis = alloc::vec![root.clone(), opener.clone()];
        for act in &genesis {
            if Act::from_message(act.message.clone(), &act.signer)? != *act
                || !auth.authenticate_act(act)
            {
                return Err("unauthenticated genesis".into());
            }
        }
        let mut genesis_rule = (**rule).clone();
        genesis_rule.certification = Certification::HostGate;
        let snapshot = match crate::escrow::observe_in(
            inst.dialect,
            &inst.thread.0,
            &genesis_rule,
            &genesis,
        ) {
            Outcome::Ready(s) => s,
            other => return Err(other.value().render()),
        };
        let bound = Instance::new(inst.dialect, inst.thread.clone(), &genesis)?;
        let cast = bound.cast.as_ref().ok_or("missing cast")?;
        let initial: BTreeMap<_, _> = snapshot
            .rights
            .iter()
            .map(|(k, n)| {
                (
                    k.clone(),
                    Resources {
                        rights: *n,
                        headroom: snapshot
                            .headroom
                            .as_ref()
                            .and_then(|h| h.get(k))
                            .copied()
                            .unwrap_or(0),
                    },
                )
            })
            .collect();
        let issuers = initial
            .keys()
            .filter(|k| cast.admits(&rule.issuer, &AgentKey((*k).clone())))
            .cloned()
            .collect();
        let id = digest(alloc::vec![
            text("cbcl/quorum-context/v1"),
            text(&crate::canonical::dialect_hash(inst.dialect)),
            text(&inst.thread.0),
            text(&root.address),
            text(&opener.address),
            text(field),
            SExpr::List(committee.validators.iter().map(|k| text(k)).collect()),
            text(&committee.faults.to_string())
        ]);
        Ok(Self {
            id,
            field: field.into(),
            dialect: inst.dialect.clone(),
            thread: inst.thread.clone(),
            genesis,
            opener: opener.address.clone(),
            rule: (**rule).clone(),
            committee,
            initial,
            issuers,
        })
    }
    pub fn id(&self) -> &str {
        &self.id
    }
    pub fn committee(&self) -> &Committee {
        &self.committee
    }
    pub fn root_epoch(&self, account: &str) -> Result<String> {
        if !self.initial.contains_key(account) {
            return Err("unknown account".into());
        }
        Ok(digest(alloc::vec![
            text("cbcl/root-epoch/v1"),
            text(&self.id),
            text(account)
        ]))
    }
    pub(crate) fn request(&self, kind: VoteKind, payload: &str, signer: &str) -> SigningRequest {
        SigningRequest {
            vote: Vote {
                context: self.id.clone(),
                kind,
                payload: payload.into(),
                signer: signer.into(),
                signature: Vec::new(),
            },
        }
    }
    pub fn cancellation_request(&self, owner: &str, operation: &str) -> Result<SigningRequest> {
        if !self.initial.contains_key(owner) {
            return Err("unknown owner".into());
        }
        Ok(self.request(VoteKind::CancelRequest, operation, owner))
    }
    pub fn checkpoint_request(&self, manifest: &Manifest) -> Result<SigningRequest> {
        if !self.initial.contains_key(&manifest.account) {
            return Err("unknown owner".into());
        }
        Ok(self.request(
            VoteKind::CheckpointRequest,
            &manifest.id(&self.id),
            &manifest.account,
        ))
    }
    pub(crate) fn matches(&self, inst: &Instance) -> bool {
        self.thread == inst.thread
            && inst.instance_id() == Some(self.opener.as_str())
            && crate::canonical::dialect_hash(inst.dialect)
                == crate::canonical::dialect_hash(&self.dialect)
    }
    pub(crate) fn structural(&self, act: &Act) -> Result<()> {
        if Act::from_message(act.message.clone(), &act.signer)? != *act {
            return Err("inconsistent act identity".into());
        }
        if !self.initial.contains_key(&act.signer) {
            return Err("owner outside pinned accounts".into());
        }
        fn language(m: &crate::message::Message) -> Option<&str> {
            match m {
                crate::message::Message::Dialect { dialect_name, .. } => Some(dialect_name),
                crate::message::Message::Wrapped { content, .. } => language(content),
                _ => None,
            }
        }
        if act.simple().thread() != Some(self.thread.0.as_str())
            || language(&act.message) != Some(self.dialect.name.as_str())
        {
            return Err("act context mismatch".into());
        }
        // Recognize the entire parameter list before interpreting any fields.
        let crate::message::Message::Simple { params, .. } = act.simple() else {
            return Err("not simple".into());
        };
        let mut seen = BTreeSet::new();
        for pair in params.chunks(2) {
            let [SExpr::Atom(Atom::Keyword(key)), _] = pair else {
                return Err("malformed resource parameters".into());
            };
            if !seen.insert(key) {
                return Err("duplicate resource keyword".into());
            }
        }
        // Closed shapes and compiler evidence; owner role is independent.
        crate::r7::verify_state_shape(&self.dialect, &act.message)
            .map_err(|e| alloc::format!("{e}"))?;
        for shape in self
            .dialect
            .shapes
            .iter()
            .filter(|s| s.performative == act.verb)
        {
            shape
                .check(&SExpr::from(act.simple()))
                .map_err(|e| alloc::format!("{e}"))?;
        }
        let inst = Instance::new(&self.dialect, self.thread.clone(), &self.genesis)?;
        if let Some(role) = self
            .dialect
            .find_performative(&act.verb)
            .and_then(|p| p.role.as_ref())
        {
            if !inst
                .cast
                .as_ref()
                .is_some_and(|cast| cast.admits(&role.from, &AgentKey(act.signer.clone())))
            {
                return Err("owner role not admitted".into());
            }
        }
        if act.fields.contains_key("from") {
            return Err("routing field in data".into());
        }
        let crate::message::Message::Simple { params, .. } = act.simple() else {
            return Err("not simple".into());
        };
        let from = params.windows(2).find_map(|p| match (&p[0], &p[1]) {
            (SExpr::Atom(Atom::Keyword(k)), SExpr::Atom(Atom::Symbol(v))) if k == "from" => Some(v),
            _ => None,
        });
        if from != Some(&act.signer) {
            return Err("from does not match authenticated owner".into());
        }
        Ok(())
    }
}
