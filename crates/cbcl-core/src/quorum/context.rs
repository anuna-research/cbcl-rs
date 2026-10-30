use super::types::{digest, text};
use super::*;
use crate::{
    certification::{Certification, Committee},
    dialect::Dialect,
    escrow::{CounterRule, Outcome, Ownership},
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
    pub(crate) handoff: Handoff,
    pub(crate) field: String,
    pub(crate) dialect: Dialect,
    pub(crate) thread: ThreadId,
    pub(crate) genesis: Vec<Act>,
    pub(crate) opener: String,
    pub(crate) rule: CounterRule,
    pub(crate) committee: Committee,
    pub(crate) initial: BTreeMap<String, Resources>,
    pub(crate) issuers: BTreeSet<String>,
    pub(crate) actors: BTreeSet<String>,
}
impl Context {
    pub fn from_instance<A: Authentication>(
        inst: &Instance,
        field: &str,
        validators: Option<&[String]>,
        auth: &A,
    ) -> Result<Self> {
        Self::with_handoff(inst, field, validators, auth, Handoff::SingleParent)
    }
    /// Isolated collective DAG protocol corresponding to SPEC-029. No legacy
    /// checkpoint signature or journal is valid in this context.
    pub fn from_instance_multi_parent<A: Authentication>(
        inst: &Instance,
        field: &str,
        validators: Option<&[String]>,
        auth: &A,
    ) -> Result<Self> {
        Self::with_handoff(inst, field, validators, auth, Handoff::MultiParent)
    }
    fn with_handoff<A: Authentication>(
        inst: &Instance,
        field: &str,
        validators: Option<&[String]>,
        auth: &A,
        handoff: Handoff,
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
        if handoff == Handoff::MultiParent && rule.ownership != Ownership::Collective {
            return Err("multi-parent protocol requires collective ownership".into());
        }
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
        let bound = Instance::new(inst.dialect, inst.thread.clone(), &genesis)?;
        let cast = bound.cast.as_ref().ok_or("missing cast")?;
        let cast_keys: BTreeSet<String> = cast
            .singleton
            .values()
            .chain(cast.indexed.values().flatten())
            .map(|k| k.0.clone())
            .collect();
        let (initial, actors) = if rule.ownership == Ownership::Collective {
            if cast_keys.contains(COLLECTIVE_POOL) {
                return Err(
                    "collective resource scope is reserved and cannot be a cast key".into(),
                );
            }
            if root.verb != "hello"
                || root.simple().thread() != Some(inst.thread.0.as_str())
                || !root.predecessors.is_empty()
                || opener.predecessors != alloc::vec![root.address.clone()]
            {
                return Err("collective genesis root context mismatch".into());
            }
            let amount = match opener.fields.get(&rule.initial_key) {
                Some(SExpr::Atom(Atom::Num(n))) if *n >= 0 => i128::from(*n),
                _ => return Err("collective initial rights must be a nonnegative integer".into()),
            };
            let headroom = match rule.ceiling {
                Some(cap) => i128::from(cap) - i128::from(rule.floor) - amount,
                None => 0,
            };
            if headroom < 0 {
                return Err("collective genesis exceeds ceiling".into());
            }
            (
                [(
                    COLLECTIVE_POOL.into(),
                    Resources {
                        rights: amount,
                        headroom,
                    },
                )]
                .into_iter()
                .collect(),
                cast_keys,
            )
        } else {
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
            let actors = initial.keys().cloned().collect();
            (initial, actors)
        };
        let issuers = actors
            .iter()
            .filter(|k| cast.admits(&rule.issuer, &AgentKey((*k).clone())))
            .cloned()
            .collect();
        let id = digest(alloc::vec![
            text(match handoff {
                Handoff::SingleParent => "cbcl/quorum-context/v1",
                Handoff::MultiParent => "cbcl/quorum-context/multi-parent/v1",
            }),
            text(&crate::canonical::dialect_hash(inst.dialect)),
            text(&inst.thread.0),
            text(&root.address),
            text(&opener.address),
            text(field),
            SExpr::List(committee.validators.iter().map(|k| text(k)).collect()),
            text(&committee.faults.to_string())
        ]);
        let context = Self {
            id,
            handoff,
            field: field.into(),
            dialect: inst.dialect.clone(),
            thread: inst.thread.clone(),
            genesis,
            opener: opener.address.clone(),
            rule: (**rule).clone(),
            committee,
            initial,
            issuers,
            actors,
        };
        if context.rule.ownership == Ownership::Collective {
            context.structural(opener)?;
        }
        Ok(context)
    }
    pub fn id(&self) -> &str {
        &self.id
    }
    pub fn handoff(&self) -> Handoff {
        self.handoff
    }
    pub fn committee(&self) -> &Committee {
        &self.committee
    }
    pub fn ownership(&self) -> Ownership {
        self.rule.ownership
    }
    pub fn pool(&self) -> Option<&str> {
        (self.rule.ownership == Ownership::Collective).then_some(COLLECTIVE_POOL)
    }
    pub(crate) fn account<'a>(&self, actor: &'a str) -> Result<&'a str> {
        if self.rule.ownership == Ownership::Collective
            && (self.actors.contains(actor) || actor == COLLECTIVE_POOL)
        {
            return Ok(COLLECTIVE_POOL);
        }
        if self.initial.contains_key(actor) {
            return Ok(actor);
        }
        Err("unknown actor or resource account".into())
    }
    pub(crate) fn checkpoint_actor(&self, account: &str, actor: &str) -> bool {
        if self.rule.ownership == Ownership::Account {
            return account == actor && self.initial.contains_key(actor);
        }
        if account != COLLECTIVE_POOL || !self.actors.contains(actor) {
            return false;
        }
        let Ok(inst) = Instance::new(&self.dialect, self.thread.clone(), &self.genesis) else {
            return false;
        };
        inst.cast.as_ref().is_some_and(|cast| {
            self.rule.operation_verbs().iter().any(|v| {
                self.dialect
                    .find_performative(v)
                    .and_then(|p| p.role.as_ref())
                    .is_some_and(|r| cast.admits(&r.from, &AgentKey(actor.into())))
            })
        })
    }
    pub fn root_epoch(&self, account: &str) -> Result<String> {
        let account = self.account(account)?;
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
        if !self.actors.contains(owner) {
            return Err("unknown owner".into());
        }
        Ok(self.request(VoteKind::CancelRequest, operation, owner))
    }
    pub fn checkpoint_request(&self, manifest: &Manifest) -> Result<SigningRequest> {
        self.checkpoint_request_by(manifest, &manifest.account)
    }
    /// Collective manifests name a resource scope, so an actual actor must sign.
    pub fn checkpoint_request_by(
        &self,
        manifest: &Manifest,
        actor: &str,
    ) -> Result<SigningRequest> {
        if self.handoff != Handoff::SingleParent {
            return Err("legacy checkpoint request in multi-parent context".into());
        }
        if !self.checkpoint_actor(&manifest.account, actor) {
            return Err("checkpoint actor is not authorized for resource account".into());
        }
        Ok(self.request(VoteKind::CheckpointRequest, &manifest.id(&self.id), actor))
    }
    /// External actor signing request; receiving replicas validate every field.
    pub fn version_request(
        &self,
        manifest: &VersionManifest,
        actor: &str,
    ) -> Result<SigningRequest> {
        if self.handoff != Handoff::MultiParent || !self.checkpoint_actor(&manifest.account, actor)
        {
            return Err("unauthorized DAG version actor or context mode".into());
        }
        Ok(self.request(VoteKind::VersionRequest, &manifest.id(&self.id), actor))
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
        if !self.actors.contains(&act.signer) {
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
