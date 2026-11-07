//! The intent binder (SPEC-019 R.5): `intend` completes a caller's verb and
//! data fields into a canonical act, or rejects. Pure: it never signs,
//! sends, stores, or reads a clock. Every host must bind identically, which
//! is why it lives beside the fold.

#![forbid(unsafe_code)]

use crate::dialect::Dialect;
use crate::message::{CausedBy, Message, Performative, Recipients, WrapperType};
use crate::projection::verify_causal_for_role;
use crate::protocol::{verify_causal, NodeRef, VerificationResult, BEGIN_KEYWORD};
use crate::r7::{bounds_of, declared_keywords, verify_state_shape};
use crate::role::{parse_wrapper_cast, AgentKey, Cast, Endpoint};
use crate::sexpr::{Atom, SExpr};
use crate::shape::ShapeViolation;
use crate::state::{
    opener, root, wire_address, Act, Rule, StateClause, Value, RESERVED_REPLACES, ROUTING_KEYWORDS,
};
use crate::store::{ContentHash, MessageStore, ThreadId, ThreadedMessageStore};
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

/// The instance context (SPEC-019 CON-1903): everything a state function
/// may read. The cast is parsed from the accepted root wrapper, never
/// supplied by a caller.
#[derive(Debug, Clone)]
pub struct Instance<'a> {
    pub dialect: &'a Dialect,
    pub thread: ThreadId,
    pub acts: &'a [Act],
    /// The act of the opener verb.
    pub opener: Option<&'a Act>,
    /// Under R6, the cast-bearing root (SPEC-014 REQ-611/623), which the
    /// opener follows; `None` for a role-free dialect.
    pub root: Option<&'a Act>,
    pub cast: Option<Cast>,
}

impl<'a> Instance<'a> {
    /// Build the context from accepted acts. For a role-declaring dialect
    /// the cast is read from the `with-roles` root among the acts.
    pub fn new(
        dialect: &'a Dialect,
        thread: ThreadId,
        acts: &'a [Act],
    ) -> Result<Instance<'a>, String> {
        let op = dialect
            .causal_protocol
            .as_ref()
            .and_then(|p| opener(p, acts));
        let (rt, cast) = if dialect.roles.is_empty() {
            (None, None)
        } else {
            match root(acts) {
                Some(r) => (Some(r), Some(cast_of(&r.message, dialect)?)),
                None => (None, None),
            }
        };
        Ok(Instance {
            dialect,
            thread,
            acts,
            opener: op,
            root: rt,
            cast,
        })
    }

    /// The accepted acts as a store keyed by content address.
    pub fn store(&self) -> ThreadedMessageStore {
        let mut store = ThreadedMessageStore::new();
        for a in self.acts {
            store.append(
                ContentHash(a.address.clone()),
                self.thread.clone(),
                a.message.clone(),
            );
        }
        store
    }

    /// The address of the accepted opener.
    pub fn instance_id(&self) -> Option<&str> {
        self.opener.map(|a| a.address.as_str())
    }
}

/// Read the cast from a root message's `with-roles` wrapper.
pub fn cast_of(root: &Message, dialect: &Dialect) -> Result<Cast, String> {
    let mut cur = root;
    loop {
        match cur {
            Message::Wrapped {
                wrapper: WrapperType::WithRoles,
                params,
                ..
            } => {
                return parse_wrapper_cast(params, &dialect.roles).map_err(|e| format!("{e}"));
            }
            Message::Wrapped { content, .. } => cur = content,
            Message::Dialect { inner, .. } => cur = inner,
            _ => {
                return Err(String::from(
                    "the root of a role-declaring dialect must carry a with-roles wrapper",
                ))
            }
        }
    }
}

/// The roles a signer occupies under a cast, sorted.
pub fn roles_of(cast: &Cast, signer: &AgentKey) -> Vec<String> {
    let mut out: Vec<String> = cast
        .singleton
        .iter()
        .filter(|(_, k)| *k == signer)
        .map(|(r, _)| r.clone())
        .chain(
            cast.indexed
                .iter()
                .filter(|(_, ks)| ks.contains(signer))
                .map(|(r, _)| r.clone()),
        )
        .collect();
    out.sort();
    out.dedup();
    out
}

/// Why an intent was rejected (SPEC-019 R.5).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Reject {
    UnknownVerb,
    Opener,
    Forge(String),
    Role(String),
    Domain(String),
    NothingToDelete,
    NoPredecessor,
    Shape(ShapeViolation),
    NotValid(VerificationResult),
    /// The instance has no accepted opener, so no recipient set is known.
    NoOpener,
    Resource(String),
}

impl fmt::Display for Reject {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Reject::Resource(reason) => write!(f, "resource authorization: {reason}"),
            Reject::UnknownVerb => write!(f, "unknown verb"),
            Reject::Opener => write!(f, "the opener cannot be emitted on an existing instance"),
            Reject::Forge(field) => {
                write!(f, "the caller supplied :{field}, which the binder owns")
            }
            Reject::Role(required) => write!(f, "the signer occupies no role '{required}'"),
            Reject::Domain(field) => write!(f, ":{field} is not among the opener's options"),
            Reject::NothingToDelete => write!(f, "nothing to delete"),
            Reject::NoPredecessor => write!(f, "no admissible predecessor"),
            Reject::Shape(v) => write!(f, "{v}"),
            Reject::NotValid(v) => write!(f, "constructed act is not Valid: {v:?}"),
            Reject::NoOpener => write!(f, "the instance has no accepted opener"),
        }
    }
}

/// The JSON rendering of a rejection, for exports.
pub fn render_reject(r: &Reject) -> String {
    let kind = match r {
        Reject::Resource(_) => "resource",
        Reject::UnknownVerb => "unknown-verb",
        Reject::Opener => "opener",
        Reject::Forge(_) => "forge",
        Reject::Role(_) => "role",
        Reject::Domain(_) => "domain",
        Reject::NothingToDelete => "nothing-to-delete",
        Reject::NoPredecessor => "no-predecessor",
        Reject::Shape(_) => "shape",
        Reject::NotValid(_) => "not-valid",
        Reject::NoOpener => "no-opener",
    };
    let detail = format!("{r}");
    let mut out = String::from("{\"reject\":");
    out.push_str(&Value::Str(String::from(kind)).render());
    out.push_str(",\"reason\":");
    out.push_str(&Value::Str(detail).render());
    out.push('}');
    out
}

/// The predecessor performatives a verb's step admits (each alternative).
fn allowed_predecessors(d: &Dialect, verb: &str) -> Vec<NodeRef> {
    d.causal_protocol
        .as_ref()
        .and_then(|p| p.steps.get(verb))
        .map(|s| s.predecessors.clone())
        .unwrap_or_default()
}

/// The keys the cast expects as recipients for a `:to` role set.
fn recipient_keys(to: &BTreeSet<String>, cast: &Cast) -> BTreeSet<String> {
    let mut keys = BTreeSet::new();
    for role in to {
        if let Some(k) = cast.singleton.get(role) {
            keys.insert(k.0.clone());
        }
        if let Some(ks) = cast.indexed.get(role) {
            keys.extend(ks.iter().map(|k| k.0.clone()));
        }
    }
    keys
}

/// Step 1 of R.5 without an intent: the verbs a signer may emit here.
pub fn may_send(inst: &Instance, signer: &AgentKey) -> Vec<String> {
    let Some(protocol) = inst.dialect.causal_protocol.as_ref() else {
        return Vec::new();
    };
    let opener_name = crate::state::opener_verb(protocol).map(String::from);
    let mut out = Vec::new();
    for p in &inst.dialect.performatives {
        if Some(&p.name) == opener_name.as_ref()
            && !protocol.steps.keys().any(|n| {
                n.contains(crate::protocol::REPEAT_SEPARATOR)
                    && crate::protocol::repeat_base_name(n) == p.name
            })
        {
            continue;
        }
        if role_gate(inst, signer, &p.name).is_err() {
            continue;
        }
        out.push(p.name.clone());
    }
    out.sort();
    out
}

fn role_gate(inst: &Instance, signer: &AgentKey, verb: &str) -> Result<(), Reject> {
    let Some(cast) = inst.cast.as_ref() else {
        return Ok(());
    };
    let Some(ann) = inst
        .dialect
        .find_performative(verb)
        .and_then(|p| p.role.as_ref())
    else {
        return Ok(());
    };
    if cast.admits(&ann.from, signer) {
        Ok(())
    } else {
        Err(Reject::Role(ann.from.clone()))
    }
}

/// Choose the predecessor for one required type set (step 5): the signer's
/// own tip among candidates, else the greatest address.
fn choose_predecessor(inst: &Instance, signer: &str, allowed: &BTreeSet<&str>) -> Option<String> {
    choose_typed_predecessor(inst, signer, allowed, None)
}
fn choose_typed_predecessor(
    inst: &Instance,
    signer: &str,
    allowed: &BTreeSet<&str>,
    resolution: Option<&crate::repeat::Resolution<'_, ThreadedMessageStore>>,
) -> Option<String> {
    let candidates: Vec<&Act> = inst
        .acts
        .iter()
        .filter(|a| match resolution {
            Some(r) => allowed
                .iter()
                .any(|name| matches!(r.at(&a.address, name), VerificationResult::Valid)),
            None => allowed.contains(a.verb.as_str()),
        })
        .collect();
    if candidates.is_empty() {
        return None;
    }
    let own: Vec<&Act> = candidates
        .iter()
        .copied()
        .filter(|a| a.signer == signer)
        .collect();
    if !own.is_empty() {
        let named: BTreeSet<&str> = own
            .iter()
            .flat_map(|a| a.predecessors.iter().map(|p| p.as_str()))
            .collect();
        let tips: Vec<&Act> = own
            .iter()
            .copied()
            .filter(|a| !named.contains(a.address.as_str()))
            .collect();
        let pool = if tips.is_empty() { own } else { tips };
        return pool
            .iter()
            .max_by(|a, b| a.address.as_bytes().cmp(b.address.as_bytes()))
            .map(|a| a.address.clone());
    }
    candidates
        .iter()
        .max_by(|a, b| a.address.as_bytes().cmp(b.address.as_bytes()))
        .map(|a| a.address.clone())
}

// Resolve expanded predecessor types from accepted causal evidence. For a
// repeated verb, skip already occupied copies and prefer the furthest ready
// position. This authoring policy does not reject concurrent peer branches.
fn repeat_cause(inst: &Instance, signer: &str, verb: &str) -> Result<CausedBy, Reject> {
    let protocol = inst
        .dialect
        .causal_protocol
        .as_ref()
        .ok_or(Reject::NoPredecessor)?;
    let store = inst.store();
    let root = inst.root.map(|a| ContentHash(a.address.clone()));
    let resolution = crate::repeat::Resolution::new(
        &store,
        protocol,
        &inst.thread,
        root.as_ref(),
        inst.acts.iter().map(|a| a.address.clone()),
    );
    for name in resolution.order.iter().rev() {
        if crate::protocol::repeat_base_name(name) != verb {
            continue;
        }
        if protocol.steps.keys().any(|n| {
            n.contains(crate::protocol::REPEAT_SEPARATOR)
                && crate::protocol::repeat_base_name(n) == verb
        }) && inst
            .acts
            .iter()
            .any(|a| matches!(resolution.at(&a.address, name), VerificationResult::Valid))
        {
            continue;
        }
        for node in &protocol.steps[*name].predecessors {
            let names: BTreeSet<&str> = node.performatives().collect();
            if names.contains(BEGIN_KEYWORD) {
                continue;
            }
            if matches!(node, NodeRef::All(_)) {
                let chosen: Option<Vec<String>> = names
                    .iter()
                    .map(|n| {
                        let occupants = inst
                            .dialect
                            .find_performative(crate::protocol::repeat_base_name(n))
                            .and_then(|p| p.role.as_ref())
                            .and_then(|ann| inst.cast.as_ref()?.indexed.get(&ann.from));
                        if let Some(occupants) = occupants {
                            occupants
                                .iter()
                                .map(|who| {
                                    inst.acts
                                        .iter()
                                        .filter(|a| {
                                            a.signer == who.0
                                                && matches!(
                                                    resolution.at(&a.address, n),
                                                    VerificationResult::Valid
                                                )
                                        })
                                        .max_by(|a, b| a.address.cmp(&b.address))
                                        .map(|a| a.address.clone())
                                })
                                .collect::<Option<Vec<_>>>()
                        } else {
                            choose_typed_predecessor(
                                inst,
                                signer,
                                &[*n].into_iter().collect(),
                                Some(&resolution),
                            )
                            .map(|h| alloc::vec![h])
                        }
                    })
                    .collect::<Option<Vec<_>>>()
                    .map(|groups| groups.into_iter().flatten().collect());
                if let Some(mut hs) = chosen.filter(|hs| !hs.is_empty()) {
                    hs.sort();
                    hs.dedup();
                    return Ok(CausedBy::Multiple(hs));
                }
            } else if let Some(hash) =
                choose_typed_predecessor(inst, signer, &names, Some(&resolution))
            {
                return Ok(CausedBy::Single(hash));
            }
        }
    }
    Err(Reject::NoPredecessor)
}

/// Complete a verb and its data fields into a canonical act for the host to sign.
pub fn intend(
    inst: &Instance,
    signer: &AgentKey,
    verb: &str,
    fields: BTreeMap<String, SExpr>,
) -> Result<Message, Reject> {
    intend_impl(inst, signer, verb, fields, None)
}

pub(crate) fn intend_certified(
    inst: &Instance,
    signer: &AgentKey,
    verb: &str,
    fields: BTreeMap<String, SExpr>,
    runtime: &crate::quorum::Replica,
    nonce: &str,
) -> Result<Message, Reject> {
    intend_impl(inst, signer, verb, fields, Some((runtime, nonce)))
}

fn intend_impl(
    inst: &Instance,
    signer: &AgentKey,
    verb: &str,
    fields: BTreeMap<String, SExpr>,
    runtime: Option<(&crate::quorum::Replica, &str)>,
) -> Result<Message, Reject> {
    let d = inst.dialect;
    let clause: &StateClause = match d.state.as_ref() {
        Some(c) => c,
        None => return Err(Reject::UnknownVerb),
    };
    let Some(protocol) = d.causal_protocol.as_ref() else {
        return Err(Reject::UnknownVerb);
    };

    // 1 admit
    if d.find_performative(verb).is_none() {
        return Err(Reject::UnknownVerb);
    }
    if crate::state::opener_verb(protocol) == Some(verb)
        && !protocol.steps.keys().any(|n| {
            n.contains(crate::protocol::REPEAT_SEPARATOR)
                && crate::protocol::repeat_base_name(n) == verb
        })
    {
        return Err(Reject::Opener);
    }
    for k in fields.keys() {
        if ROUTING_KEYWORDS.contains(&k.as_str())
            || k == RESERVED_REPLACES
            || k == crate::escrow::PREV
            || k == crate::escrow::DEPS
            || k == crate::escrow::NONCE
        {
            return Err(Reject::Forge(k.clone()));
        }
    }
    role_gate(inst, signer, verb)?;

    // 2 domain
    let state = crate::state::fold(clause, Some(protocol), inst.acts);
    for (dv, key, field) in clause.domains() {
        if dv != verb {
            continue;
        }
        let allowed = match state.iter().find(|(n, _)| n == field) {
            Some((_, Value::List(items))) | Some((_, Value::Set(items))) => items.clone(),
            _ => Vec::new(),
        };
        let supplied = fields.get(key).map(Value::from_sexpr);
        let ok = supplied.as_ref().is_some_and(|v| {
            let r = v.render();
            allowed.iter().any(|x| x.render() == r)
        });
        if !ok {
            return Err(Reject::Domain(String::from(key)));
        }
    }

    // 3 to
    let recipients: BTreeSet<String> = match (
        &inst.cast,
        d.find_performative(verb).and_then(|p| p.role.as_ref()),
    ) {
        (Some(cast), Some(ann)) => recipient_keys(&ann.to, cast),
        _ => match inst.opener {
            Some(op) => op.recipients.clone(),
            None => return Err(Reject::NoOpener),
        },
    };

    // 4 replaces
    let bounds = bounds_of(d);
    let mut replaces: Option<Vec<String>> = None;
    for (_, rule) in clause.fields() {
        if let Rule::LwwPerSigner { verb: writer, .. } = rule {
            if writer == verb {
                let mut addrs: Vec<String> =
                    crate::state::current_by_signer(clause, inst.acts, writer)
                        .into_iter()
                        .filter(|a| a.signer == signer.0)
                        .map(|a| a.address.clone())
                        .collect();
                addrs.sort();
                addrs.dedup();
                let existing = replaces.get_or_insert_with(Vec::new);
                existing.extend(addrs);
                existing.sort();
                existing.dedup();
                existing.truncate(bounds.max_list as usize);
            }
            continue;
        }
        let binding = match rule {
            Rule::Values { verb: w, .. } if w == verb => Some((w.as_str(), None, None, false)),
            Rule::ValuesPerKey {
                verb: w,
                key,
                delete,
                ..
            }
            | Rule::LwwMap {
                verb: w,
                key,
                delete,
                ..
            } => {
                if w == verb {
                    Some((w.as_str(), Some(key.as_str()), delete.as_deref(), false))
                } else if delete.as_deref() == Some(verb) {
                    Some((w.as_str(), Some(key.as_str()), delete.as_deref(), true))
                } else {
                    None
                }
            }
            Rule::ObservedSet { add, remove, key } if remove == verb => Some((
                add.as_str(),
                Some(key.as_str()),
                Some(remove.as_str()),
                true,
            )),
            _ => None,
        };
        let Some((writer, key, delete, is_delete)) = binding else {
            continue;
        };
        let mine = |a: &Act| -> bool {
            match key {
                None => true,
                Some(k) => match (a.fields.get(k), fields.get(k)) {
                    (Some(x), Some(y)) => {
                        Value::from_sexpr(x).render() == Value::from_sexpr(y).render()
                    }
                    _ => false,
                },
            }
        };
        let current = crate::state::current_writes(clause, inst.acts, writer, key, delete);
        let mut addrs: Vec<String> = current
            .iter()
            .filter(|a| mine(a))
            .map(|a| a.address.clone())
            .collect();
        if is_delete && addrs.is_empty() {
            return Err(Reject::NothingToDelete);
        }
        if !is_delete {
            if let Some(dv) = delete {
                // Current deletions for the key: deletions no later write names.
                let deletions =
                    crate::state::current_writes(clause, inst.acts, dv, key, Some(writer));
                addrs.extend(
                    deletions
                        .iter()
                        .filter(|a| mine(a))
                        .map(|a| a.address.clone()),
                );
            }
        }
        addrs.sort();
        addrs.dedup();
        addrs.truncate(bounds.max_list as usize);
        match replaces.as_mut() {
            None => replaces = Some(addrs),
            Some(existing) => {
                existing.extend(addrs);
                existing.sort();
                existing.dedup();
                existing.truncate(bounds.max_list as usize);
            }
        }
    }

    // 5 caused-by
    let steps = allowed_predecessors(d, verb);
    let caused_by = if crate::repeat::has_repeat(protocol) {
        repeat_cause(inst, &signer.0, verb)?
    } else if steps.is_empty() {
        return Err(Reject::NoPredecessor);
    } else {
        let mut chosen: Vec<String> = Vec::new();
        let mut fan_in = false;
        for node in &steps {
            match node {
                NodeRef::Single(s) => {
                    let allowed: BTreeSet<&str> = [s.as_str()].into_iter().collect();
                    if let Some(p) = choose_predecessor(inst, &signer.0, &allowed) {
                        chosen = alloc::vec![p];
                        break;
                    }
                    if s == BEGIN_KEYWORD {
                        return Err(Reject::Opener);
                    }
                }
                NodeRef::Any(set) => {
                    let allowed: BTreeSet<&str> = set.iter().map(|s| s.as_str()).collect();
                    if let Some(p) = choose_predecessor(inst, &signer.0, &allowed) {
                        chosen = alloc::vec![p];
                        break;
                    }
                }
                NodeRef::All(set) => {
                    fan_in = true;
                    let mut all = Vec::new();
                    for s in set {
                        let allowed: BTreeSet<&str> = [s.as_str()].into_iter().collect();
                        match choose_predecessor(inst, &signer.0, &allowed) {
                            Some(p) => all.push(p),
                            None => {
                                all.clear();
                                break;
                            }
                        }
                    }
                    if !all.is_empty() {
                        chosen = all;
                        break;
                    }
                }
            }
        }
        if chosen.is_empty() {
            return Err(Reject::NoPredecessor);
        }
        if fan_in && chosen.len() > 1 {
            chosen.sort();
            CausedBy::Multiple(chosen)
        } else {
            CausedBy::Single(chosen.remove(0))
        }
    };

    // 6 build
    let mut params: Vec<SExpr> = Vec::new();
    let declared = declared_keywords(&d.shapes, verb);
    for k in fields.keys() {
        if !declared.contains(k) {
            return Err(Reject::Shape(ShapeViolation {
                rule: String::from("closed"),
                field: Some(format!(":{k}")),
                expected: None,
                found: None,
                detail: format!("undeclared field :{k} on '{verb}'"),
            }));
        }
    }
    // Canonical order (SPEC-019 REQ-1949): business fields as the shape declares them.
    for k in crate::r7::declared_keyword_order(&d.shapes, verb) {
        if let Some(v) = fields.get(&k) {
            params.push(SExpr::Atom(Atom::Keyword(k)));
            params.push(v.clone());
        }
    }
    // Keep identity rejection at its original point after ordinary admission.
    // The binding holds the exact immutable inputs for both authoring stages.
    let authoring = runtime
        .map(|(engine, nonce)| engine.bind_authoring(inst).map(|bound| (bound, nonce)))
        .transpose()
        .map_err(Reject::Resource)?;
    let inst = authoring
        .as_ref()
        .map_or(inst, |(bound, _)| bound.instance());
    let bookkeeping = match &authoring {
        Some((engine, nonce)) => engine.bookkeeping(&signer.0, verb, nonce),
        None => crate::escrow::bookkeeping(d, inst.acts, &inst.thread.0, &signer.0, verb),
    }
    .map_err(Reject::Resource)?;
    for (key, value) in bookkeeping {
        params.push(SExpr::Atom(Atom::Keyword(key)));
        params.push(value);
    }
    if let Some(addrs) = replaces {
        params.push(SExpr::Atom(Atom::Keyword(String::from(RESERVED_REPLACES))));
        params.push(SExpr::List(
            addrs
                .into_iter()
                .map(|a| SExpr::Atom(Atom::Symbol(a)))
                .collect(),
        ));
    }
    params.push(SExpr::Atom(Atom::Keyword(String::from("from"))));
    params.push(SExpr::Atom(Atom::Symbol(signer.0.clone())));
    let recipient = match recipients.len() {
        0 => None,
        1 => Some(Recipients::One(recipients.into_iter().next().unwrap())),
        _ => Some(Recipients::Set(recipients)),
    };
    let inner = Message::Simple {
        performative: Performative::Custom(String::from(verb)),
        recipient,
        content: SExpr::List(Vec::new()),
        params,
        thread: Some(inst.thread.0.clone()),
        sender: None,
        caused_by: Some(caused_by),
    };
    let message = Message::Dialect {
        dialect_name: d.name.clone(),
        inner: alloc::boxed::Box::new(inner),
    };

    // 7 verify
    let simple = message.innermost_simple().expect("built a simple message");
    verify_state_shape(d, &message).map_err(Reject::Shape)?;
    for shape in d.shapes.iter().filter(|s| s.performative == verb) {
        shape.check(&SExpr::from(simple)).map_err(Reject::Shape)?;
    }
    let mut store = inst.store();
    let address = ContentHash(wire_address(simple));
    // The host signs the returned act; for verification the constructed
    // act is viewed under the signed wrapper it will carry, so that role
    // conformance can read the signer key (SPEC-014 REQ-612).
    let signed = Message::Wrapped {
        wrapper: WrapperType::Signed,
        params: alloc::vec![SExpr::Atom(Atom::Symbol(signer.0.clone()))],
        content: alloc::boxed::Box::new(message.clone()),
    };
    store.append(address.clone(), inst.thread.clone(), signed.clone());
    let verdict = match (&inst.cast, inst.root) {
        (Some(cast), Some(rt)) => {
            let endpoint = Endpoint {
                role: String::new(),
                occupant: Some(signer.clone()),
            };
            verify_causal_for_role(
                &signed,
                &endpoint,
                d,
                cast,
                &store,
                &inst.thread,
                &ContentHash(rt.address.clone()),
            )
        }
        _ => verify_causal(verb, simple.caused_by(), &store, protocol, &inst.thread),
    };
    match verdict {
        VerificationResult::Valid => {
            if let Some((_, c)) = crate::escrow::rule_for(d, verb) {
                let candidate =
                    Act::from_message(message.clone(), &signer.0).map_err(Reject::Resource)?;
                if c.certification.is_quorum() {
                    let (engine, _) = authoring.as_ref().ok_or_else(|| {
                        Reject::Resource("quorum-budget requires certificate runtime".into())
                    })?;
                    engine
                        .check_candidate(&candidate)
                        .map_err(Reject::Resource)?;
                    return Ok(message);
                }
                match crate::escrow::observe_in(d, &inst.thread.0, c, inst.acts) {
                    crate::escrow::Outcome::Ready(_) => {}
                    other => return Err(Reject::Resource(other.value().render())),
                }
                match crate::escrow::check(c, inst.acts, &candidate) {
                    crate::escrow::Outcome::Ready(_) => {}
                    other => return Err(Reject::Resource(other.value().render())),
                }
            }
            Ok(message)
        }
        other => Err(Reject::NotValid(other)),
    }
}

/// The canonical text of an act, as the host signs it.
pub fn canonical_text(message: &Message) -> String {
    crate::serializer::serialize(&SExpr::from(message))
}

/// The content address of an act built by `intend`, wire spelling.
pub fn address_of(message: &Message) -> Option<String> {
    message.innermost_simple().map(wire_address)
}

impl Reject {
    pub fn kind(&self) -> &'static str {
        match self {
            Reject::Resource(_) => "resource",
            Reject::UnknownVerb => "unknown-verb",
            Reject::Opener => "opener",
            Reject::Forge(_) => "forge",
            Reject::Role(_) => "role",
            Reject::Domain(_) => "domain",
            Reject::NothingToDelete => "nothing-to-delete",
            Reject::NoPredecessor => "no-predecessor",
            Reject::Shape(_) => "shape",
            Reject::NotValid(_) => "not-valid",
            Reject::NoOpener => "no-opener",
        }
    }
}
