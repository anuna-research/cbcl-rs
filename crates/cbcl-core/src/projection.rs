//! Endpoint projection and role-local verification (SPEC-014
//! REQ-609..620, 623, 626; CON-602).
//!
//! [`project`] derives a role's local protocol from a role-annotated
//! dialect as a pure function: every agent holding the same dialect (and,
//! for indexed roles, the same sealed cast) computes the same local
//! protocols — the choreographer is replicated at every endpoint.
//!
//! [`verify_causal_for_role`] is the runtime monitor: the lattice meet of a
//! role-conformance check with the *unchanged* R5 `verify_causal` run
//! against the dialect-level protocol (ADR-604), plus the one check the
//! role layer adds rather than reuses: the occupant-counted `(all …)`
//! fan-in (REQ-618). Projection keeps raw `:caused-by` edges (REQ-610):
//! under R6(vi) the bystander splice is vacuous, so no rewritten
//! predecessor view exists.
//!
//! Root typing (REQ-623, ADR-603): traces name the thread root *by hash*
//! (`:caused-by h₀`) while protocol clauses name `begin`; the composition
//! maps a reference that resolves to the thread's `with-roles` wrapper to
//! the `begin` predecessor type before delegating to R5.

#![forbid(unsafe_code)]

use crate::dialect::Dialect;
use crate::message::{CausedBy, Message, WrapperType};
use crate::protocol::{
    verify_causal, CausalProtocol, CausalViolation, NodeRef, VerificationResult,
};
use crate::role::{parse_cast, AgentKey, Cast, Endpoint, RoleAnnotation, RoleCardinality};
use crate::sexpr::{Atom, SExpr};
use crate::store::{ContentHash, MessageStore, ThreadId};
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

/// A step of a local protocol, from one endpoint's viewpoint (CON-602).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum LocalStep {
    /// The endpoint's role is the performative's sender.
    Send,
    /// The endpoint's role is among the performative's recipients.
    Recv,
}

/// A role's local protocol: its Send/Recv steps plus the dialect-level
/// causal protocol, predecessor clauses untouched (raw edges, REQ-610).
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct LocalProtocol {
    /// Performative name → step kind; bystander performatives are erased
    /// (absent).
    pub steps: BTreeMap<String, LocalStep>,
    /// The dialect-level protocol the R5 composition verifies against
    /// (ADR-604); shared verbatim across all endpoints.
    pub protocol: Option<CausalProtocol>,
}

/// Endpoint projection (REQ-609): a pure function of the dialect and the
/// endpoint. A performative whose `:from` is the endpoint's role becomes a
/// [`LocalStep::Send`]; one whose `:to` contains it becomes a
/// [`LocalStep::Recv`]; one in which the role is no endpoint is erased,
/// with no predecessor reference rewritten (the splice is vacuous under
/// R6(vi)).
///
/// `cast` is accepted for per-occupant instantiation (CON-602); in v1 the
/// step set is identical across an indexed role's occupants, so it is
/// unused beyond the signature contract.
pub fn project(d: &Dialect, endpoint: &Endpoint, cast: Option<&Cast>) -> LocalProtocol {
    let _ = cast;
    let mut steps: BTreeMap<String, LocalStep> = BTreeMap::new();
    for p in &d.performatives {
        if let Some(ann) = &p.role {
            if ann.from == endpoint.role {
                steps.insert(p.name.clone(), LocalStep::Send);
            } else if ann.to.contains(&endpoint.role) {
                steps.insert(p.name.clone(), LocalStep::Recv);
            }
        }
    }
    LocalProtocol {
        steps,
        protocol: d.causal_protocol.clone(),
    }
}

/// The key a message is *ratified* under: the key of an enclosing `signed`
/// wrapper (REQ-612, ratification-by-signature). Deliberately does **not**
/// fall back to the innermost `:sender` field — that field is a self-asserted,
/// unauthenticated claim, so trusting it would let an unsigned message occupy
/// a role (a forgery path). A message with no `signed` wrapper has no
/// ratifying key and cannot occupy a sender role.
fn signer_of(msg: &Message) -> Option<&str> {
    let mut cur = msg;
    loop {
        match cur {
            Message::Wrapped {
                wrapper: WrapperType::Signed,
                params,
                content,
            } => {
                if let Some(SExpr::Atom(Atom::Symbol(s))) = params.first() {
                    return Some(s.as_str());
                }
                cur = content;
            }
            Message::Wrapped { content, .. } => cur = content,
            Message::Dialect { inner, .. } => cur = inner,
            // No signed wrapper enclosed this payload: no ratifying key.
            Message::Simple { .. } | Message::Meta { .. } => return None,
        }
    }
}

fn role_violation(reason: String) -> VerificationResult {
    VerificationResult::Violation(CausalViolation::RoleConformance { reason })
}

/// The keys the cast expects as recipients for an annotation's `:to` set:
/// the singleton key per singleton role, every sealed occupant per indexed
/// role.
fn expected_recipient_keys<'a>(ann: &RoleAnnotation, cast: &'a Cast) -> BTreeSet<&'a str> {
    let mut keys: BTreeSet<&str> = BTreeSet::new();
    for role in &ann.to {
        if let Some(k) = cast.singleton.get(role) {
            keys.insert(k.0.as_str());
        }
        if let Some(ks) = cast.indexed.get(role) {
            keys.extend(ks.iter().map(|k| k.0.as_str()));
        }
    }
    keys
}

/// Role-local verification (REQ-612..620, 623, 626; CON-602): the lattice
/// meet of role conformance, the unchanged R5 predecessor check against
/// the dialect-level protocol, and the occupant-counted fan-in.
pub fn verify_causal_for_role<S: MessageStore>(
    msg: &Message,
    endpoint: &Endpoint,
    d: &Dialect,
    cast: &Cast,
    store: &S,
    thread: &ThreadId,
    root: &ContentHash,
) -> VerificationResult {
    let _ = endpoint; // the verdict is endpoint-independent in v1 (exact
                      // conformance); the parameter fixes the caller's view

    // REQ-613: a with-roles wrapper is legal only as the thread's root,
    // carrying the thread's one cast.
    if msg.wrapper_type() == Some(WrapperType::WithRoles) {
        return verify_cast_wrapper(msg, d, cast, store, thread, root);
    }

    let Some(simple) = msg.innermost_simple() else {
        // Meta messages carry no role obligations.
        return VerificationResult::Valid;
    };
    let perf = match simple.performative() {
        Some(p) => p.name(),
        None => return VerificationResult::Valid,
    };
    let annotation = d.find_performative(perf).and_then(|p| p.role.as_ref());

    // (i) Role conformance (REQ-612/615/626).
    let conformance = match annotation {
        Some(ann) => check_conformance(msg, simple, ann, cast),
        // Unannotated performative: no role obligation (R6 guarantees
        // protocol performatives are annotated in installed dialects).
        None => VerificationResult::Valid,
    };
    if let VerificationResult::Violation(_) = conformance {
        return conformance;
    }

    // (iii) R5 predecessor-type check against the dialect-level protocol
    // (ADR-604), with root typing (REQ-623) applied to the references.
    let caused_by = simple.caused_by().cloned();
    let rewritten = caused_by
        .as_ref()
        .map(|cb| rewrite_root_references(cb, root));
    let r5 = match &d.causal_protocol {
        Some(protocol) => verify_causal(perf, rewritten.as_ref(), store, protocol, thread),
        None => VerificationResult::Valid,
    };

    // (ii+) Occupant-counted fan-in (REQ-618) — the one extension over R5.
    let fanin = occupant_fanin(perf, caused_by.as_ref(), d, cast, store, thread);

    conformance.meet(r5).meet(fanin)
}

/// REQ-613: verify a `with-roles` wrapper. It is legal only as *the*
/// thread root: the caller-supplied `root` hash must resolve to a
/// `with-roles` wrapper equal to this one, its inner message must open the
/// thread (`:caused-by begin`), and its bindings must denote exactly the
/// thread's root cast. A second/mid-thread wrapper — one whose content
/// differs from the message stored at `root` — is a `Violation` (binding is
/// immutable for the life of the thread).
fn verify_cast_wrapper<S: MessageStore>(
    msg: &Message,
    d: &Dialect,
    cast: &Cast,
    store: &S,
    thread: &ThreadId,
    root: &ContentHash,
) -> VerificationResult {
    let Message::Wrapped {
        params, content, ..
    } = msg
    else {
        unreachable!("guarded by wrapper_type");
    };
    let Some(bindings) = params.first() else {
        return role_violation(String::from("with-roles wrapper has no bindings"));
    };
    let parsed = match parse_cast(bindings, &d.roles) {
        Ok(c) => c,
        Err(v) => return role_violation(format!("{v}")),
    };
    if &parsed != cast {
        return role_violation(String::from(
            "with-roles wrapper does not match the thread's root cast (REQ-613)",
        ));
    }
    // Root uniqueness (REQ-613): if the store already holds the thread's
    // root, this wrapper is legal only if it *is* that root message. A
    // distinct wrapper (a forged or duplicate root) is rejected, which also
    // stops it being referenced-as-root by a re-parenting attack.
    if let Some(root_msg) = store.lookup_in_thread(root, thread) {
        if root_msg != msg {
            return role_violation(String::from(
                "a second with-roles wrapper is not the thread root (REQ-613)",
            ));
        }
    }
    match content.innermost_simple().and_then(|m| m.caused_by()) {
        Some(CausedBy::Begin) => VerificationResult::Valid,
        _ => role_violation(String::from(
            "with-roles wrapper must be the thread's causal root (REQ-613)",
        )),
    }
}

/// REQ-612/615/626: sender key equals the cast binding for the `:from`
/// role; recipient keys equal the cast's keys for the `:to` set exactly.
fn check_conformance(
    outer: &Message,
    simple: &Message,
    ann: &RoleAnnotation,
    cast: &Cast,
) -> VerificationResult {
    // Sender (REQ-612): ratification by signature — the sender key must be
    // one the cast admits for the sender role. Receive-only roles never
    // send, so this clause never fires for them (REQ-626).
    let Some(sender) = signer_of(outer) else {
        return role_violation(String::from("role-annotated message carries no sender key"));
    };
    if !cast.admits(&ann.from, &AgentKey(String::from(sender))) {
        return role_violation(format!(
            "sender '{sender}' is not the cast's occupant of role '{}' (REQ-612)",
            ann.from
        ));
    }
    // Recipients (REQ-615): exact conformance, no subtyping (v1).
    let expected = expected_recipient_keys(ann, cast);
    let actual = simple.recipient_set();
    if expected != actual {
        return role_violation(format!(
            "recipients {actual:?} do not match the cast keys {expected:?} for :to roles {:?} (REQ-615)",
            ann.to
        ));
    }
    VerificationResult::Valid
}

/// REQ-623 (root typing): rewrite a `:caused-by` reference to the thread's
/// *genuine* root (the caller-supplied `root` hash) into the `begin`
/// predecessor type. Scoped to the exact root hash — not "any stored
/// `with-roles` wrapper" — so a forged mid-thread wrapper cannot be
/// referenced-as-root to smuggle a message in as a first step. A `Multiple`
/// is only ever a fan-in over non-root predecessors in v1, so it is left
/// untouched (mixing the root into a fan-in has no v1 use and would type
/// inconsistently otherwise).
fn rewrite_root_references(cb: &CausedBy, root: &ContentHash) -> CausedBy {
    match cb {
        CausedBy::Single(h) if h == &root.0 => CausedBy::Begin,
        other => other.clone(),
    }
}

/// REQ-618: occupant-counted `(all …)` fan-in. While any referenced
/// predecessor is absent the verdict is `Unknown` (R5 reports the same);
/// once all references resolve, the present referenced instances of each
/// indexed-sender predecessor type must include a distinct cast-admitted
/// sender for *every* sealed occupant, else `Violation` — permanent from
/// resolution (REQ-620).
fn occupant_fanin<S: MessageStore>(
    perf: &str,
    caused_by: Option<&CausedBy>,
    d: &Dialect,
    cast: &Cast,
    store: &S,
    thread: &ThreadId,
) -> VerificationResult {
    let Some(cp) = &d.causal_protocol else {
        return VerificationResult::Valid;
    };
    let Some(step) = cp.steps.get(perf) else {
        return VerificationResult::Valid;
    };

    // Indexed-sender predecessor types inside (all …) fan-ins.
    let mut counted: Vec<(&str, &BTreeSet<AgentKey>)> = Vec::new();
    for nr in &step.predecessors {
        let NodeRef::All(preds) = nr else { continue };
        for pred in preds {
            let Some(p_ann) = d.find_performative(pred).and_then(|p| p.role.as_ref()) else {
                continue;
            };
            let indexed = d
                .roles
                .iter()
                .any(|r| r.name == p_ann.from && matches!(r.cardinality, RoleCardinality::Indexed));
            if indexed {
                if let Some(occupants) = cast.indexed.get(&p_ann.from) {
                    counted.push((pred.as_str(), occupants));
                }
            }
        }
    }
    if counted.is_empty() {
        return VerificationResult::Valid;
    }

    // An occupant fan-in is only meaningful over a `(h1 h2 …)` reference.
    // With a single or absent `:caused-by`, this is not a well-formed
    // fan-in message at all — defer to R5, which reports the accurate
    // `MissingCausedBy`/`InvalidPredecessor`, rather than mislabelling it
    // as an occupant-coverage failure.
    let CausedBy::Multiple(hs) = (match caused_by {
        Some(cb) => cb,
        None => return VerificationResult::Valid,
    }) else {
        return VerificationResult::Valid;
    };
    let hashes: Vec<&str> = hs.iter().map(String::as_str).collect();
    let mut resolved: Vec<&Message> = Vec::new();
    for h in &hashes {
        match store.lookup_in_thread(&ContentHash(String::from(*h)), thread) {
            Some(m) => resolved.push(m),
            None => return VerificationResult::Unknown,
        }
    }

    for (pred_type, occupants) in counted {
        let mut senders: BTreeSet<&str> = BTreeSet::new();
        for m in &resolved {
            let Some(simple) = m.innermost_simple() else {
                continue;
            };
            if simple.performative().map(|p| p.name()) != Some(pred_type) {
                continue;
            }
            if let Some(k) = signer_of(m) {
                // Count only cast-admitted instances (REQ-618).
                if occupants.contains(&AgentKey(String::from(k))) {
                    senders.insert(k);
                }
            }
        }
        let missing: Vec<&str> = occupants
            .iter()
            .map(|k| k.0.as_str())
            .filter(|k| !senders.contains(*k))
            .collect();
        if !missing.is_empty() {
            return role_violation(format!(
                "fan-in over '{pred_type}' lacks instances from sealed occupant(s) {missing:?} (REQ-618)"
            ));
        }
    }
    VerificationResult::Valid
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dialect::{Dialect, PerformativeDef, ResourceBounds};
    use crate::protocol::StepDecl;
    use crate::role::parse_roles;
    use crate::store::ThreadedMessageStore;
    use alloc::string::ToString;
    use alloc::vec;

    fn perf(name: &str, from: &str, to: &[&str]) -> PerformativeDef {
        PerformativeDef {
            name: name.to_string(),
            params: Vec::new(),
            template: SExpr::Atom(Atom::Symbol("t".to_string())),
            role: Some(RoleAnnotation {
                from: from.to_string(),
                to: to.iter().map(|s| s.to_string()).collect(),
            }),
        }
    }

    fn single(name: &str) -> NodeRef {
        NodeRef::Single(name.to_string())
    }

    fn any(names: &[&str]) -> NodeRef {
        NodeRef::Any(names.iter().map(|s| s.to_string()).collect())
    }

    fn all_of(names: &[&str]) -> NodeRef {
        NodeRef::All(names.iter().map(|s| s.to_string()).collect())
    }

    fn step(name: &str, preds: Vec<NodeRef>, succs: Vec<NodeRef>) -> (String, StepDecl) {
        (
            name.to_string(),
            StepDecl {
                performative: name.to_string(),
                predecessors: preds,
                successors: succs,
            },
        )
    }

    fn dialect(
        roles_src: &str,
        perfs: Vec<PerformativeDef>,
        steps: Vec<(String, StepDecl)>,
    ) -> Dialect {
        Dialect {
            roles: parse_roles(&roles_src.parse::<SExpr>().unwrap()).unwrap(),
            name: "test".to_string(),
            extends: Vec::new(),
            author: None,
            performatives: perfs,
            resources: ResourceBounds {
                max_depth: 8,
                max_expansion_size: 512,
                verification_time_ms: 10,
            },
            examples: Vec::new(),
            signature: None,
            hash: None,
            protocol: None,
            causal_protocol: Some(CausalProtocol {
                steps: steps.into_iter().collect(),
            }),
            shapes: Vec::new(),
        }
    }

    /// The widened OAuth dialect of the paper (R6-clean).
    fn oauth() -> Dialect {
        dialect(
            "(server client authoriser)",
            vec![
                perf("login", "server", &["client", "authoriser"]),
                perf("abort", "server", &["client", "authoriser"]),
                perf("passwd", "client", &["authoriser", "server"]),
                perf("auth", "authoriser", &["server"]),
                perf("quit", "client", &["authoriser"]),
            ],
            vec![
                step("begin", vec![], vec![any(&["login", "abort"])]),
                step("login", vec![single("begin")], vec![single("passwd")]),
                step("abort", vec![single("begin")], vec![single("quit")]),
                step("passwd", vec![single("login")], vec![single("auth")]),
                step("auth", vec![single("passwd")], vec![]),
                step("quit", vec![single("abort")], vec![]),
            ],
        )
    }

    fn oauth_cast(d: &Dialect) -> Cast {
        parse_cast(
            &"((server @srv) (client @cli) (authoriser @as))"
                .parse::<SExpr>()
                .unwrap(),
            &d.roles,
        )
        .unwrap()
    }

    fn ep(role: &str) -> Endpoint {
        Endpoint {
            role: role.to_string(),
            occupant: None,
        }
    }

    fn msg(src: &str) -> Message {
        Message::try_from(&src.parse::<SExpr>().unwrap()).unwrap()
    }

    fn tid() -> ThreadId {
        ThreadId("conv".to_string())
    }

    fn put(store: &mut ThreadedMessageStore, h: &str, m: &Message) {
        store.append(ContentHash(h.to_string()), tid(), m.clone());
    }

    fn oauth_h0() -> Message {
        msg("(with-roles ((server @srv) (client @cli) (authoriser @as)) (signed @srv \"sig\" (hello :thread \"conv\" :caused-by begin)))")
    }

    // ---- REQ-609/610 / TEST-609/610/630: projection ----

    #[test]
    fn oauth_projections_match_the_paper() {
        let d = oauth();
        let server = project(&d, &ep("server"), None);
        assert_eq!(server.steps.get("login"), Some(&LocalStep::Send));
        assert_eq!(server.steps.get("abort"), Some(&LocalStep::Send));
        assert_eq!(server.steps.get("passwd"), Some(&LocalStep::Recv));
        assert_eq!(server.steps.get("auth"), Some(&LocalStep::Recv));
        assert_eq!(server.steps.get("quit"), None, "bystander erased");

        let client = project(&d, &ep("client"), None);
        assert_eq!(client.steps.get("passwd"), Some(&LocalStep::Send));
        assert_eq!(client.steps.get("quit"), Some(&LocalStep::Send));
        assert_eq!(client.steps.get("login"), Some(&LocalStep::Recv));
        assert_eq!(client.steps.get("auth"), None, "bystander erased");

        let authoriser = project(&d, &ep("authoriser"), None);
        assert_eq!(authoriser.steps.get("auth"), Some(&LocalStep::Send));
        assert_eq!(authoriser.steps.get("passwd"), Some(&LocalStep::Recv));
        assert_eq!(authoriser.steps.get("quit"), Some(&LocalStep::Recv));
    }

    #[test]
    fn projection_keeps_raw_predecessor_clauses() {
        let d = oauth();
        for role in ["server", "client", "authoriser"] {
            let local = project(&d, &ep(role), None);
            assert_eq!(local.protocol, d.causal_protocol, "raw edges (REQ-610)");
        }
    }

    #[test]
    fn projection_is_deterministic() {
        let d = oauth();
        assert_eq!(
            project(&d, &ep("client"), None),
            project(&d, &ep("client"), None)
        );
    }

    // ---- REQ-623 / TEST-623: root typing ----

    #[test]
    fn first_step_naming_root_hash_verifies() {
        let d = oauth();
        let cast = oauth_cast(&d);
        let mut store = ThreadedMessageStore::new();
        put(&mut store, "h0", &oauth_h0());
        let h1 = msg("(signed @srv \"sig\" (login (@as @cli) \"n-42\" :caused-by h0))");
        assert_eq!(
            verify_causal_for_role(
                &h1,
                &ep("client"),
                &d,
                &cast,
                &store,
                &tid(),
                &ContentHash("h0".to_string())
            ),
            VerificationResult::Valid
        );
    }

    // ---- REQ-612/615 / TEST-612/615: conformance ----

    #[test]
    fn non_nominee_cannot_squat_a_role() {
        let d = oauth();
        let cast = oauth_cast(&d);
        let mut store = ThreadedMessageStore::new();
        put(&mut store, "h0", &oauth_h0());
        let evil = msg("(signed @evil \"sig\" (login (@as @cli) \"n\" :caused-by h0))");
        assert!(matches!(
            verify_causal_for_role(
                &evil,
                &ep("client"),
                &d,
                &cast,
                &store,
                &tid(),
                &ContentHash("h0".to_string())
            ),
            VerificationResult::Violation(CausalViolation::RoleConformance { .. })
        ));
    }

    #[test]
    fn narrowed_recipients_violate_conformance() {
        let d = oauth();
        let cast = oauth_cast(&d);
        let mut store = ThreadedMessageStore::new();
        put(&mut store, "h0", &oauth_h0());
        // login must go to both client and authoriser under the widened :to
        let narrow = msg("(signed @srv \"sig\" (login @cli \"n\" :caused-by h0))");
        assert!(matches!(
            verify_causal_for_role(
                &narrow,
                &ep("client"),
                &d,
                &cast,
                &store,
                &tid(),
                &ContentHash("h0".to_string())
            ),
            VerificationResult::Violation(CausalViolation::RoleConformance { .. })
        ));
    }

    // ---- REQ-619 / TEST-619 + out-of-order delivery ----

    #[test]
    fn out_of_order_is_unknown_then_valid() {
        let d = oauth();
        let cast = oauth_cast(&d);
        let mut store = ThreadedMessageStore::new();
        put(&mut store, "h0", &oauth_h0());
        let h1 = msg("(signed @srv \"sig\" (login (@as @cli) \"n-42\" :caused-by h0))");
        let h2 = msg("(signed @cli \"sig\" (passwd (@as @srv) \"cred\" :caused-by h1))");
        // h2 arrives before h1: Unknown (a message the role will see has
        // not yet arrived), never Violation.
        assert_eq!(
            verify_causal_for_role(
                &h2,
                &ep("authoriser"),
                &d,
                &cast,
                &store,
                &tid(),
                &ContentHash("h0".to_string())
            ),
            VerificationResult::Unknown
        );
        put(&mut store, "h1", &h1);
        assert_eq!(
            verify_causal_for_role(
                &h2,
                &ep("authoriser"),
                &d,
                &cast,
                &store,
                &tid(),
                &ContentHash("h0".to_string())
            ),
            VerificationResult::Valid
        );
    }

    #[test]
    fn vacant_role_dependency_stays_unknown() {
        let d = oauth();
        let cast = oauth_cast(&d);
        let store = ThreadedMessageStore::new();
        let auth = msg("(signed @as \"sig\" (auth @srv \"tok\" :caused-by h-never))");
        assert_eq!(
            verify_causal_for_role(
                &auth,
                &ep("server"),
                &d,
                &cast,
                &store,
                &tid(),
                &ContentHash("h0".to_string())
            ),
            VerificationResult::Unknown
        );
    }

    // ---- REQ-613 / TEST-613: root uniqueness ----

    #[test]
    fn foreign_cast_wrapper_is_a_violation() {
        let d = oauth();
        let cast = oauth_cast(&d);
        let store = ThreadedMessageStore::new();
        let second = msg("(with-roles ((server @evil) (client @cli) (authoriser @as)) (signed @evil \"sig\" (hello :caused-by begin)))");
        assert!(matches!(
            verify_causal_for_role(
                &second,
                &ep("client"),
                &d,
                &cast,
                &store,
                &tid(),
                &ContentHash("h0".to_string())
            ),
            VerificationResult::Violation(CausalViolation::RoleConformance { .. })
        ));
    }

    #[test]
    fn non_root_wrapper_is_a_violation() {
        let d = oauth();
        let cast = oauth_cast(&d);
        let store = ThreadedMessageStore::new();
        let late = msg("(with-roles ((server @srv) (client @cli) (authoriser @as)) (signed @srv \"sig\" (hello :caused-by h0)))");
        assert!(matches!(
            verify_causal_for_role(
                &late,
                &ep("client"),
                &d,
                &cast,
                &store,
                &tid(),
                &ContentHash("h0".to_string())
            ),
            VerificationResult::Violation(CausalViolation::RoleConformance { .. })
        ));
    }

    // ---- Forgery regressions (adversarial review, HIGH findings) ----

    #[test]
    fn unsigned_sender_field_cannot_occupy_a_role() {
        // An unsigned message self-asserting :sender must NOT ratify a role
        // (ratification is by signature, REQ-612).
        let d = oauth();
        let cast = oauth_cast(&d);
        let mut store = ThreadedMessageStore::new();
        put(&mut store, "h0", &oauth_h0());
        let forged = msg("(login (@as @cli) \"n\" :sender @srv :caused-by h0)");
        assert!(matches!(
            verify_causal_for_role(
                &forged,
                &ep("client"),
                &d,
                &cast,
                &store,
                &tid(),
                &ContentHash("h0".to_string())
            ),
            VerificationResult::Violation(CausalViolation::RoleConformance { .. })
        ));
    }

    #[test]
    fn forged_second_root_wrapper_is_rejected() {
        // A second with-roles wrapper (distinct from the stored root) is a
        // Violation, and cannot be referenced-as-root (REQ-613).
        let d = oauth();
        let cast = oauth_cast(&d);
        let mut store = ThreadedMessageStore::new();
        put(&mut store, "h0", &oauth_h0());
        let second = msg("(with-roles ((server @srv) (client @cli) (authoriser @as)) (signed @cli \"sig\" (hello :caused-by begin)))");
        put(&mut store, "h9", &second);
        // The forged wrapper itself is a Violation (not the thread root).
        assert!(matches!(
            verify_causal_for_role(
                &second,
                &ep("client"),
                &d,
                &cast,
                &store,
                &tid(),
                &ContentHash("h0".to_string())
            ),
            VerificationResult::Violation(CausalViolation::RoleConformance { .. })
        ));
        // A message re-parented onto the forged wrapper does NOT verify as a
        // first step: h9 is not the root, so its type (hello) is an illegal
        // predecessor of login.
        let reparented = msg("(signed @srv \"sig\" (login (@as @cli) \"n\" :caused-by h9))");
        assert!(matches!(
            verify_causal_for_role(
                &reparented,
                &ep("client"),
                &d,
                &cast,
                &store,
                &tid(),
                &ContentHash("h0".to_string())
            ),
            VerificationResult::Violation(_)
        ));
    }

    #[test]
    fn receive_only_role_needs_no_signature_to_be_addressed() {
        // REQ-626: a message addressed to a nominated receive-only role is
        // conformant without any ratifying signature from that role — the
        // recipient never signs. Here `client` is a pure recipient of login.
        let d = oauth();
        let cast = oauth_cast(&d);
        let mut store = ThreadedMessageStore::new();
        put(&mut store, "h0", &oauth_h0());
        let login = msg("(signed @srv \"sig\" (login (@as @cli) \"n-42\" :caused-by h0))");
        // client is addressed but contributes no signature; still Valid.
        assert_eq!(
            verify_causal_for_role(
                &login,
                &ep("client"),
                &d,
                &cast,
                &store,
                &tid(),
                &ContentHash("h0".to_string())
            ),
            VerificationResult::Valid
        );
    }

    #[test]
    fn matching_root_wrapper_is_valid() {
        let d = oauth();
        let cast = oauth_cast(&d);
        let store = ThreadedMessageStore::new();
        assert_eq!(
            verify_causal_for_role(
                &oauth_h0(),
                &ep("client"),
                &d,
                &cast,
                &store,
                &tid(),
                &ContentHash("h0".to_string())
            ),
            VerificationResult::Valid
        );
    }

    // ---- REQ-618 / TEST-618: occupant-counted fan-in (auction) ----

    fn auction() -> Dialect {
        dialect(
            "(auctioneer (* bidder))",
            vec![
                perf("commit", "bidder", &["auctioneer"]),
                perf("reveal", "bidder", &["auctioneer"]),
                perf("declare-winner", "auctioneer", &[]),
            ],
            vec![
                step("begin", vec![], vec![single("commit")]),
                step("commit", vec![single("begin")], vec![single("reveal")]),
                step("reveal", vec![single("commit")], vec![]),
                step("declare-winner", vec![all_of(&["reveal"])], vec![]),
            ],
        )
    }

    fn auction_cast(d: &Dialect) -> Cast {
        parse_cast(
            &"((auctioneer @auc) (bidder @b1 @b2 @b3))"
                .parse::<SExpr>()
                .unwrap(),
            &d.roles,
        )
        .unwrap()
    }

    fn auction_store() -> ThreadedMessageStore {
        let mut store = ThreadedMessageStore::new();
        put(&mut store, "h0", &msg("(with-roles ((auctioneer @auc) (bidder @b1 @b2 @b3)) (signed @auc \"sig\" (hello :thread \"conv\" :caused-by begin)))"));
        for (i, b) in ["@b1", "@b2", "@b3"].iter().enumerate() {
            let hc = alloc::format!("h{}", i + 1);
            let hr = alloc::format!("h{}", i + 4);
            put(
                &mut store,
                &hc,
                &msg(&alloc::format!(
                    "(signed {b} \"sig\" (commit @auc \"c\" :caused-by h0))"
                )),
            );
            put(
                &mut store,
                &hr,
                &msg(&alloc::format!(
                    "(signed {b} \"sig\" (reveal @auc 42 :caused-by {hc}))"
                )),
            );
        }
        store
    }

    #[test]
    fn fanin_unknown_until_all_reveals_then_valid() {
        let d = auction();
        let cast = auction_cast(&d);
        let mut store = ThreadedMessageStore::new();
        put(&mut store, "h0", &msg("(with-roles ((auctioneer @auc) (bidder @b1 @b2 @b3)) (signed @auc \"sig\" (hello :caused-by begin)))"));
        put(
            &mut store,
            "h1",
            &msg("(signed @b1 \"sig\" (commit @auc \"c\" :caused-by h0))"),
        );
        put(
            &mut store,
            "h2",
            &msg("(signed @b2 \"sig\" (commit @auc \"c\" :caused-by h0))"),
        );
        put(
            &mut store,
            "h4",
            &msg("(signed @b1 \"sig\" (reveal @auc 42 :caused-by h1))"),
        );
        put(
            &mut store,
            "h5",
            &msg("(signed @b2 \"sig\" (reveal @auc 17 :caused-by h2))"),
        );
        let h7 = msg("(signed @auc \"sig\" (declare-winner \"b3\" :caused-by (h4 h5 h6)))");
        // h6 absent: Unknown
        assert_eq!(
            verify_causal_for_role(
                &h7,
                &ep("auctioneer"),
                &d,
                &cast,
                &store,
                &tid(),
                &ContentHash("h0".to_string())
            ),
            VerificationResult::Unknown
        );
        put(
            &mut store,
            "h3",
            &msg("(signed @b3 \"sig\" (commit @auc \"c\" :caused-by h0))"),
        );
        put(
            &mut store,
            "h6",
            &msg("(signed @b3 \"sig\" (reveal @auc 55 :caused-by h3))"),
        );
        assert_eq!(
            verify_causal_for_role(
                &h7,
                &ep("auctioneer"),
                &d,
                &cast,
                &store,
                &tid(),
                &ContentHash("h0".to_string())
            ),
            VerificationResult::Valid
        );
    }

    #[test]
    fn resolved_fanin_missing_an_occupant_is_a_violation() {
        // R5's type-level (all reveal) is satisfied by ANY reveal; the
        // occupant count is the role layer's extension (REQ-618).
        let d = auction();
        let cast = auction_cast(&d);
        let store = auction_store();
        let h7 = msg("(signed @auc \"sig\" (declare-winner \"b1\" :caused-by (h4 h5)))");
        assert!(matches!(
            verify_causal_for_role(
                &h7,
                &ep("auctioneer"),
                &d,
                &cast,
                &store,
                &tid(),
                &ContentHash("h0".to_string())
            ),
            VerificationResult::Violation(CausalViolation::RoleConformance { .. })
        ));
    }

    #[test]
    fn non_member_instance_does_not_count_toward_coverage() {
        let d = auction();
        let cast = auction_cast(&d);
        let mut store = auction_store();
        // b4 is outside the sealed membership; its reveal replaces b3's.
        put(
            &mut store,
            "hx",
            &msg("(signed @b4 \"sig\" (reveal @auc 99 :caused-by h3))"),
        );
        let h7 = msg("(signed @auc \"sig\" (declare-winner \"b1\" :caused-by (h4 h5 hx)))");
        assert!(matches!(
            verify_causal_for_role(
                &h7,
                &ep("auctioneer"),
                &d,
                &cast,
                &store,
                &tid(),
                &ContentHash("h0".to_string())
            ),
            VerificationResult::Violation(CausalViolation::RoleConformance { .. })
        ));
    }

    #[test]
    fn full_auction_trace_verifies_end_to_end() {
        let d = auction();
        let cast = auction_cast(&d);
        let store = auction_store();
        for (h, role) in [
            ("h1", "bidder"),
            ("h2", "bidder"),
            ("h3", "bidder"),
            ("h4", "bidder"),
            ("h5", "bidder"),
            ("h6", "bidder"),
        ] {
            let m = store
                .lookup_in_thread(&ContentHash(h.to_string()), &tid())
                .unwrap()
                .clone();
            assert_eq!(
                verify_causal_for_role(
                    &m,
                    &ep(role),
                    &d,
                    &cast,
                    &store,
                    &tid(),
                    &ContentHash("h0".to_string())
                ),
                VerificationResult::Valid,
                "{h} should be Valid"
            );
        }
        let h7 = msg("(signed @auc \"sig\" (declare-winner \"b3\" :caused-by (h4 h5 h6)))");
        assert_eq!(
            verify_causal_for_role(
                &h7,
                &ep("auctioneer"),
                &d,
                &cast,
                &store,
                &tid(),
                &ContentHash("h0".to_string())
            ),
            VerificationResult::Valid
        );
    }
}
