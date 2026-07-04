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
use crate::role::{parse_wrapper_cast, AgentKey, Cast, Endpoint, R6Violation, RoleAnnotation};
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
    /// ExpectEnvelope steps (SPEC-015 REQ-709): the performatives whose
    /// *redacted envelopes* this endpoint awaits under a
    /// `(:causal-locality derive)` dialect — a Recv-analogue carrying no
    /// payload obligation, one per derived route naming this endpoint.
    ///
    /// A separate step set, not a [`LocalStep`] variant in `steps`: a
    /// per-occupant endpoint of an indexed role can hold *both* Send (its
    /// own instance) and ExpectEnvelope (its co-occupants' instances) for
    /// one performative type, which a single-valued step map cannot
    /// express. Send/Recv steps and payload delivery are untouched; empty
    /// under `reject` (the v1 reading, bit-for-bit).
    #[cfg_attr(feature = "serde", serde(default))]
    pub expect_envelopes: BTreeSet<String>,
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
/// `cast` is accepted for per-occupant instantiation (CON-602). The
/// Send/Recv step set is identical across an indexed role's occupants;
/// under a `(:causal-locality derive)` dialect the cast additionally
/// drives the thread-open half of the envelope-route derivation (SPEC-015
/// REQ-709), whose ExpectEnvelope steps *are* occupant-dependent.
pub fn project(d: &Dialect, endpoint: &Endpoint, cast: Option<&Cast>) -> LocalProtocol {
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
    // ExpectEnvelope steps (REQ-709): one per derived route naming this
    // endpoint. Under the default `reject` this set is empty and the
    // projection is the v1 function bit-for-bit.
    let mut expect_envelopes: BTreeSet<String> = BTreeSet::new();
    if let crate::role::CausalLocality::Derive(table) = &d.causal_locality {
        // Install-time (dialect-level) routes: role-addressed.
        for (perf, roles) in &table.0 {
            if roles.contains(&endpoint.role) {
                expect_envelopes.insert(perf.clone());
            }
        }
        // Thread-open (per-occupant) routes: derived here as a pure
        // function of dialect and sealed cast — the same table every
        // agent computes (REQ-709) — and read for this endpoint's
        // occupant.
        if let (Some(cast), Some(occupant)) = (cast, &endpoint.occupant) {
            let occ = crate::r6::derive_occupant_envelope_routes(d, cast);
            for (perf, keys) in &occ.0 {
                if keys.contains(occupant) {
                    expect_envelopes.insert(perf.clone());
                }
            }
        }
    }
    LocalProtocol {
        steps,
        expect_envelopes,
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

/// Role-local verification (REQ-612..620, 623, 626, 628; CON-602): the
/// lattice meet of role conformance, the unchanged R5 predecessor check
/// against the dialect-level protocol, and the occupant-counted fan-in,
/// gated by the root's dialect pin when one is present.
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

    // REQ-628: dialect pin. When the thread's root cast pins the governing
    // dialect's content hash and the verifier's installed dialect carries
    // its hash (DialectRegistry::install populates it), the two must agree —
    // otherwise this verifier would check the thread against a different
    // protocol than the root named, so every message of the thread is a
    // Violation. An unpinned cast (`dialect_pin: None`) is accepted as-is:
    // the spec's transition plan is warn-then-reject, and the verdict
    // lattice (Unknown/Valid/Violation) has no warning level to carry the
    // "warn" half, so this release accepts silently.
    // SIMPLIFY: when the transition window closes, reject `None` pins here
    // (and surface a warning signal in the interim if one is added).
    if let (Some(pinned), Some(installed)) = (cast.dialect_pin.as_deref(), d.hash.as_deref()) {
        if pinned != installed {
            return role_violation(format!(
                "{}",
                R6Violation::DialectPinMismatch {
                    pinned: String::from(pinned),
                    installed: String::from(installed),
                }
            ));
        }
    }

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
    // Exact shape (CON-601, REQ-628): the wrapper is `(with-roles
    // (<bindings>) [:dialect sha256:<hex64>] <signed-form>)` — the bindings
    // list, then at most the optional dialect pin, no more. A malformed pin
    // is a parse rejection, never repaired (LangSec principle 4).
    let parsed = match parse_wrapper_cast(params, &d.roles) {
        Ok(c) => c,
        Err(v) => return role_violation(format!("{v}")),
    };
    if &parsed != cast {
        return role_violation(String::from(
            "with-roles wrapper does not match the thread's root cast (REQ-613)",
        ));
    }
    // The payload MUST be the existing `signed` form (CON-601): the cast is
    // ratified by the initiator's signature, so an unsigned root is not a
    // valid nomination. Reject anything whose immediate content is not a
    // signed wrapper before accepting the cast (REQ-611).
    if !matches!(
        content.as_ref(),
        Message::Wrapped {
            wrapper: WrapperType::Signed,
            ..
        }
    ) {
        return role_violation(String::from(
            "with-roles payload must be a signed message (CON-601)",
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
            // The cast holds a sealed membership only for indexed roles, so a
            // `Some` here already means `p_ann.from` is an indexed sender — no
            // separate cardinality check against `d.roles` is needed.
            if let Some(occupants) = cast.indexed.get(&p_ann.from) {
                counted.push((pred.as_str(), occupants));
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
            // SPEC-015 REQ-703: completion requires content. Only full
            // messages enter `resolved` — a member present solely as a
            // redacted envelope (`store.envelope_in_thread`) is deliberately
            // NOT consulted here, because fan-in membership is "present and
            // Valid" and full validity includes payload grammaticality. The
            // decider's verdict stays Unknown (not-yet-complete) until the
            // full members arrive, which is monotone-safe; the envelope
            // satisfies only the safety-level type checks of R5
            // (`protocol::predecessor_type`, REQ-702).
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
    use crate::role::{parse_cast, parse_roles};
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
            causal_locality: Default::default(),
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

    // ---- SPEC-015 REQ-709 / TEST-709: ExpectEnvelope steps ----

    /// The paper's OAuth fragment *as written* (R6(vi)-failing), with the
    /// dialect-level closure recorded as `DialectRegistry::install` would
    /// under `(:causal-locality derive)`.
    fn derived_oauth() -> Dialect {
        let mut d = dialect(
            "(server client authoriser)",
            vec![
                perf("login", "server", &["client"]),
                perf("abort", "server", &["client"]),
                perf("passwd", "client", &["authoriser"]),
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
        );
        d.causal_locality =
            crate::role::CausalLocality::Derive(crate::r6::derive_envelope_routes(&d));
        d
    }

    #[test]
    fn reject_mode_projection_has_no_envelope_steps() {
        // The v1 reading, bit-for-bit: under the default `reject` no
        // ExpectEnvelope step exists for any endpoint.
        let d = oauth();
        for role in ["server", "client", "authoriser"] {
            assert!(project(&d, &ep(role), None).expect_envelopes.is_empty());
        }
    }

    #[test]
    fn derived_projection_emits_expect_envelope_per_route() {
        let d = derived_oauth();
        // Routes: login ⇒ authoriser, abort ⇒ authoriser, passwd ⇒ server.
        let authoriser = project(&d, &ep("authoriser"), None);
        let expected: BTreeSet<String> =
            ["login", "abort"].iter().map(|s| s.to_string()).collect();
        assert_eq!(authoriser.expect_envelopes, expected);
        let server = project(&d, &ep("server"), None);
        let expected: BTreeSet<String> = ["passwd"].iter().map(|s| s.to_string()).collect();
        assert_eq!(server.expect_envelopes, expected);
        // client is on no derived route.
        assert!(project(&d, &ep("client"), None).expect_envelopes.is_empty());
    }

    #[test]
    fn expect_envelope_leaves_send_recv_steps_untouched() {
        // The Send/Recv step map of the derived dialect equals the
        // unwidened v1 projection — payload delivery is untouched.
        let d = derived_oauth();
        let mut v1 = d.clone();
        v1.causal_locality = crate::role::CausalLocality::Reject;
        for role in ["server", "client", "authoriser"] {
            assert_eq!(
                project(&d, &ep(role), None).steps,
                project(&v1, &ep(role), None).steps,
            );
        }
    }

    #[test]
    fn per_occupant_expect_envelope_steps_come_from_the_sealed_cast() {
        // The announcing auction: declare-winner :to bidder passes
        // dialect-level R6(vi), so the install table is empty and the
        // ExpectEnvelope steps exist only for occupant endpoints under a
        // sealed cast (thread open) — covering the widened prefix
        // (commit), not just reveal.
        let mut d = dialect(
            "(auctioneer (* bidder))",
            vec![
                perf("commit", "bidder", &["auctioneer"]),
                perf("reveal", "bidder", &["auctioneer"]),
                perf("declare-winner", "auctioneer", &["bidder"]),
            ],
            vec![
                step("begin", vec![], vec![single("commit")]),
                step("commit", vec![single("begin")], vec![single("reveal")]),
                step("reveal", vec![single("commit")], vec![]),
                step("declare-winner", vec![all_of(&["reveal"])], vec![]),
            ],
        );
        d.causal_locality =
            crate::role::CausalLocality::Derive(crate::r6::derive_envelope_routes(&d));
        let cast = auction_cast(&d);

        // Occupant endpoint at thread open: awaits co-occupant envelopes
        // of reveal AND commit — while still *sending* its own instances.
        let b1 = Endpoint {
            role: "bidder".to_string(),
            occupant: Some(AgentKey("@b1".to_string())),
        };
        let local = project(&d, &b1, Some(&cast));
        let expected: BTreeSet<String> =
            ["commit", "reveal"].iter().map(|s| s.to_string()).collect();
        assert_eq!(local.expect_envelopes, expected);
        assert_eq!(local.steps.get("commit"), Some(&LocalStep::Send));
        assert_eq!(local.steps.get("reveal"), Some(&LocalStep::Send));

        // Without a cast (before thread open) the per-occupant routes
        // cannot exist yet; the auctioneer is on no route either way.
        assert!(project(&d, &b1, None).expect_envelopes.is_empty());
        let auc = project(&d, &ep("auctioneer"), Some(&cast));
        assert!(auc.expect_envelopes.is_empty());
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

    #[test]
    fn unsigned_root_payload_is_rejected() {
        // CON-601: the with-roles payload must be the signed form. An
        // unsigned inner message, even with the right cast and caused-by
        // begin, is not a valid nomination.
        let d = oauth();
        let cast = oauth_cast(&d);
        let store = ThreadedMessageStore::new();
        let unsigned = msg("(with-roles ((server @srv) (client @cli) (authoriser @as)) (hello :thread \"conv\" :caused-by begin))");
        assert!(matches!(
            verify_causal_for_role(
                &unsigned,
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
    fn root_wrapper_with_extra_params_is_rejected() {
        // CON-601 exact arity: exactly one bindings list.
        let d = oauth();
        let cast = oauth_cast(&d);
        let store = ThreadedMessageStore::new();
        let extra = msg("(with-roles ((server @srv) (client @cli) (authoriser @as)) junk (signed @srv \"sig\" (hello :caused-by begin)))");
        assert!(matches!(
            verify_causal_for_role(
                &extra,
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

    // ---- REQ-628 / TEST-642: dialect pin ----

    /// The OAuth dialect with its canonical content hash populated, as
    /// `DialectRegistry::install` would leave it (`ensure_hash`).
    fn hashed_oauth() -> Dialect {
        let mut d = oauth();
        d.hash = Some(crate::canonical::dialect_hash(&d));
        d
    }

    fn pinned_h0(pin: &str) -> Message {
        msg(&format!(
            "(with-roles ((server @srv) (client @cli) (authoriser @as)) :dialect {pin} (signed @srv \"sig\" (hello :thread \"conv\" :caused-by begin)))"
        ))
    }

    /// The thread's root cast as the wrapper nominates it, pin included.
    fn pinned_cast(d: &Dialect, root: &Message) -> Cast {
        let Message::Wrapped { params, .. } = root else {
            panic!("root fixture is a wrapper");
        };
        parse_wrapper_cast(params, &d.roles).unwrap()
    }

    #[test]
    fn pinned_root_matching_installed_hash_verifies() {
        let d = hashed_oauth();
        let pin = d.hash.clone().unwrap();
        let root = pinned_h0(&pin);
        let cast = pinned_cast(&d, &root);
        let mut store = ThreadedMessageStore::new();
        put(&mut store, "h0", &root);
        // The pinned wrapper itself verifies …
        assert_eq!(
            verify_causal_for_role(
                &root,
                &ep("client"),
                &d,
                &cast,
                &store,
                &tid(),
                &ContentHash("h0".to_string())
            ),
            VerificationResult::Valid
        );
        // … and so does a first step of the pinned thread.
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

    #[test]
    fn pin_mismatch_is_a_typed_violation_for_every_thread_message() {
        // The root pins a different (same-named, divergent) dialect than
        // the verifier installed: the typed REQ-628 violation fires for the
        // wrapper and for every subsequent message of the thread.
        let d = hashed_oauth();
        let stale = format!("sha256:{}", "0".repeat(64));
        let root = pinned_h0(&stale);
        let cast = pinned_cast(&d, &root);
        let mut store = ThreadedMessageStore::new();
        put(&mut store, "h0", &root);
        let h1 = msg("(signed @srv \"sig\" (login (@as @cli) \"n-42\" :caused-by h0))");
        for m in [&root, &h1] {
            match verify_causal_for_role(
                m,
                &ep("client"),
                &d,
                &cast,
                &store,
                &tid(),
                &ContentHash("h0".to_string()),
            ) {
                VerificationResult::Violation(CausalViolation::RoleConformance { reason }) => {
                    assert!(
                        reason.contains("REQ-628"),
                        "expected the typed pin violation, got: {reason}"
                    );
                }
                other => panic!("expected the REQ-628 violation, got {other:?}"),
            }
        }
    }

    #[test]
    fn unpinned_root_still_verifies_during_transition() {
        // REQ-628 transition (warn-then-reject): an unpinned wrapper is
        // accepted as today, even when the installed dialect carries its
        // hash — see the REQ-628 comment in `verify_causal_for_role`.
        let d = hashed_oauth();
        let cast = oauth_cast(&d);
        let mut store = ThreadedMessageStore::new();
        put(&mut store, "h0", &oauth_h0());
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

    #[test]
    fn malformed_pin_on_root_is_rejected() {
        // LangSec: a malformed `:dialect` value (bad prefix, wrong length)
        // is a parse rejection surfaced as a Violation, never repaired.
        let d = hashed_oauth();
        let cast = oauth_cast(&d);
        let store = ThreadedMessageStore::new();
        for bad in [
            "(with-roles ((server @srv) (client @cli) (authoriser @as)) :dialect sha256:abc (signed @srv \"sig\" (hello :caused-by begin)))",
            "(with-roles ((server @srv) (client @cli) (authoriser @as)) :dialect md5:0000 (signed @srv \"sig\" (hello :caused-by begin)))",
        ] {
            assert!(matches!(
                verify_causal_for_role(
                    &msg(bad),
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

    // ---- SPEC-015 TEST-703: completion still requires content ----

    use crate::attest::{sign_attestation_v2, AttestationHeader};
    use crate::envelope::RedactedEnvelope;
    use crate::keyid::KeyId;
    use crate::r4::Signer;

    /// Data-dependent test signer (as in `attest.rs`); distinct secrets
    /// model the distinct bidder keys.
    struct TestSigner {
        secret: &'static str,
    }

    impl Signer for TestSigner {
        fn sign(&self, data: &[u8]) -> Vec<u8> {
            use sha2::{Digest, Sha256};
            let mut h = Sha256::new();
            h.update(self.secret.as_bytes());
            h.update(data);
            h.finalize().to_vec()
        }
        fn verify(&self, data: &[u8], sig: &[u8]) -> bool {
            self.sign(data) == sig
        }
    }

    /// A signed reveal envelope for bidder `b` (SPEC-015 REQ-700/701):
    /// authenticated header only — no bid value anywhere.
    fn reveal_envelope(bidder: &str, content_hash: &str, commit_hash: &str) -> RedactedEnvelope {
        let mut to = BTreeSet::new();
        to.insert(KeyId::parse("@auc").unwrap());
        let header = AttestationHeader {
            content_hash: content_hash.to_string(),
            performative: String::from("reveal"),
            from: KeyId::parse(bidder).unwrap(),
            to,
            thread: String::from("conv"),
            caused_by: Some(crate::message::CausedBy::Single(String::from(commit_hash))),
        };
        let signer = TestSigner {
            secret: match bidder {
                "@b1" => "b1",
                "@b2" => "b2",
                _ => "b3",
            },
        };
        let signature = sign_attestation_v2(&signer, &header).unwrap();
        RedactedEnvelope { header, signature }
    }

    /// TEST-703: a fan-in decider whose member reveals are present only as
    /// envelopes reports the fan-in not-yet-complete (Unknown); supplying
    /// the full members completes it (Valid). Meanwhile the *safety-level*
    /// R5 check resolves from the very same envelopes (REQ-702) — the
    /// REQ-703 boundary is exactly the completion-level occupant fan-in.
    #[test]
    fn test_703_envelope_only_members_leave_the_fanin_incomplete() {
        let d = auction();
        let cast = auction_cast(&d);
        // Root and full commits; reveals arrive only as redacted envelopes.
        let mut store = ThreadedMessageStore::new();
        put(&mut store, "h0", &msg("(with-roles ((auctioneer @auc) (bidder @b1 @b2 @b3)) (signed @auc \"sig\" (hello :thread \"conv\" :caused-by begin)))"));
        for (i, b) in ["@b1", "@b2", "@b3"].iter().enumerate() {
            let hc = alloc::format!("h{}", i + 1);
            put(
                &mut store,
                &hc,
                &msg(&alloc::format!(
                    "(signed {b} \"sig\" (commit @auc \"c\" :caused-by h0))"
                )),
            );
            let hr = alloc::format!("h{}", i + 4);
            let signer = TestSigner {
                secret: match *b {
                    "@b1" => "b1",
                    "@b2" => "b2",
                    _ => "b3",
                },
            };
            store
                .append_envelope(reveal_envelope(b, &hr, &hc), &signer)
                .unwrap();
        }

        let h7 = msg("(signed @auc \"sig\" (declare-winner \"b3\" :caused-by (h4 h5 h6)))");

        // Safety level (REQ-702): the R5 type check over the fan-in
        // resolves from the envelopes' authenticated types.
        let simple = h7.innermost_simple().unwrap();
        assert_eq!(
            crate::protocol::verify_causal(
                "declare-winner",
                simple.caused_by(),
                &store,
                d.causal_protocol.as_ref().unwrap(),
                &tid(),
            ),
            VerificationResult::Valid
        );

        // Completion level (REQ-703): the occupant fan-in still demands
        // full messages — envelope-only members are not-yet-complete.
        let decide = |store: &ThreadedMessageStore| {
            verify_causal_for_role(
                &h7,
                &ep("auctioneer"),
                &d,
                &cast,
                store,
                &tid(),
                &ContentHash("h0".to_string()),
            )
        };
        assert_eq!(decide(&store), VerificationResult::Unknown);

        // Supplying the full members completes the fan-in.
        for (i, b) in ["@b1", "@b2", "@b3"].iter().enumerate() {
            put(
                &mut store,
                &alloc::format!("h{}", i + 4),
                &msg(&alloc::format!(
                    "(signed {b} \"sig\" (reveal @auc 42 :caused-by h{}))",
                    i + 1
                )),
            );
        }
        assert_eq!(decide(&store), VerificationResult::Valid);
    }
}
