// Frozen pre-refactor reference from cbcl-rs 4a6c020, protocol.rs.
// Used only for differential regression testing, not as a formal specification.
use cbcl_core::message::CausedBy;
use cbcl_core::protocol::{
    CausalProtocol, CausalViolation, NodeRef, StepDecl, VerificationResult, BEGIN_KEYWORD,
};
use cbcl_core::store::{ContentHash, MessageStore, ThreadId};
use std::collections::BTreeSet;

fn predecessor_type<'a, S: MessageStore>(
    store: &'a S,
    hash: &ContentHash,
    thread: &ThreadId,
) -> Option<&'a str> {
    if let Some(predecessor_msg) = store.lookup_in_thread(hash, thread) {
        // Type through wrappers: the agent stores whole (possibly signed)
        // messages, so a wrapped predecessor must type as its innermost
        // Simple (SPEC-014; pre-existing Simple behaviour unchanged).
        return Some(
            predecessor_msg
                .innermost_simple()
                .and_then(|m| m.performative())
                .map(|p| p.name())
                .unwrap_or(""),
        );
    }
    if let Some(e) = store.envelope_in_thread(hash, thread) {
        return Some(e.performative());
    }
    store
        .opened_in_thread(hash, thread)
        .and_then(|e| e.performative())
}

/// Collect performative names allowed as single-message predecessors.
///
/// Gathers names from `Single` and `Any` node-refs (not `All`, which is for fan-in).
fn allowed_single_predecessors(step: &StepDecl) -> Vec<String> {
    let mut types = Vec::new();
    for nr in &step.predecessors {
        match nr {
            NodeRef::Single(s) => types.push(s.clone()),
            NodeRef::Any(set) => types.extend(set.iter().cloned()),
            NodeRef::All(_) => {} // fan-in handled separately
        }
    }
    types
}

/// Verify causal consistency of a message against its protocol (REQ-203, REQ-304).
///
/// Three-valued result: `Unknown` when a predecessor hash is not yet in the store,
/// `Valid` when all predecessors resolve and match the protocol, `Violation` when
/// a predecessor exists but has the wrong type or the causal link is malformed.
///
/// Thread-scoped: `:caused-by` hashes resolve only within the same `:thread` (ADR-008).
/// Stateless and monotone — re-evaluating after store growth can only move from
/// `Unknown` toward `Valid` or `Violation`, never backwards.
pub fn verify_causal<S: MessageStore>(
    msg_performative: &str,
    caused_by: Option<&CausedBy>,
    store: &S,
    protocol: &CausalProtocol,
    thread: &ThreadId,
) -> VerificationResult {
    // Look up the step declaration for this performative
    let step = match protocol.steps.get(msg_performative) {
        Some(s) => s,
        // Performative not declared in protocol — not constrained
        None => return VerificationResult::Valid,
    };

    let has_predecessors = !step.predecessors.is_empty();

    match caused_by {
        // No :caused-by provided
        None => {
            if has_predecessors {
                VerificationResult::Violation(CausalViolation::MissingCausedBy)
            } else {
                VerificationResult::Valid
            }
        }

        // :caused-by begin — root of a causal chain
        Some(CausedBy::Begin) => {
            // BEGIN_KEYWORD must appear in a Single or Any predecessor ref
            let begin_allowed = step.predecessors.iter().any(|nr| match nr {
                NodeRef::Single(s) => s == BEGIN_KEYWORD,
                NodeRef::Any(set) => set.contains(BEGIN_KEYWORD),
                NodeRef::All(_) => false, // begin in All doesn't apply to Begin caused-by
            });
            if begin_allowed {
                VerificationResult::Valid
            } else {
                let expected = allowed_single_predecessors(step);
                VerificationResult::Violation(CausalViolation::InvalidPredecessor {
                    caused_by: BEGIN_KEYWORD.into(),
                    expected,
                    found: BEGIN_KEYWORD.into(),
                })
            }
        }

        // :caused-by <hash> — single predecessor
        Some(CausedBy::Single(hash_str)) => {
            let content_hash = ContentHash(hash_str.clone());
            match predecessor_type(store, &content_hash, thread) {
                None => VerificationResult::Unknown,
                Some(pred_perf) => {
                    let allowed = allowed_single_predecessors(step);
                    if allowed.iter().any(|a| a == pred_perf) {
                        VerificationResult::Valid
                    } else if allowed.is_empty() && !has_predecessors {
                        VerificationResult::Violation(CausalViolation::ExtraneousPredecessor {
                            caused_by: hash_str.clone(),
                            found: pred_perf.into(),
                        })
                    } else {
                        VerificationResult::Violation(CausalViolation::InvalidPredecessor {
                            caused_by: hash_str.clone(),
                            expected: allowed,
                            found: pred_perf.into(),
                        })
                    }
                }
            }
        }

        // :caused-by (h1 h2 ...) — fan-in (multiple predecessors)
        Some(CausedBy::Multiple(hashes)) => {
            // Must have an (all ...) predecessor declaration
            let all_decl = step.predecessors.iter().find_map(|nr| {
                if let NodeRef::All(set) = nr {
                    Some(set)
                } else {
                    None
                }
            });

            let all_set = match all_decl {
                Some(s) => s,
                None => {
                    return VerificationResult::Violation(CausalViolation::FanInWithoutAllDecl {
                        performative: msg_performative.into(),
                    });
                }
            };

            let mut result = VerificationResult::Valid;
            let mut found_types = BTreeSet::new();

            for hash_str in hashes {
                let content_hash = ContentHash(hash_str.clone());
                match predecessor_type(store, &content_hash, thread) {
                    None => {
                        result = result.meet(VerificationResult::Unknown);
                    }
                    Some(pred_perf) => {
                        if all_set.contains(pred_perf) {
                            found_types.insert(String::from(pred_perf));
                        } else {
                            result = result.meet(VerificationResult::Violation(
                                CausalViolation::InvalidPredecessor {
                                    caused_by: hash_str.clone(),
                                    expected: all_set.iter().cloned().collect(),
                                    found: pred_perf.into(),
                                },
                            ));
                        }
                    }
                }
            }

            // Check completeness only when all lookups succeeded
            if matches!(result, VerificationResult::Valid) {
                let missing: Vec<String> = all_set
                    .iter()
                    .filter(|t| !found_types.contains(*t))
                    .cloned()
                    .collect();
                if !missing.is_empty() {
                    result = VerificationResult::Violation(CausalViolation::IncompleteFanIn {
                        missing_types: missing,
                    });
                }
            }

            result
        }
    }
}
