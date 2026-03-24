//! Violation blame attribution (REQ-230, REQ-232, REQ-233, CON-205).
//!
//! When a constraint violation is detected, a `ViolationError` captures who is
//! responsible (`BlameParty`), what went wrong, and a chain of evidence entries
//! (`BlameEntry`) that a third party can independently verify.
//!
//! `to_sexpr` produces a valid CBCL error message per REQ-233 grammar.
//! `verify_blame` allows third-party re-checking of the evidence chain.

#![forbid(unsafe_code)]

use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

use crate::protocol::CausalViolation;
use crate::sexpr::{Atom, SExpr};
use crate::shape::{ShapeConstraint, ShapeViolation};

// ================================================================
// Blame Party (CON-205)
// ================================================================

/// Who is responsible for a violation.
///
/// - `Sender` — the agent that sent a malformed or protocol-violating message.
/// - `DialectAuthor` — the dialect definition itself contains errors (e.g. R5).
/// - `Installer` — the agent that installed a faulty dialect.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum BlameParty {
    Sender,
    DialectAuthor,
    Installer,
}

impl BlameParty {
    /// Symbol name used in S-expression serialisation.
    pub fn as_str(&self) -> &'static str {
        match self {
            BlameParty::Sender => "sender",
            BlameParty::DialectAuthor => "dialect-author",
            BlameParty::Installer => "installer",
        }
    }
}

impl fmt::Display for BlameParty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

// ================================================================
// Violation Kind
// ================================================================

/// Classification of the underlying constraint that was violated.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ViolationKind {
    /// Shape constraint violation (REQ-223).
    Shape,
    /// Causal protocol violation (CON-202).
    Causal,
    /// R5 well-formedness violation (REQ-222).
    R5,
}

impl ViolationKind {
    /// Symbol name used in S-expression serialisation.
    pub fn as_str(&self) -> &'static str {
        match self {
            ViolationKind::Shape => "shape",
            ViolationKind::Causal => "causal",
            ViolationKind::R5 => "r5",
        }
    }
}

impl fmt::Display for ViolationKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

// ================================================================
// Blame Entry (CON-205)
// ================================================================

/// A single entry in the blame chain, attributing a piece of evidence to a party.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct BlameEntry {
    /// Who is responsible.
    pub party: BlameParty,
    /// Human-readable reason for blame.
    pub reason: String,
    /// Optional evidence S-expression (the violating data).
    pub evidence: Option<SExpr>,
}

impl BlameEntry {
    /// Serialise this entry as an S-expression.
    ///
    /// ```text
    /// (blame :party sender :reason "missing :caused-by" :evidence (...))
    /// ```
    pub fn to_sexpr(&self) -> SExpr {
        let mut items: Vec<SExpr> = Vec::new();
        items.push(SExpr::Atom(Atom::Symbol(String::from("blame"))));
        items.push(SExpr::Atom(Atom::Keyword(String::from("party"))));
        items.push(SExpr::Atom(Atom::Symbol(String::from(self.party.as_str()))));
        items.push(SExpr::Atom(Atom::Keyword(String::from("reason"))));
        items.push(SExpr::Atom(Atom::Str(self.reason.clone())));
        if let Some(ref ev) = self.evidence {
            items.push(SExpr::Atom(Atom::Keyword(String::from("evidence"))));
            items.push(ev.clone());
        }
        SExpr::List(items)
    }
}

// ================================================================
// Violation Error (REQ-230, REQ-232)
// ================================================================

/// A complete violation error with blame attribution.
///
/// Carries the violation kind, a human-readable detail, optional context
/// (message hash, thread), and a chain of blame entries that allow
/// third-party verification.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ViolationError {
    /// What kind of constraint was violated.
    pub kind: ViolationKind,
    /// Ordered chain of blame entries (CON-205).
    pub blame_chain: Vec<BlameEntry>,
    /// Content hash of the offending message, if applicable.
    pub message_hash: Option<String>,
    /// Thread in which the violation occurred.
    pub thread_id: Option<String>,
    /// Human-readable description of the violation.
    pub detail: String,
}

impl fmt::Display for ViolationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} violation: {}", self.kind, self.detail)
    }
}

// ----------------------------------------------------------------
// Constructors
// ----------------------------------------------------------------

impl ViolationError {
    /// Create a `ViolationError` from a `ShapeViolation` (REQ-230).
    ///
    /// Shape violations blame the **Sender** (who sent a message that does not
    /// conform to the declared shape) with the violating S-expression as evidence.
    pub fn from_shape_violation(
        violation: &ShapeViolation,
        message_hash: Option<String>,
        thread_id: Option<String>,
        evidence: Option<SExpr>,
    ) -> Self {
        let reason = alloc::format!(
            "shape rule '{}' violated: {}",
            violation.rule,
            violation.detail
        );
        ViolationError {
            kind: ViolationKind::Shape,
            blame_chain: alloc::vec![BlameEntry {
                party: BlameParty::Sender,
                reason,
                evidence,
            }],
            message_hash,
            thread_id,
            detail: alloc::format!("{}", violation),
        }
    }

    /// Create a `ViolationError` from a `CausalViolation` (REQ-230).
    ///
    /// Causal violations blame the **Sender** (who sent a message with invalid
    /// causal predecessors).
    pub fn from_causal_violation(
        violation: &CausalViolation,
        message_hash: Option<String>,
        thread_id: Option<String>,
    ) -> Self {
        let reason = alloc::format!("{}", violation);
        ViolationError {
            kind: ViolationKind::Causal,
            blame_chain: alloc::vec![BlameEntry {
                party: BlameParty::Sender,
                reason: reason.clone(),
                evidence: None,
            }],
            message_hash,
            thread_id,
            detail: reason,
        }
    }

    /// Create a `ViolationError` from R5 well-formedness violations (REQ-230).
    ///
    /// R5 violations blame the **DialectAuthor** (who wrote a dialect with
    /// malformed shapes or protocol) with an additional **Installer** entry
    /// (who installed it without catching the problem).
    pub fn from_r5_violation(
        dialect_name: &str,
        violations: &[String],
    ) -> Self {
        let detail = alloc::format!(
            "dialect '{}' has {} R5 violation(s): {}",
            dialect_name,
            violations.len(),
            violations.join("; ")
        );

        let author_reason = alloc::format!(
            "dialect '{}' contains well-formedness errors",
            dialect_name
        );
        let installer_reason = alloc::format!(
            "installed dialect '{}' without catching R5 violations",
            dialect_name
        );

        ViolationError {
            kind: ViolationKind::R5,
            blame_chain: alloc::vec![
                BlameEntry {
                    party: BlameParty::DialectAuthor,
                    reason: author_reason,
                    evidence: None,
                },
                BlameEntry {
                    party: BlameParty::Installer,
                    reason: installer_reason,
                    evidence: None,
                },
            ],
            message_hash: None,
            thread_id: None,
            detail,
        }
    }

    // ----------------------------------------------------------------
    // Serialisation (REQ-233)
    // ----------------------------------------------------------------

    /// Serialise as a valid CBCL error S-expression (REQ-233).
    ///
    /// ```text
    /// (error :kind shape
    ///        :detail "shape violation: ..."
    ///        :message-hash "abc123"
    ///        :thread "t1"
    ///        :blame-chain
    ///          ((blame :party sender :reason "..." :evidence (...))))
    /// ```
    pub fn to_sexpr(&self) -> SExpr {
        let mut items: Vec<SExpr> = Vec::new();
        items.push(SExpr::Atom(Atom::Symbol(String::from("error"))));

        // :kind
        items.push(SExpr::Atom(Atom::Keyword(String::from("kind"))));
        items.push(SExpr::Atom(Atom::Symbol(String::from(self.kind.as_str()))));

        // :detail
        items.push(SExpr::Atom(Atom::Keyword(String::from("detail"))));
        items.push(SExpr::Atom(Atom::Str(self.detail.clone())));

        // :message-hash (optional)
        if let Some(ref hash) = self.message_hash {
            items.push(SExpr::Atom(Atom::Keyword(String::from("message-hash"))));
            items.push(SExpr::Atom(Atom::Str(hash.clone())));
        }

        // :thread (optional)
        if let Some(ref thread) = self.thread_id {
            items.push(SExpr::Atom(Atom::Keyword(String::from("thread"))));
            items.push(SExpr::Atom(Atom::Str(thread.clone())));
        }

        // :blame-chain
        items.push(SExpr::Atom(Atom::Keyword(String::from("blame-chain"))));
        let chain: Vec<SExpr> = self.blame_chain.iter().map(|e| e.to_sexpr()).collect();
        items.push(SExpr::List(chain));

        SExpr::List(items)
    }

    // ----------------------------------------------------------------
    // Third-party verification (REQ-232)
    // ----------------------------------------------------------------

    /// Verify that a shape-blame claim is justified by re-checking the evidence
    /// against the given shape constraint.
    ///
    /// Returns `true` if the blame chain is verified: the evidence S-expression
    /// actually fails the shape constraint, confirming the violation is real.
    /// Returns `false` if the evidence passes (blame is unjustified) or if
    /// verification is not applicable (wrong kind, no evidence, no constraint).
    pub fn verify_blame(&self, shape_constraint: Option<&ShapeConstraint>) -> bool {
        match self.kind {
            ViolationKind::Shape => {
                self.verify_shape_blame(shape_constraint)
            }
            ViolationKind::Causal => {
                self.verify_causal_blame()
            }
            ViolationKind::R5 => {
                self.verify_r5_blame()
            }
        }
    }

    /// Re-check shape violation evidence against the constraint.
    fn verify_shape_blame(&self, shape_constraint: Option<&ShapeConstraint>) -> bool {
        let constraint = match shape_constraint {
            Some(c) => c,
            None => return false,
        };

        // At least one blame entry must have evidence that actually violates
        // the shape constraint.
        for entry in &self.blame_chain {
            if let Some(ref evidence) = entry.evidence {
                if constraint.check(evidence).is_err() {
                    return true;
                }
            }
        }
        false
    }

    /// Verify causal blame: the chain must have at least one Sender entry.
    fn verify_causal_blame(&self) -> bool {
        self.blame_chain
            .iter()
            .any(|e| e.party == BlameParty::Sender)
    }

    /// Verify R5 blame: the chain must have a DialectAuthor entry.
    fn verify_r5_blame(&self) -> bool {
        self.blame_chain
            .iter()
            .any(|e| e.party == BlameParty::DialectAuthor)
    }

    // ----------------------------------------------------------------
    // Observability (REQ-234)
    // ----------------------------------------------------------------

    /// Emit tracing events for blame attribution metrics.
    ///
    /// Emits two events when the `tracing` feature is enabled:
    /// - `cbcl_blame_attribution_count` — one event per blame-chain entry,
    ///   with labels `{dialect, blamed_party, violation_type}`.
    /// - `cbcl_violation_error_size_bytes` — the serialised S-expression
    ///   byte length of this error.
    ///
    /// This is a no-op when the `tracing` feature is disabled.
    #[allow(unused_variables)]
    pub fn record_metrics(&self, dialect: &str) {
        #[cfg(feature = "tracing")]
        {
            // Counter: one event per blame-chain entry.
            for entry in &self.blame_chain {
                tracing::event!(
                    tracing::Level::INFO,
                    dialect = dialect,
                    blamed_party = entry.party.as_str(),
                    violation_type = self.kind.as_str(),
                    "cbcl_blame_attribution_count"
                );
            }

            // Histogram: serialised error size in bytes.
            let sexpr = self.to_sexpr();
            let size = alloc::format!("{}", sexpr).len();
            tracing::event!(
                tracing::Level::INFO,
                size_bytes = size,
                violation_type = self.kind.as_str(),
                dialect = dialect,
                "cbcl_violation_error_size_bytes"
            );
        }
    }
}

// ================================================================
// Tests
// ================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::string::ToString;
    use alloc::vec;

    fn sym(s: &str) -> SExpr {
        SExpr::Atom(Atom::Symbol(String::from(s)))
    }

    fn kw(s: &str) -> SExpr {
        SExpr::Atom(Atom::Keyword(String::from(s)))
    }

    fn str_expr(s: &str) -> SExpr {
        SExpr::Atom(Atom::Str(String::from(s)))
    }

    fn num(n: i64) -> SExpr {
        SExpr::Atom(Atom::Num(n))
    }

    fn list(items: Vec<SExpr>) -> SExpr {
        SExpr::List(items)
    }

    // -- BlameParty --

    #[test]
    fn blame_party_as_str() {
        assert_eq!(BlameParty::Sender.as_str(), "sender");
        assert_eq!(BlameParty::DialectAuthor.as_str(), "dialect-author");
        assert_eq!(BlameParty::Installer.as_str(), "installer");
    }

    #[test]
    fn blame_party_display() {
        assert_eq!(BlameParty::Sender.to_string(), "sender");
        assert_eq!(BlameParty::DialectAuthor.to_string(), "dialect-author");
        assert_eq!(BlameParty::Installer.to_string(), "installer");
    }

    // -- ViolationKind --

    #[test]
    fn violation_kind_as_str() {
        assert_eq!(ViolationKind::Shape.as_str(), "shape");
        assert_eq!(ViolationKind::Causal.as_str(), "causal");
        assert_eq!(ViolationKind::R5.as_str(), "r5");
    }

    #[test]
    fn violation_kind_display() {
        assert_eq!(ViolationKind::Shape.to_string(), "shape");
        assert_eq!(ViolationKind::Causal.to_string(), "causal");
        assert_eq!(ViolationKind::R5.to_string(), "r5");
    }

    // -- BlameEntry::to_sexpr --

    #[test]
    fn blame_entry_to_sexpr_with_evidence() {
        let entry = BlameEntry {
            party: BlameParty::Sender,
            reason: String::from("missing :target"),
            evidence: Some(list(vec![sym("track"), kw("route"), str_expr("A")])),
        };
        let sexpr = entry.to_sexpr();
        let s = alloc::format!("{}", sexpr);
        assert!(s.contains("blame"));
        assert!(s.contains(":party"));
        assert!(s.contains("sender"));
        assert!(s.contains(":reason"));
        assert!(s.contains("missing :target"));
        assert!(s.contains(":evidence"));
    }

    #[test]
    fn blame_entry_to_sexpr_without_evidence() {
        let entry = BlameEntry {
            party: BlameParty::DialectAuthor,
            reason: String::from("bad shape"),
            evidence: None,
        };
        let sexpr = entry.to_sexpr();
        let s = alloc::format!("{}", sexpr);
        assert!(s.contains("dialect-author"));
        assert!(!s.contains(":evidence"));
    }

    // -- from_shape_violation --

    #[test]
    fn from_shape_violation_blames_sender() {
        let sv = ShapeViolation {
            rule: String::from("require :target string"),
            field: Some(String::from(":target")),
            expected: Some(String::from("string")),
            found: Some(String::from("number")),
            detail: String::from("parameter :target expected type string, found number"),
        };
        let evidence = list(vec![sym("propose"), kw("target"), num(42)]);
        let err = ViolationError::from_shape_violation(
            &sv,
            Some(String::from("abc123")),
            Some(String::from("t1")),
            Some(evidence),
        );

        assert_eq!(err.kind, ViolationKind::Shape);
        assert_eq!(err.message_hash, Some(String::from("abc123")));
        assert_eq!(err.thread_id, Some(String::from("t1")));
        assert_eq!(err.blame_chain.len(), 1);
        assert_eq!(err.blame_chain[0].party, BlameParty::Sender);
        assert!(err.blame_chain[0].evidence.is_some());
        assert!(err.detail.contains("shape violation"));
    }

    // -- from_causal_violation --

    #[test]
    fn from_causal_violation_blames_sender() {
        let cv = CausalViolation::MissingCausedBy;
        let err = ViolationError::from_causal_violation(
            &cv,
            Some(String::from("def456")),
            Some(String::from("t2")),
        );

        assert_eq!(err.kind, ViolationKind::Causal);
        assert_eq!(err.blame_chain.len(), 1);
        assert_eq!(err.blame_chain[0].party, BlameParty::Sender);
        assert!(err.detail.contains("caused-by"));
    }

    #[test]
    fn from_causal_violation_unknown_predecessor() {
        let cv = CausalViolation::UnknownPredecessor {
            caused_by: String::from("hash999"),
        };
        let err = ViolationError::from_causal_violation(&cv, None, None);

        assert_eq!(err.kind, ViolationKind::Causal);
        assert!(err.detail.contains("hash999"));
    }

    #[test]
    fn from_causal_violation_invalid_predecessor() {
        let cv = CausalViolation::InvalidPredecessor {
            caused_by: String::from("hash111"),
            expected: alloc::vec![String::from("ask"), String::from("tell")],
            found: String::from("reply"),
        };
        let err = ViolationError::from_causal_violation(&cv, None, None);

        assert!(err.detail.contains("hash111"));
        assert!(err.detail.contains("reply"));
    }

    // -- from_r5_violation --

    #[test]
    fn from_r5_violation_blames_author_and_installer() {
        let violations = alloc::vec![
            String::from("shape targets unknown performative 'foo'"),
            String::from("cycle detected: a → b → a"),
        ];
        let err = ViolationError::from_r5_violation("bad-dialect", &violations);

        assert_eq!(err.kind, ViolationKind::R5);
        assert_eq!(err.blame_chain.len(), 2);
        assert_eq!(err.blame_chain[0].party, BlameParty::DialectAuthor);
        assert_eq!(err.blame_chain[1].party, BlameParty::Installer);
        assert!(err.detail.contains("bad-dialect"));
        assert!(err.detail.contains("2 R5 violation(s)"));
    }

    // -- to_sexpr (REQ-233) --

    #[test]
    fn to_sexpr_shape_violation() {
        let sv = ShapeViolation {
            rule: String::from("require :pkg string"),
            field: Some(String::from(":pkg")),
            expected: Some(String::from("string")),
            found: Some(String::from("number")),
            detail: String::from(":pkg expected string, found number"),
        };
        let err = ViolationError::from_shape_violation(
            &sv,
            Some(String::from("h1")),
            Some(String::from("t1")),
            Some(num(42)),
        );
        let sexpr = err.to_sexpr();
        let s = alloc::format!("{}", sexpr);

        // Must start with (error ...)
        assert!(s.starts_with("(error "));
        assert!(s.contains(":kind"));
        assert!(s.contains("shape"));
        assert!(s.contains(":detail"));
        assert!(s.contains(":message-hash"));
        assert!(s.contains("\"h1\""));
        assert!(s.contains(":thread"));
        assert!(s.contains("\"t1\""));
        assert!(s.contains(":blame-chain"));
        assert!(s.contains("(blame "));
    }

    #[test]
    fn to_sexpr_without_optional_fields() {
        let cv = CausalViolation::MissingCausedBy;
        let err = ViolationError::from_causal_violation(&cv, None, None);
        let sexpr = err.to_sexpr();
        let s = alloc::format!("{}", sexpr);

        assert!(s.starts_with("(error "));
        assert!(s.contains(":kind"));
        assert!(s.contains("causal"));
        assert!(!s.contains(":message-hash"));
        assert!(!s.contains(":thread"));
    }

    #[test]
    fn to_sexpr_r5_violation() {
        let err = ViolationError::from_r5_violation(
            "test-d",
            &[String::from("cycle found")],
        );
        let sexpr = err.to_sexpr();
        let s = alloc::format!("{}", sexpr);

        assert!(s.starts_with("(error "));
        assert!(s.contains("r5"));
        assert!(s.contains(":blame-chain"));
        // Two blame entries: dialect-author and installer
        let blame_count = s.matches("(blame ").count();
        assert_eq!(blame_count, 2);
    }

    // -- ViolationError::display --

    #[test]
    fn violation_error_display() {
        let cv = CausalViolation::MissingCausedBy;
        let err = ViolationError::from_causal_violation(&cv, None, None);
        let s = err.to_string();
        assert!(s.contains("causal violation"));
    }

    // -- verify_blame --

    #[test]
    fn verify_blame_shape_with_valid_evidence() {
        use crate::shape::{ShapeConstraint, ShapeRule, TypeConstraint};

        let constraint = ShapeConstraint {
            performative: String::from("track"),
            rules: vec![ShapeRule::Require {
                keyword: String::from("package"),
                type_constraint: Some(TypeConstraint::String),
                children: vec![],
            }],
        };

        // Evidence that actually violates the constraint (wrong type)
        let evidence = list(vec![sym("track"), kw("package"), num(42)]);
        let sv = ShapeViolation {
            rule: String::from("require :package string"),
            field: Some(String::from(":package")),
            expected: Some(String::from("string")),
            found: Some(String::from("number")),
            detail: String::from(":package expected string, found number"),
        };
        let err = ViolationError::from_shape_violation(&sv, None, None, Some(evidence));

        assert!(err.verify_blame(Some(&constraint)));
    }

    #[test]
    fn verify_blame_shape_with_passing_evidence_returns_false() {
        use crate::shape::{ShapeConstraint, ShapeRule, TypeConstraint};

        let constraint = ShapeConstraint {
            performative: String::from("track"),
            rules: vec![ShapeRule::Require {
                keyword: String::from("package"),
                type_constraint: Some(TypeConstraint::String),
                children: vec![],
            }],
        };

        // Evidence that actually passes (correct type) — blame is unjustified
        let evidence = list(vec![sym("track"), kw("package"), str_expr("box-1")]);
        let sv = ShapeViolation {
            rule: String::from("require :package string"),
            field: Some(String::from(":package")),
            expected: Some(String::from("string")),
            found: Some(String::from("number")),
            detail: String::from("fabricated violation"),
        };
        let err = ViolationError::from_shape_violation(&sv, None, None, Some(evidence));

        assert!(!err.verify_blame(Some(&constraint)));
    }

    #[test]
    fn verify_blame_shape_without_constraint_returns_false() {
        let sv = ShapeViolation {
            rule: String::from("require :x"),
            field: None,
            expected: None,
            found: None,
            detail: String::from("missing"),
        };
        let err = ViolationError::from_shape_violation(&sv, None, None, Some(sym("x")));
        assert!(!err.verify_blame(None));
    }

    #[test]
    fn verify_blame_shape_without_evidence_returns_false() {
        use crate::shape::{ShapeConstraint, ShapeRule, TypeConstraint};

        let constraint = ShapeConstraint {
            performative: String::from("track"),
            rules: vec![ShapeRule::Require {
                keyword: String::from("package"),
                type_constraint: Some(TypeConstraint::String),
                children: vec![],
            }],
        };

        let sv = ShapeViolation {
            rule: String::from("require :package string"),
            field: None,
            expected: None,
            found: None,
            detail: String::from("missing"),
        };
        let err = ViolationError::from_shape_violation(&sv, None, None, None);
        assert!(!err.verify_blame(Some(&constraint)));
    }

    #[test]
    fn verify_blame_causal() {
        let cv = CausalViolation::MissingCausedBy;
        let err = ViolationError::from_causal_violation(&cv, None, None);
        assert!(err.verify_blame(None));
    }

    #[test]
    fn verify_blame_r5() {
        let err = ViolationError::from_r5_violation("d", &[String::from("bad")]);
        assert!(err.verify_blame(None));
    }

    #[test]
    fn verify_blame_r5_without_author_returns_false() {
        // Manually constructed with only Installer — should fail verification
        let err = ViolationError {
            kind: ViolationKind::R5,
            blame_chain: vec![BlameEntry {
                party: BlameParty::Installer,
                reason: String::from("installed bad dialect"),
                evidence: None,
            }],
            message_hash: None,
            thread_id: None,
            detail: String::from("test"),
        };
        assert!(!err.verify_blame(None));
    }

    #[test]
    fn verify_blame_causal_without_sender_returns_false() {
        // Manually constructed with wrong party — should fail verification
        let err = ViolationError {
            kind: ViolationKind::Causal,
            blame_chain: vec![BlameEntry {
                party: BlameParty::DialectAuthor,
                reason: String::from("wrong party"),
                evidence: None,
            }],
            message_hash: None,
            thread_id: None,
            detail: String::from("test"),
        };
        assert!(!err.verify_blame(None));
    }

    // -- Equality and Clone --

    #[test]
    fn blame_party_copy_and_eq() {
        let a = BlameParty::Sender;
        let b = a; // Copy
        assert_eq!(a, b);
    }

    #[test]
    fn violation_error_clone_and_eq() {
        let err = ViolationError::from_r5_violation("d", &[String::from("x")]);
        let err2 = err.clone();
        assert_eq!(err, err2);
    }

    // -- record_metrics (REQ-234) --

    #[test]
    fn record_metrics_does_not_panic_shape() {
        let sv = ShapeViolation {
            rule: String::from("require :x string"),
            field: Some(String::from(":x")),
            expected: Some(String::from("string")),
            found: Some(String::from("number")),
            detail: String::from(":x expected string, found number"),
        };
        let err = ViolationError::from_shape_violation(
            &sv,
            Some(String::from("h1")),
            Some(String::from("t1")),
            Some(num(42)),
        );
        // Should not panic regardless of tracing feature state.
        err.record_metrics("test-dialect");
    }

    #[test]
    fn record_metrics_does_not_panic_causal() {
        let cv = CausalViolation::MissingCausedBy;
        let err = ViolationError::from_causal_violation(&cv, None, None);
        err.record_metrics("test-dialect");
    }

    #[test]
    fn record_metrics_does_not_panic_r5() {
        let err = ViolationError::from_r5_violation(
            "bad-d",
            &[String::from("cycle")],
        );
        // R5 has two blame-chain entries; both should be emitted.
        err.record_metrics("bad-d");
    }
}
