//! Candidate vocabulary entries: attestation header reconstruction and label
//! binding (SPEC-035 REQ-3504, CON-3504, ADR-3504).
use cbcl_core::{
    attest::verify_attestation_v2,
    equivocation::attestation_header_for,
    keyid::KeyId,
    message::Message,
    r4::Signer,
    serializer::serialize,
    sexpr::{Atom, SExpr},
};

/// One member of the public candidate vocabulary: a `lang`-wrapped simple
/// message and the signer label it is admitted under.
///
/// Fields are private. The only constructors are [`Candidate::attested`],
/// which verifies an R4 v2 attestation, and [`Candidate::unauthenticated`],
/// which trusts the host (REQ-3504 a). Both paths yield the same profile
/// identity for the same text and label (REQ-3504 e).
///
/// ```compile_fail
/// let _ = cbcl_state_proof::Candidate {
///     text: String::new(),
///     label: String::new(),
/// };
/// ```
#[derive(Clone, Debug)]
pub struct Candidate {
    text: String,
    label: String,
}

impl Candidate {
    /// Host precondition: `label` is the authenticated sender of `text`. The
    /// library does not authenticate the label; a wrong label here is a wrong
    /// profile, not an error.
    pub fn unauthenticated(text: String, label: String) -> Candidate {
        Candidate { text, label }
    }

    /// Authenticate `message` through its R4 v2 attestation and bind its
    /// `:from` text as the label.
    ///
    /// Rebuilds the header of the innermost simple message with
    /// `attestation_header_for` and verifies `signature` over it under the
    /// header's sender. Rejects: no simple message; a missing `:sender` or
    /// `:thread`; a signature that does not verify; a `:from` count other
    /// than one; a `:from` whose `KeyId` differs from the header's sender.
    ///
    /// Host precondition the library cannot check: `signer` verifies for the
    /// key `header.from` names. The `lang` wrapper is not signed; the profile
    /// binds it to the installed dialect (REQ-3512 b).
    pub fn attested(
        message: &Message,
        signature: &[u8],
        signer: &dyn Signer,
    ) -> Result<Candidate, String> {
        let simple = message
            .innermost_simple()
            .ok_or("candidate has no simple message")?;
        let header = attestation_header_for(simple).map_err(|e| e.to_string())?;
        verify_attestation_v2(signer, &header.from, &header, signature)
            .map_err(|e| e.to_string())?;
        let from = from_field(simple).ok_or("candidate must carry exactly one :from")?;
        if KeyId::parse(from).map_err(|e| e.to_string())? != header.from {
            return Err("candidate :from names a different key than its :sender".into());
        }
        Ok(Candidate {
            text: serialize(&SExpr::from(message)),
            label: from.into(),
        })
    }

    /// The candidate's CBCL message text.
    pub fn text(&self) -> &str {
        &self.text
    }
    /// The signer label the candidate is admitted under.
    pub fn label(&self) -> &str {
        &self.label
    }
}

/// The single `:from` field of a simple message, as a string or symbol.
/// `None` when absent, repeated, or of another atom type. Scans as
/// `cbcl_core::state::keyword_fields` does: a keyword consumes the next
/// param, anything else is skipped, so a stray positional param cannot hide
/// a second `:from`.
pub(crate) fn from_field(simple: &Message) -> Option<&str> {
    let Message::Simple { params, .. } = simple else {
        return None;
    };
    let mut from = None;
    let mut i = 0;
    while i + 1 < params.len() {
        if let SExpr::Atom(Atom::Keyword(k)) = &params[i] {
            if k == "from" {
                if from.is_some() {
                    return None;
                }
                from = Some(&params[i + 1]);
            }
            i += 2;
        } else {
            i += 1;
        }
    }
    match from? {
        SExpr::Atom(Atom::Str(s) | Atom::Symbol(s)) => Some(s.as_str()),
        _ => None,
    }
}
