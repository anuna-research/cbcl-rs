//! Bundled native checkpoint coordination dialect (SPEC-035 CON-3504).
//! Installation proves native well-formedness, never checkpoint truth. Exact
//! payload recognition and independently pinned policy checks belong to the
//! certificate verifier; the source label is not an authority identifier.

use alloc::format;
use alloc::string::String;
use cbcl_core::canonical::dialect_name;
use cbcl_core::dialect::Dialect;
use cbcl_core::sexpr::{Atom, SExpr};

/// Native definition bundled with this build; its human label is untrusted.
pub const SOURCE: &str = include_str!("../../../dialects/checkpoint.cbcl");

/// Compute the native self-address and install through the shared R1–R7 path.
/// The returned `hash` is the native code pin for certificate verification.
pub fn builtin() -> Result<Dialect, String> {
    let mut form = crate::parse(SOURCE).map_err(|e| format!("checkpoint parse: {e}"))?;
    let draft = crate::parse_dialect(&form).map_err(|e| format!("checkpoint dialect: {e}"))?;
    let name = dialect_name(&draft);
    if let SExpr::List(items) = &mut form {
        items[1] = SExpr::Atom(Atom::Symbol(name));
    }
    let registry = crate::parse_and_install_dialect(&form)?;
    registry
        .iter()
        .last()
        .cloned()
        .ok_or_else(|| String::from("checkpoint dialect was not installed"))
}
