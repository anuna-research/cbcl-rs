//! NIFs for the SPEC-019 state layer (R.7): `fold/1`, `intend/1`,
//! `verify_state_shape/1`, `state_schema/1`, `may_send/1`, `frontier/1`,
//! `dialect_hash/1`, `admit/1`.
//!
//! Each takes one `binary()` holding the export's S-expression frame (see
//! `cbcl_parser::state_exports`) and returns `{ok, Result :: binary()} |
//! {error, Reason :: binary()}`. Results are the shared implementation's
//! bytes verbatim: JSON for `fold`, `state_schema`, `may_send`, `frontier`;
//! the canonical act text for `intend`; `<<"ok">>` for `verify_state_shape`;
//! `sha256-<hex>` for `dialect_hash`; `{"verdict":…}` JSON for `admit`. A rejected intent is `{error, JSON}`
//! with `{"reject": kind, "reason": text}`, and a state-shape violation is
//! `{error, BlameSExpr}`.
//!
//! Errors are binaries, never atoms, for the same reason as `verify_dialect/1`:
//! reasons are free-form and atoms would leak into the global atom table.
//! Every entry point runs under `panic_guard::catch` (SPEC-009 REQ-005).

use cbcl_parser::state_exports;
use rustler::types::atom;
use rustler::{Binary, Encoder, Env, OwnedBinary, Term};

use crate::tracing_hooks;

fn make_binary<'a>(env: Env<'a>, s: String) -> Binary<'a> {
    match OwnedBinary::new(s.len()) {
        Some(mut owned) => {
            owned.as_mut_slice().copy_from_slice(s.as_bytes());
            Binary::from_owned(owned, env)
        }
        None => {
            let mut owned = OwnedBinary::new(3).expect("3-byte allocation");
            owned.as_mut_slice().copy_from_slice(b"oom");
            Binary::from_owned(owned, env)
        }
    }
}

fn utf8(bytes: &[u8]) -> Result<&str, String> {
    core::str::from_utf8(bytes).map_err(|_| String::from("invalid utf-8"))
}

/// Env-free core of `fold/1`.
pub fn fold_pure(bytes: &[u8]) -> Result<String, String> {
    state_exports::fold_str(utf8(bytes)?)
}
/// Env-free core of `intend/1`.
pub fn intend_pure(bytes: &[u8]) -> Result<String, String> {
    state_exports::intend_str(utf8(bytes)?)
}
/// Env-free core of `verify_state_shape/1`.
pub fn verify_state_shape_pure(bytes: &[u8]) -> Result<String, String> {
    state_exports::verify_state_shape_str(utf8(bytes)?)
}
/// Env-free core of `state_schema/1`.
pub fn state_schema_pure(bytes: &[u8]) -> Result<String, String> {
    state_exports::state_schema_str(utf8(bytes)?)
}
/// Env-free core of `may_send/1`.
pub fn may_send_pure(bytes: &[u8]) -> Result<String, String> {
    state_exports::may_send_str(utf8(bytes)?)
}
/// Env-free core of `frontier/1`.
pub fn frontier_pure(bytes: &[u8]) -> Result<String, String> {
    state_exports::frontier_str(utf8(bytes)?)
}
/// Env-free core of `dialect_hash/1`.
pub fn dialect_hash_pure(bytes: &[u8]) -> Result<String, String> {
    state_exports::dialect_hash_str(utf8(bytes)?)
}
/// Env-free core of `admit/1`.
pub fn admit_pure(bytes: &[u8]) -> Result<String, String> {
    state_exports::admit_str(utf8(bytes)?)
}
/// Env-free core of `read/1`: the parser's tree as JSON.
pub fn read_pure(bytes: &[u8]) -> Result<String, String> {
    cbcl_parser::read_str(utf8(bytes)?)
}
/// Env-free core of `compile_contract/1` (SPEC-087): a JSON contract →
/// `{"name","label","dialect"}` JSON, or the recognition or R1–R7 reason.
pub fn compile_contract_pure(bytes: &[u8]) -> Result<String, String> {
    cbcl_parser::compile_contract_str(utf8(bytes)?)
}
/// Env-free core of `define_text/1`: the canonical `(define …)` a frame carries.
pub fn define_text_pure(bytes: &[u8]) -> Result<String, String> {
    cbcl_parser::define_text_str(utf8(bytes)?)
}
/// Env-free core of `describe_dialect/1`: a dialect's description as JSON.
pub fn describe_dialect_pure(bytes: &[u8]) -> Result<String, String> {
    cbcl_parser::describe_dialect_str(utf8(bytes)?)
}
/// Env-free core of `read_act/1`: an act's routing and fields as JSON.
pub fn read_act_pure(bytes: &[u8]) -> Result<String, String> {
    cbcl_parser::read_act_str(utf8(bytes)?)
}
/// Env-free core of `verify_message_shape/1` (SPEC-009 CON-002; cbcl-rs #14):
/// `(verify-shape <dialect> <performative> <message>)` → `"ok"`, or `Err`
/// with the REQ-233 blame S-expression, the same verdict the browser's wasm
/// gives, so a hub never re-encodes a shape grammar in its own language.
pub fn verify_message_shape_pure(bytes: &[u8]) -> Result<String, String> {
    cbcl_parser::verify_message_shape_str(utf8(bytes)?)
}

/// Encode a pure result as `{ok, Bin} | {error, Bin}` under the panic guard.
#[allow(clippy::let_unit_value)]
fn run<'a>(
    env: Env<'a>,
    name: &'static str,
    input: &[u8],
    f: fn(&[u8]) -> Result<String, String>,
) -> Term<'a> {
    crate::panic_guard::catch(env, || {
        let span = tracing_hooks::enter(name, input.len());
        match f(input) {
            Ok(s) => {
                tracing_hooks::exit_ok(span);
                (atom::ok(), make_binary(env, s)).encode(env)
            }
            Err(msg) => {
                let cat: &'static str = if msg == "invalid utf-8" {
                    "invalid_utf8"
                } else if msg.starts_with("parse error") || msg.starts_with("expected (") {
                    "frame_error"
                } else if msg.starts_with("dialect") || msg.starts_with("contract:") {
                    "dialect_error"
                } else if msg.starts_with("{\"reject\"") {
                    "intent_rejected"
                } else {
                    "violation"
                };
                tracing_hooks::exit_err(span, cat);
                (atom::error(), make_binary(env, msg)).encode(env)
            }
        }
    })
}

#[rustler::nif]
pub fn fold<'a>(env: Env<'a>, bytes: Binary<'a>) -> Term<'a> {
    run(env, "fold", bytes.as_slice(), fold_pure)
}

#[rustler::nif]
pub fn intend<'a>(env: Env<'a>, bytes: Binary<'a>) -> Term<'a> {
    run(env, "intend", bytes.as_slice(), intend_pure)
}

#[rustler::nif]
pub fn verify_state_shape<'a>(env: Env<'a>, bytes: Binary<'a>) -> Term<'a> {
    run(
        env,
        "verify_state_shape",
        bytes.as_slice(),
        verify_state_shape_pure,
    )
}

#[rustler::nif]
pub fn state_schema<'a>(env: Env<'a>, bytes: Binary<'a>) -> Term<'a> {
    run(env, "state_schema", bytes.as_slice(), state_schema_pure)
}

#[rustler::nif]
pub fn may_send<'a>(env: Env<'a>, bytes: Binary<'a>) -> Term<'a> {
    run(env, "may_send", bytes.as_slice(), may_send_pure)
}

#[rustler::nif]
pub fn frontier<'a>(env: Env<'a>, bytes: Binary<'a>) -> Term<'a> {
    run(env, "frontier", bytes.as_slice(), frontier_pure)
}

#[rustler::nif]
pub fn dialect_hash<'a>(env: Env<'a>, bytes: Binary<'a>) -> Term<'a> {
    run(env, "dialect_hash", bytes.as_slice(), dialect_hash_pure)
}

#[rustler::nif]
pub fn admit<'a>(env: Env<'a>, bytes: Binary<'a>) -> Term<'a> {
    run(env, "admit", bytes.as_slice(), admit_pure)
}

#[rustler::nif]
pub fn read<'a>(env: Env<'a>, bytes: Binary<'a>) -> Term<'a> {
    run(env, "read", bytes.as_slice(), read_pure)
}

#[rustler::nif]
pub fn define_text<'a>(env: Env<'a>, bytes: Binary<'a>) -> Term<'a> {
    run(env, "define_text", bytes.as_slice(), define_text_pure)
}

#[rustler::nif]
pub fn describe_dialect<'a>(env: Env<'a>, bytes: Binary<'a>) -> Term<'a> {
    run(env, "describe_dialect", bytes.as_slice(), describe_dialect_pure)
}

#[rustler::nif]
pub fn read_act<'a>(env: Env<'a>, bytes: Binary<'a>) -> Term<'a> {
    run(env, "read_act", bytes.as_slice(), read_act_pure)
}

#[rustler::nif]
pub fn compile_contract<'a>(env: Env<'a>, bytes: Binary<'a>) -> Term<'a> {
    run(env, "compile_contract", bytes.as_slice(), compile_contract_pure)
}

#[rustler::nif]
pub fn verify_message_shape<'a>(env: Env<'a>, bytes: Binary<'a>) -> Term<'a> {
    run(env, "verify_message_shape", bytes.as_slice(), verify_message_shape_pure)
}

#[cfg(test)]
mod tests {
    //! Tests target the env-free `*_pure` helpers (see `verify_dialect.rs`
    //! for why the term-bound wrappers cannot run under `cargo test`).
    use super::*;

    const LUNCH: &str = "(define lunch-vote (cbcl) @anuna \
      (:resource-requirements ((max-depth 12) (max-expansion-size 2048) (verification-time 200))) \
      (extend propose (to question options) (tell to :question question :options options)) \
      (extend vote (to choice) (tell to :choice choice)) \
      (shape propose (require :question string) (require :options list)) \
      (shape vote (require :choice string)) \
      (protocol (then begin propose) (then propose vote)) \
      (state (question (last propose :question)) (options (last propose :options)) \
             (domain vote :choice options) (ballots (latest-per-signer vote :choice)) \
             (tally (histogram ballots))))";

    #[test]
    fn schema_and_hash() {
        let schema = state_schema_pure(format!("(state-schema {LUNCH})").as_bytes()).unwrap();
        assert!(
            schema.starts_with("{\"question\":{\"type\":\"opt-scalar\""),
            "{schema}"
        );
        let name = dialect_hash_pure(LUNCH.as_bytes()).unwrap();
        assert!(
            name.starts_with("sha256-") && name.len() == 7 + 64,
            "{name}"
        );
    }

    #[test]
    fn fold_and_intend_agree_with_the_core() {
        let opener = "(lang lunch-vote (propose @lunch :question \"Lunch?\" :options (\"Pizza\" \"Sushi\") :caused-by begin :thread \"v1\" :from @aria))";
        let acts = format!("(acts (@aria {opener}))");
        let state = fold_pure(format!("(fold {LUNCH} \"v1\" {acts})").as_bytes()).unwrap();
        assert_eq!(state, "{\"question\":\"Lunch?\",\"options\":[\"Pizza\",\"Sushi\"],\"ballots\":{},\"tally\":{}}");
        let ok = intend_pure(
            format!("(intend {LUNCH} \"v1\" {acts} @bo vote (:choice \"Sushi\"))").as_bytes(),
        )
        .unwrap();
        assert!(ok.starts_with("(lang lunch-vote (vote @lunch"), "{ok}");
        let rejected = intend_pure(
            format!("(intend {LUNCH} \"v1\" {acts} @bo vote (:choice \"Tacos\"))").as_bytes(),
        )
        .unwrap_err();
        assert!(rejected.starts_with("{\"reject\":\"domain\""), "{rejected}");
        let verbs =
            may_send_pure(format!("(may-send {LUNCH} \"v1\" {acts} @bo)").as_bytes()).unwrap();
        assert_eq!(verbs, "[\"vote\"]");
        let fr = frontier_pure(format!("(frontier {LUNCH} \"v1\" {acts})").as_bytes()).unwrap();
        assert!(fr.starts_with("{\"instance\":\"sha256-"), "{fr}");
        let root = fr.split('"').nth(3).unwrap().to_string();
        let vote = format!("(lang lunch-vote (vote @lunch :choice \"Sushi\" :caused-by {root} :thread \"v1\" :from @bo))");
        let admitted = admit_pure(format!("(admit {LUNCH} \"v1\" {acts} (@bo {vote}))").as_bytes()).unwrap();
        assert_eq!(admitted, "{\"verdict\":\"accepted\"}");
        let orphan = "(lang lunch-vote (vote @lunch :choice \"Sushi\" :caused-by sha256-ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff :thread \"v1\" :from @bo))";
        let pending = admit_pure(format!("(admit {LUNCH} \"v1\" {acts} (@bo {orphan}))").as_bytes()).unwrap();
        assert_eq!(pending, "{\"verdict\":\"pending\"}");
        assert_eq!(
            verify_message_shape_pure(format!("(verify-shape {LUNCH} vote (vote @lunch :choice \"Sushi\"))").as_bytes()).unwrap(),
            "ok"
        );
        let blame = verify_message_shape_pure(format!("(verify-shape {LUNCH} vote (vote @lunch :choice 3))").as_bytes()).unwrap_err();
        assert!(blame.contains("choice"), "{blame}");
    }

    #[test]
    fn errors_are_reasons_not_panics() {
        assert_eq!(fold_pure(&[0xFF, 0xFE]).unwrap_err(), "invalid utf-8");
        assert!(fold_pure(b"(fold").unwrap_err().starts_with("parse error"));
        assert!(fold_pure(b"(nope x)")
            .unwrap_err()
            .starts_with("expected (fold"));
        let bad = format!("(verify-state-shape {LUNCH} (lang lunch-vote (vote @lunch :choice \"x\" :extra 1 :caused-by begin :thread \"v1\" :from @bo)))");
        assert!(verify_state_shape_pure(bad.as_bytes())
            .unwrap_err()
            .contains("closed"));
    }
}
