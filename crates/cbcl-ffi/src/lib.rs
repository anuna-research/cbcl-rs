//! cbcl-ffi: C FFI bindings for CBCL.
//!
//! Provides a C-compatible API via cbindgen:
//! - `cbcl_parse_message` — parse S-expr string into a CBCL message
//! - `cbcl_verify_dialect` — parse and verify a dialect definition against R1/R2/R3
//! - `cbcl_agent_new` — create a new agent (opaque handle)
//! - `cbcl_agent_send` — construct a tell message, evaluate via agent
//! - `cbcl_agent_free` — free an agent handle
//! - `cbcl_string_free` — free a result string

use std::ffi::{CStr, CString};
use std::os::raw::c_char;
use std::ptr;

use cbcl_core::agent::Agent;
use cbcl_core::dialect::DialectRegistry;
use cbcl_core::evaluator;
use cbcl_core::message::{CorePerformative, Message, Performative};
use cbcl_core::serializer::serialize;
use cbcl_core::sexpr::{Atom, SExpr};
use cbcl_parser::parser;

// ---------------------------------------------------------------------------
// Result type
// ---------------------------------------------------------------------------

/// FFI result: contains either a success string or an error string.
///
/// The caller must free `data` with `cbcl_string_free` when done.
/// If `error` is 0, `data` is the success value.
/// If `error` is non-zero, `data` is the error message.
#[repr(C)]
pub struct CbclResult {
    /// Null-terminated UTF-8 string (must be freed with `cbcl_string_free`).
    /// NULL if allocation failed.
    pub data: *mut c_char,
    /// 0 on success, non-zero on error.
    pub error: i32,
}

impl CbclResult {
    fn ok(s: String) -> Self {
        CbclResult {
            data: string_to_c(s),
            error: 0,
        }
    }

    fn err(s: String) -> Self {
        CbclResult {
            data: string_to_c(s),
            error: 1,
        }
    }
}

// ---------------------------------------------------------------------------
// Opaque agent handle
// ---------------------------------------------------------------------------

/// Opaque handle to a CBCL agent. Created with `cbcl_agent_new`, freed with `cbcl_agent_free`.
pub struct CbclAgent {
    inner: Agent,
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn string_to_c(s: String) -> *mut c_char {
    match CString::new(s) {
        Ok(cs) => cs.into_raw(),
        Err(_) => ptr::null_mut(),
    }
}

/// # Safety
///
/// `s` must be a valid null-terminated C string.
unsafe fn c_to_str<'a>(s: *const c_char) -> Result<&'a str, CbclResult> {
    if s.is_null() {
        return Err(CbclResult::err("null pointer".into()));
    }
    // SAFETY: caller guarantees s is a valid null-terminated C string.
    unsafe { CStr::from_ptr(s) }
        .to_str()
        .map_err(|e| CbclResult::err(format!("invalid UTF-8: {e}")))
}

// ---------------------------------------------------------------------------
// Core string-level implementations (shared with tests)
// ---------------------------------------------------------------------------

fn parse_message_impl(input: &str) -> Result<String, String> {
    let sexpr = parser::parse(input).map_err(|e| format!("parse error: {e}"))?;
    let msg = cbcl_parser::parse_message(&sexpr).map_err(|e| format!("message error: {e}"))?;
    let msg_sexpr: SExpr = msg.into();
    Ok(serialize(&msg_sexpr))
}

fn verify_dialect_impl(input: &str) -> Result<String, String> {
    let sexpr = parser::parse(input).map_err(|e| format!("parse error: {e}"))?;
    let dialect =
        cbcl_parser::parse_dialect(&sexpr).map_err(|e| format!("dialect parse error: {e}"))?;

    let mut registry = DialectRegistry::new();
    registry
        .install(dialect)
        .map_err(|e| format!("verification failed: {e}"))?;

    Ok("ok".into())
}

fn send_message_impl(agent: &Agent, recipient: &str, content: &str) -> Result<String, String> {
    let content_expr =
        parser::parse(content).unwrap_or(SExpr::Atom(Atom::Str(content.to_string())));

    let recipient_sym = if recipient.starts_with('@') {
        recipient.to_string()
    } else {
        format!("@{recipient}")
    };

    let msg = Message::Simple {
        performative: Performative::Core(CorePerformative::Tell),
        recipient: Some(recipient_sym.into()),
        content: content_expr,
        params: Vec::new(),
        thread: None,
        sender: None,
        caused_by: None,
    };

    let result = evaluator::evaluate(&msg, agent.dialect_registry())
        .map_err(|e| format!("eval error: {e}"))?;

    Ok(serialize(&result.expanded))
}

// ---------------------------------------------------------------------------
// C FFI exports
// ---------------------------------------------------------------------------

/// Parse an S-expression string into a CBCL message.
///
/// Returns the canonical serialized form on success.
/// The caller must free the result with `cbcl_string_free`.
///
/// # Safety
///
/// `input` must be a valid null-terminated UTF-8 C string.
#[no_mangle]
pub unsafe extern "C" fn cbcl_parse_message(input: *const c_char) -> CbclResult {
    let input_str = match unsafe { c_to_str(input) } {
        Ok(s) => s,
        Err(r) => return r,
    };
    match parse_message_impl(input_str) {
        Ok(s) => CbclResult::ok(s),
        Err(e) => CbclResult::err(e),
    }
}

/// Parse and verify a dialect definition against R1/R2/R3 rules.
///
/// Returns "ok" on success or an error description.
/// The caller must free the result with `cbcl_string_free`.
///
/// # Safety
///
/// `input` must be a valid null-terminated UTF-8 C string.
#[no_mangle]
pub unsafe extern "C" fn cbcl_verify_dialect(input: *const c_char) -> CbclResult {
    let input_str = match unsafe { c_to_str(input) } {
        Ok(s) => s,
        Err(r) => return r,
    };
    match verify_dialect_impl(input_str) {
        Ok(s) => CbclResult::ok(s),
        Err(e) => CbclResult::err(e),
    }
}

/// Create a new CBCL agent with the given ID and base dialect installed.
///
/// Returns an opaque handle. The caller must free it with `cbcl_agent_free`.
/// Returns NULL on error (e.g. null or invalid UTF-8 id).
///
/// # Safety
///
/// `id` must be a valid null-terminated UTF-8 C string.
#[no_mangle]
pub unsafe extern "C" fn cbcl_agent_new(id: *const c_char) -> *mut CbclAgent {
    let id_str = match unsafe { c_to_str(id) } {
        Ok(s) => s,
        Err(_) => return ptr::null_mut(),
    };
    let agent = Agent::new(id_str);
    Box::into_raw(Box::new(CbclAgent { inner: agent }))
}

/// Send a tell message from the agent to a recipient.
///
/// Evaluates the message against the agent's dialect registry and returns the
/// expanded effect form. The caller must free the result with `cbcl_string_free`.
///
/// # Safety
///
/// - `agent` must be a valid pointer from `cbcl_agent_new`.
/// - `recipient` and `content` must be valid null-terminated UTF-8 C strings.
#[no_mangle]
pub unsafe extern "C" fn cbcl_agent_send(
    agent: *mut CbclAgent,
    recipient: *const c_char,
    content: *const c_char,
) -> CbclResult {
    if agent.is_null() {
        return CbclResult::err("null agent pointer".into());
    }
    let recipient_str = match unsafe { c_to_str(recipient) } {
        Ok(s) => s,
        Err(r) => return r,
    };
    let content_str = match unsafe { c_to_str(content) } {
        Ok(s) => s,
        Err(r) => return r,
    };
    // SAFETY: caller guarantees agent is a valid pointer from cbcl_agent_new.
    let agent_ref = unsafe { &*agent };
    match send_message_impl(&agent_ref.inner, recipient_str, content_str) {
        Ok(s) => CbclResult::ok(s),
        Err(e) => CbclResult::err(e),
    }
}

/// Free an agent handle created by `cbcl_agent_new`.
///
/// # Safety
///
/// `agent` must be a valid pointer from `cbcl_agent_new`, or NULL (which is a no-op).
/// After calling this function, the pointer must not be used again.
#[no_mangle]
pub unsafe extern "C" fn cbcl_agent_free(agent: *mut CbclAgent) {
    if !agent.is_null() {
        // SAFETY: caller guarantees agent was allocated by cbcl_agent_new.
        drop(unsafe { Box::from_raw(agent) });
    }
}

/// Free a string returned by any `cbcl_*` function.
///
/// # Safety
///
/// `s` must be a pointer returned by a `cbcl_*` function's `data` field,
/// or NULL (which is a no-op). After calling this function, the pointer
/// must not be used again.
#[no_mangle]
pub unsafe extern "C" fn cbcl_string_free(s: *mut c_char) {
    if !s.is_null() {
        // SAFETY: caller guarantees s was allocated by CString::into_raw.
        drop(unsafe { CString::from_raw(s) });
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::CString;

    fn cstr(s: &str) -> CString {
        CString::new(s).unwrap()
    }

    // -- parse_message --

    #[test]
    fn parse_message_tell() {
        let input = cstr("(tell \"hello\")");
        let result = unsafe { cbcl_parse_message(input.as_ptr()) };
        assert_eq!(result.error, 0);
        let data = unsafe { CStr::from_ptr(result.data) }.to_str().unwrap();
        assert!(data.contains("tell"));
        assert!(data.contains("hello"));
        unsafe { cbcl_string_free(result.data) };
    }

    #[test]
    fn parse_message_with_recipient() {
        let input = cstr("(tell @bob \"hello\")");
        let result = unsafe { cbcl_parse_message(input.as_ptr()) };
        assert_eq!(result.error, 0);
        let data = unsafe { CStr::from_ptr(result.data) }.to_str().unwrap();
        assert!(data.contains("@bob"));
        unsafe { cbcl_string_free(result.data) };
    }

    #[test]
    fn parse_message_error() {
        let input = cstr("(unclosed");
        let result = unsafe { cbcl_parse_message(input.as_ptr()) };
        assert_ne!(result.error, 0);
        let data = unsafe { CStr::from_ptr(result.data) }.to_str().unwrap();
        assert!(data.contains("parse error"));
        unsafe { cbcl_string_free(result.data) };
    }

    #[test]
    fn parse_message_null() {
        let result = unsafe { cbcl_parse_message(ptr::null()) };
        assert_ne!(result.error, 0);
        unsafe { cbcl_string_free(result.data) };
    }

    // -- verify_dialect --

    #[test]
    fn verify_valid_dialect() {
        let input = cstr("(define test-dialect (cbcl) @author)");
        let result = unsafe { cbcl_verify_dialect(input.as_ptr()) };
        assert_eq!(result.error, 0);
        let data = unsafe { CStr::from_ptr(result.data) }.to_str().unwrap();
        assert_eq!(data, "ok");
        unsafe { cbcl_string_free(result.data) };
    }

    #[test]
    fn verify_dialect_r3_violation() {
        let input = cstr("(define bad (cbcl) @a (extend tell (m) (effect x)))");
        let result = unsafe { cbcl_verify_dialect(input.as_ptr()) };
        assert_ne!(result.error, 0);
        let data = unsafe { CStr::from_ptr(result.data) }.to_str().unwrap();
        assert!(data.contains("verification failed"));
        unsafe { cbcl_string_free(result.data) };
    }

    #[test]
    fn verify_dialect_parse_error() {
        let input = cstr("(unclosed");
        let result = unsafe { cbcl_verify_dialect(input.as_ptr()) };
        assert_ne!(result.error, 0);
        unsafe { cbcl_string_free(result.data) };
    }

    // -- agent lifecycle --

    #[test]
    fn agent_new_and_free() {
        let id = cstr("test-agent");
        let agent = unsafe { cbcl_agent_new(id.as_ptr()) };
        assert!(!agent.is_null());
        unsafe { cbcl_agent_free(agent) };
    }

    #[test]
    fn agent_new_null() {
        let agent = unsafe { cbcl_agent_new(ptr::null()) };
        assert!(agent.is_null());
    }

    #[test]
    fn agent_free_null() {
        // Should not crash
        unsafe { cbcl_agent_free(ptr::null_mut()) };
    }

    // -- agent_send --

    #[test]
    fn agent_send_basic() {
        let id = cstr("sender");
        let agent = unsafe { cbcl_agent_new(id.as_ptr()) };
        assert!(!agent.is_null());

        let recipient = cstr("bob");
        let content = cstr("\"hello\"");
        let result = unsafe { cbcl_agent_send(agent, recipient.as_ptr(), content.as_ptr()) };
        assert_eq!(result.error, 0);
        let data = unsafe { CStr::from_ptr(result.data) }.to_str().unwrap();
        assert!(data.contains("send-message"));

        unsafe {
            cbcl_string_free(result.data);
            cbcl_agent_free(agent);
        };
    }

    #[test]
    fn agent_send_with_at_prefix() {
        let id = cstr("sender");
        let agent = unsafe { cbcl_agent_new(id.as_ptr()) };

        let recipient = cstr("@alice");
        let content = cstr("\"hi\"");
        let result = unsafe { cbcl_agent_send(agent, recipient.as_ptr(), content.as_ptr()) };
        assert_eq!(result.error, 0);

        unsafe {
            cbcl_string_free(result.data);
            cbcl_agent_free(agent);
        };
    }

    #[test]
    fn agent_send_null_agent() {
        let recipient = cstr("bob");
        let content = cstr("\"hi\"");
        let result =
            unsafe { cbcl_agent_send(ptr::null_mut(), recipient.as_ptr(), content.as_ptr()) };
        assert_ne!(result.error, 0);
        unsafe { cbcl_string_free(result.data) };
    }

    #[test]
    fn agent_send_null_recipient() {
        let id = cstr("sender");
        let agent = unsafe { cbcl_agent_new(id.as_ptr()) };

        let content = cstr("\"hi\"");
        let result = unsafe { cbcl_agent_send(agent, ptr::null(), content.as_ptr()) };
        assert_ne!(result.error, 0);

        unsafe {
            cbcl_string_free(result.data);
            cbcl_agent_free(agent);
        };
    }
}
