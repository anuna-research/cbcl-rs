//! The OAuth fragment of the EPP paper (§6.1), driven through the actual
//! reference implementation: parse → install (R1–R5) → R6.
//!
//! This test is the paper's guarantee that its worked example is *real* CBCL:
//! the as-written dialect is rejected by R6 causal locality exactly as the
//! paper claims, and the recipient-widened repair installs cleanly. The
//! dialect text here is the concrete syntax the paper prints (with the
//! Scalas–Yoshida branch renamed `cancel` → `abort`, since `cancel` is one
//! of CBCL's eight reserved core performatives and R3 forbids redefining
//! it).

use cbcl_core::dialect::{DialectInstallError, DialectRegistry};
use cbcl_core::r6::r6_violations;
use cbcl_core::role::R6Violation;
use cbcl_core::sexpr::SExpr;
use cbcl_parser::parse_dialect;

/// The paper's OAuth dialect. `widened` selects the recipient-widened repair
/// (§6.1): `login`/`abort` gain `authoriser`, `passwd` gains `server`.
fn oauth_src(widened: bool) -> String {
    let (login_to, abort_to, passwd_to) = if widened {
        (
            "(client authoriser)",
            "(client authoriser)",
            "(authoriser server)",
        )
    } else {
        ("client", "client", "authoriser")
    };
    format!(
        "(define oauth (cbcl) @example
           (:roles (server client authoriser))
           (:resource-requirements
             ((max-depth 4) (max-expansion-size 256) (verification-time 10)))
           (extend login (session scope)
             :from server :to {login_to}
             (tell @client :session session :scope scope :domain oauth))
           (extend abort (session reason)
             :from server :to {abort_to}
             (tell @client :session session :reason reason :domain oauth))
           (extend passwd (session credential)
             :from client :to {passwd_to}
             (tell @authoriser :session session :credential credential :domain oauth))
           (extend auth (session grant)
             :from authoriser :to server
             (tell @server :session session :grant grant :domain oauth))
           (extend quit (session reason)
             :from client :to authoriser
             (tell @authoriser :session session :reason reason :domain oauth))
           (protocol (then begin (any login abort))
                     (then login passwd auth)
                     (then abort quit)))"
    )
}

fn parse(src: &str) -> cbcl_core::dialect::Dialect {
    let sexpr: SExpr = src
        .parse()
        .expect("OAuth dialect must parse as an S-expression");
    parse_dialect(&sexpr).expect("OAuth dialect must parse as a dialect")
}

#[test]
fn as_written_parses_and_passes_r1_r5_but_fails_r6() {
    let d = parse(&oauth_src(false));

    // The role layer parsed the annotations onto the dialect value.
    assert_eq!(d.roles.len(), 3);
    assert_eq!(
        d.find_performative("login")
            .unwrap()
            .role
            .as_ref()
            .unwrap()
            .from,
        "server"
    );

    // R6 rejects it for causal locality, naming exactly the three hand-offs
    // the paper calls out (§6.1): passwd/login/authoriser, auth/passwd/server,
    // quit/abort/authoriser.
    let violations = r6_violations(&d);
    assert!(violations.contains(&R6Violation::NotCausallyLocal {
        performative: "passwd".into(),
        predecessor: "login".into(),
        role: "authoriser".into(),
    }));
    assert!(violations.contains(&R6Violation::NotCausallyLocal {
        performative: "auth".into(),
        predecessor: "passwd".into(),
        role: "server".into(),
    }));
    assert!(violations.contains(&R6Violation::NotCausallyLocal {
        performative: "quit".into(),
        predecessor: "abort".into(),
        role: "authoriser".into(),
    }));

    // Installing it fails at R6 — but *only* R6: R1–R5 pass (so the failure
    // is the role layer's, not a malformed dialect).
    let mut reg = DialectRegistry::new();
    match reg.install(d) {
        Err(DialectInstallError::R6Violation { .. }) => {}
        other => panic!("expected an R6 violation, got {other:?}"),
    }
}

#[test]
fn recipient_widened_repair_installs_cleanly() {
    let d = parse(&oauth_src(true));
    assert_eq!(r6_violations(&d), Vec::new());
    let mut reg = DialectRegistry::new();
    reg.install(d)
        .expect("the widened OAuth dialect installs (R1–R6 pass)");
}
