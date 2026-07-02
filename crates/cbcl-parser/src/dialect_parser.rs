//! Dialect definition parser.
//!
//! Extracts `Dialect` from `(define dialect-name ...)` S-expressions,
//! matching the Guile reference `define-dialect` in `cbcl.scm:514`.

#![forbid(unsafe_code)]

use alloc::string::String;
use alloc::vec::Vec;
use cbcl_core::dialect::{Dialect, PerformativeDef, ResourceBounds};
use cbcl_core::protocol::CausalProtocol;
use cbcl_core::role::{parse_from, parse_recipient_set, parse_roles, RoleAnnotation, RoleDecl};
use cbcl_core::sexpr::{Atom, SExpr};
use cbcl_core::shape::ShapeConstraint;

/// Parse a dialect definition from a `(define name extends author clauses...)` form (REQ-045).
///
/// Expected shape (matching `define-dialect` in `cbcl.scm:514`):
/// ```text
/// (define dialect-name
///   (parent1 parent2 ...)
///   @author
///   (extend perf-name (param1 param2 ...) template)
///   ...
///   (:resource-requirements ((max-depth . N) (max-expansion-size . N) (verification-time . N)))
///   (:examples ...)
///   (:signature sig)
///   (:hash "sha256:...")
///   (:protocol "ed25519"))
/// ```
pub fn parse_dialect(sexpr: &SExpr) -> Result<Dialect, String> {
    let items = match sexpr {
        SExpr::List(items) => items,
        _ => return Err(String::from("dialect definition must be a list")),
    };

    if items.is_empty() {
        return Err(String::from("empty dialect definition"));
    }

    // First element must be 'define'
    if !items[0].is_symbol("define") {
        return Err(String::from("dialect definition must start with 'define'"));
    }

    if items.len() < 4 {
        return Err(String::from(
            "dialect definition requires at least: define, name, extends, author",
        ));
    }

    // Second element: dialect name (symbol)
    let name = extract_symbol(&items[1], "dialect name")?;

    // Third element: extends list
    let extends = extract_extends(&items[2])?;

    // Fourth element: author (symbol starting with @, or string)
    let author = extract_author(&items[3])?;

    // Remaining elements: clauses
    let mut performatives = Vec::new();
    let mut resources = ResourceBounds {
        max_depth: 16,
        max_expansion_size: 1024,
        verification_time_ms: 50,
    };
    let mut examples = Vec::new();
    let mut signature: Option<Vec<u8>> = None;
    let mut hash: Option<String> = None;
    let mut protocol: Option<String> = None;
    let mut causal_protocol: Option<CausalProtocol> = None;
    let mut shapes: Vec<ShapeConstraint> = Vec::new();
    let mut roles: Vec<RoleDecl> = Vec::new();

    for clause in &items[4..] {
        parse_clause(
            clause,
            &mut performatives,
            &mut resources,
            &mut examples,
            &mut signature,
            &mut hash,
            &mut protocol,
            &mut causal_protocol,
            &mut shapes,
            &mut roles,
        )?;
    }

    Ok(Dialect {
        roles,
        name,
        extends,
        author,
        performatives,
        resources,
        examples,
        signature,
        hash,
        protocol,
        causal_protocol,
        shapes,
    })
}

/// Parse a dialect from `(meta (define ...))` form.
pub fn parse_meta_define(sexpr: &SExpr) -> Result<Dialect, String> {
    let items = match sexpr {
        SExpr::List(items) => items,
        _ => return Err(String::from("meta message must be a list")),
    };

    if items.len() != 2 {
        return Err(String::from("meta message must have exactly 2 elements"));
    }

    if !items[0].is_symbol("meta") {
        return Err(String::from("expected 'meta' keyword"));
    }

    parse_dialect(&items[1])
}

fn extract_symbol(sexpr: &SExpr, context: &str) -> Result<String, String> {
    match sexpr {
        SExpr::Atom(Atom::Symbol(s)) => Ok(s.clone()),
        _ => Err(alloc::format!("{context} must be a symbol")),
    }
}

fn extract_extends(sexpr: &SExpr) -> Result<Vec<String>, String> {
    match sexpr {
        SExpr::List(items) => {
            let mut extends = Vec::new();
            for item in items {
                extends.push(extract_symbol(item, "extends entry")?);
            }
            Ok(extends)
        }
        _ => Err(String::from("extends must be a list")),
    }
}

fn extract_author(sexpr: &SExpr) -> Result<Option<String>, String> {
    match sexpr {
        SExpr::Atom(Atom::Symbol(s)) => Ok(Some(s.clone())),
        SExpr::Atom(Atom::Str(s)) => Ok(Some(s.clone())),
        _ => Err(String::from("author must be a symbol or string")),
    }
}

fn parse_clause(
    clause: &SExpr,
    performatives: &mut Vec<PerformativeDef>,
    resources: &mut ResourceBounds,
    examples: &mut Vec<SExpr>,
    signature: &mut Option<Vec<u8>>,
    hash: &mut Option<String>,
    protocol: &mut Option<String>,
    causal_protocol: &mut Option<CausalProtocol>,
    shapes: &mut Vec<ShapeConstraint>,
    roles: &mut Vec<RoleDecl>,
) -> Result<(), String> {
    let items = match clause {
        SExpr::List(items) if !items.is_empty() => items,
        _ => return Err(String::from("clause must be a non-empty list")),
    };

    // Check if it's a keyword-prefixed clause
    if let SExpr::Atom(Atom::Keyword(kw)) = &items[0] {
        match kw.as_str() {
            "resource-requirements" => {
                if items.len() < 2 {
                    return Err(String::from("resource-requirements needs a value"));
                }
                *resources = parse_resource_requirements(&items[1])?;
            }
            "examples" => {
                for ex in &items[1..] {
                    examples.push(ex.clone());
                }
            }
            "signature" | "signed" => {
                if items.len() >= 2 {
                    *signature = Some(extract_signature_bytes(&items[1]));
                }
            }
            "hash" => {
                if items.len() >= 2 {
                    *hash = Some(extract_string_or_symbol(&items[1]));
                }
            }
            "protocol" => {
                if items.len() >= 2 {
                    *protocol = Some(extract_string_or_symbol(&items[1]));
                }
            }
            // SPEC-014 REQ-600/621: (:roles (name (* name) ...))
            "roles" => {
                if items.len() != 2 {
                    return Err(String::from(":roles takes exactly one value (CON-600)"));
                }
                *roles = parse_roles(&items[1]).map_err(|v| alloc::format!("{v}"))?;
            }
            _ => {
                return Err(alloc::format!("unknown keyword clause: :{kw}"));
            }
        }
        return Ok(());
    }

    // Check for 'extend' clause (performative definition)
    if items[0].is_symbol("extend") {
        if items.len() < 4 {
            return Err(String::from(
                "extend clause requires: extend name (params) template",
            ));
        }
        let perf_name = extract_symbol(&items[1], "performative name")?;
        let params = extract_param_list(&items[2])?;

        // SPEC-014 REQ-621/CON-600: optional :from/:to annotations may
        // appear before or after the template; exactly one template form.
        let mut template: Option<SExpr> = None;
        let mut from: Option<String> = None;
        let mut to = None;
        let mut rest = items[3..].iter();
        while let Some(item) = rest.next() {
            match item {
                SExpr::Atom(Atom::Keyword(kw)) if kw == "from" => {
                    let value = rest
                        .next()
                        .ok_or_else(|| alloc::format!(":from on '{perf_name}' needs a value"))?;
                    if from.is_some() {
                        return Err(alloc::format!("duplicate :from on '{perf_name}'"));
                    }
                    from = Some(parse_from(&perf_name, value).map_err(|v| alloc::format!("{v}"))?);
                }
                SExpr::Atom(Atom::Keyword(kw)) if kw == "to" => {
                    let value = rest
                        .next()
                        .ok_or_else(|| alloc::format!(":to on '{perf_name}' needs a value"))?;
                    if to.is_some() {
                        return Err(alloc::format!("duplicate :to on '{perf_name}'"));
                    }
                    to = Some(
                        parse_recipient_set(&perf_name, value)
                            .map_err(|v| alloc::format!("{v}"))?,
                    );
                }
                // Fail closed: an unrecognised keyword is not silently
                // absorbed as a template (CON-600, LangSec principle 4).
                SExpr::Atom(Atom::Keyword(kw)) => {
                    return Err(alloc::format!(
                        "extend '{perf_name}' has unknown keyword :{kw}"
                    ));
                }
                other => {
                    if template.is_some() {
                        return Err(alloc::format!(
                            "extend '{perf_name}' has more than one template form"
                        ));
                    }
                    template = Some(other.clone());
                }
            }
        }
        let template = template
            .ok_or_else(|| alloc::format!("extend '{perf_name}' is missing its template"))?;
        let role = match (from, to) {
            (Some(from), Some(to)) => Some(RoleAnnotation { from, to }),
            (None, None) => None,
            // Fail closed: half an annotation is malformed (CON-600).
            _ => {
                return Err(alloc::format!(
                    "extend '{perf_name}' must carry both :from and :to or neither (CON-600)"
                ))
            }
        };

        performatives.push(PerformativeDef {
            role,
            name: perf_name,
            params,
            template,
        });
        return Ok(());
    }

    // Check for 'protocol' clause (REQ-200, REQ-201)
    if items[0].is_symbol("protocol") {
        let cp = crate::protocol_parser::parse_protocol(clause)
            .map_err(|e| alloc::format!("protocol parse error: {e}"))?;
        *causal_protocol = Some(cp);
        return Ok(());
    }

    // Check for 'shape' clause (REQ-220, REQ-221)
    if items[0].is_symbol("shape") {
        let shape = crate::shape_parser::parse_shape(clause)?;
        shapes.push(shape);
        return Ok(());
    }

    Err(alloc::format!(
        "unknown clause type: {}",
        clause_head_description(&items[0])
    ))
}

fn parse_resource_requirements(sexpr: &SExpr) -> Result<ResourceBounds, String> {
    let items = match sexpr {
        SExpr::List(items) => items,
        _ => return Err(String::from("resource-requirements must be a list")),
    };

    let mut max_depth: u32 = 16;
    let mut max_expansion_size: u32 = 1024;
    let mut verification_time_ms: u32 = 50;

    for item in items {
        match item {
            // Alist form: (key . value) which parses as a 2-element list
            SExpr::List(pair) if pair.len() == 2 => {
                let key = match &pair[0] {
                    SExpr::Atom(Atom::Symbol(s)) => s.as_str(),
                    _ => continue,
                };
                let val = match &pair[1] {
                    SExpr::Atom(Atom::Num(n)) => *n as u32,
                    _ => continue,
                };
                match key {
                    "max-depth" => max_depth = val,
                    "max-expansion-size" => max_expansion_size = val,
                    "verification-time" => verification_time_ms = val,
                    _ => {}
                }
            }
            // Keyword form: :key value (handled as pairs in the parent list)
            _ => {}
        }
    }

    Ok(ResourceBounds {
        max_depth,
        max_expansion_size,
        verification_time_ms,
    })
}

fn extract_param_list(sexpr: &SExpr) -> Result<Vec<SExpr>, String> {
    match sexpr {
        SExpr::List(items) => Ok(items.clone()),
        _ => Err(String::from("parameter list must be a list")),
    }
}

fn extract_signature_bytes(sexpr: &SExpr) -> Vec<u8> {
    match sexpr {
        SExpr::Atom(Atom::Str(s)) => s.as_bytes().to_vec(),
        SExpr::Atom(Atom::Symbol(s)) => s.as_bytes().to_vec(),
        _ => Vec::new(),
    }
}

fn extract_string_or_symbol(sexpr: &SExpr) -> String {
    match sexpr {
        SExpr::Atom(Atom::Str(s)) | SExpr::Atom(Atom::Symbol(s)) => s.clone(),
        other => alloc::format!("{other}"),
    }
}

fn clause_head_description(sexpr: &SExpr) -> String {
    match sexpr {
        SExpr::Atom(Atom::Symbol(s)) => s.clone(),
        SExpr::Atom(Atom::Keyword(k)) => alloc::format!(":{k}"),
        _ => String::from("<non-symbol>"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    fn sym(s: &str) -> SExpr {
        SExpr::Atom(Atom::Symbol(String::from(s)))
    }

    fn kw(s: &str) -> SExpr {
        SExpr::Atom(Atom::Keyword(String::from(s)))
    }

    fn num(n: i64) -> SExpr {
        SExpr::Atom(Atom::Num(n))
    }

    fn str_expr(s: &str) -> SExpr {
        SExpr::Atom(Atom::Str(String::from(s)))
    }

    fn list(items: Vec<SExpr>) -> SExpr {
        SExpr::List(items)
    }

    fn make_resource_requirements(depth: i64, expansion: i64, time: i64) -> SExpr {
        list(vec![
            kw("resource-requirements"),
            list(vec![
                list(vec![sym("max-depth"), num(depth)]),
                list(vec![sym("max-expansion-size"), num(expansion)]),
                list(vec![sym("verification-time"), num(time)]),
            ]),
        ])
    }

    fn make_extend(name: &str, params: Vec<&str>, template: SExpr) -> SExpr {
        list(vec![
            sym("extend"),
            sym(name),
            list(params.into_iter().map(sym).collect()),
            template,
        ])
    }

    fn make_minimal_dialect() -> SExpr {
        list(vec![
            sym("define"),
            sym("test-dialect"),
            list(vec![sym("cbcl")]),
            sym("@test-author"),
        ])
    }

    #[test]
    fn parse_minimal_dialect() {
        let d = parse_dialect(&make_minimal_dialect()).unwrap();
        assert_eq!(d.name, "test-dialect");
        assert_eq!(d.extends, vec!["cbcl"]);
        assert_eq!(d.author, Some(String::from("@test-author")));
        assert!(d.performatives.is_empty());
    }

    #[test]
    fn parse_dialect_with_performative() {
        let def = list(vec![
            sym("define"),
            sym("my-dialect"),
            list(vec![sym("cbcl")]),
            sym("@author"),
            make_extend(
                "propose-step",
                vec!["step-id", "action", "achieves"],
                list(vec![sym("effect"), sym("propose")]),
            ),
        ]);
        let d = parse_dialect(&def).unwrap();
        assert_eq!(d.performatives.len(), 1);
        assert_eq!(d.performatives[0].name, "propose-step");
        assert_eq!(d.performatives[0].params.len(), 3);
    }

    #[test]
    fn parse_dialect_with_resources() {
        let def = list(vec![
            sym("define"),
            sym("my-dialect"),
            list(vec![sym("cbcl")]),
            sym("@author"),
            make_resource_requirements(16, 1024, 50),
        ]);
        let d = parse_dialect(&def).unwrap();
        assert_eq!(d.resources.max_depth, 16);
        assert_eq!(d.resources.max_expansion_size, 1024);
        assert_eq!(d.resources.verification_time_ms, 50);
    }

    #[test]
    fn parse_dialect_with_integrity() {
        let def = list(vec![
            sym("define"),
            sym("my-dialect"),
            list(vec![sym("cbcl")]),
            sym("@author"),
            list(vec![kw("hash"), str_expr("sha256:abcd1234")]),
            list(vec![kw("signature"), sym("sig123")]),
            list(vec![kw("protocol"), str_expr("ed25519")]),
        ]);
        let d = parse_dialect(&def).unwrap();
        assert_eq!(d.hash, Some(String::from("sha256:abcd1234")));
        assert!(d.signature.is_some());
        assert_eq!(d.protocol, Some(String::from("ed25519")));
    }

    #[test]
    fn parse_full_planning_dialect() {
        let def = list(vec![
            sym("define"),
            sym("cbcl-planning"),
            list(vec![sym("cbcl")]),
            sym("@planning-authority"),
            make_extend(
                "share-conditional",
                vec!["action", "precondition", "effect"],
                list(vec![sym("effect"), sym("share-conditional")]),
            ),
            make_extend(
                "propose-step",
                vec!["step-id", "action", "achieves"],
                list(vec![sym("effect"), sym("propose")]),
            ),
            make_resource_requirements(16, 1024, 50),
            list(vec![kw("protocol"), str_expr("ed25519")]),
            list(vec![
                kw("hash"),
                str_expr("sha256:planning-dialect-v1.0-hash"),
            ]),
            list(vec![kw("signature"), sym("planning-consortium-key-2024")]),
        ]);
        let d = parse_dialect(&def).unwrap();
        assert_eq!(d.name, "cbcl-planning");
        assert_eq!(d.extends, vec!["cbcl"]);
        assert_eq!(d.author, Some(String::from("@planning-authority")));
        assert_eq!(d.performatives.len(), 2);
        assert_eq!(d.resources.max_depth, 16);
        assert_eq!(d.resources.max_expansion_size, 1024);
        assert_eq!(d.protocol, Some(String::from("ed25519")));
        assert!(d.hash.is_some());
        assert!(d.signature.is_some());
    }

    #[test]
    fn parse_meta_define_form() {
        let meta = list(vec![sym("meta"), make_minimal_dialect()]);
        let d = parse_meta_define(&meta).unwrap();
        assert_eq!(d.name, "test-dialect");
    }

    #[test]
    fn reject_non_list() {
        assert!(parse_dialect(&sym("not-a-list")).is_err());
    }

    #[test]
    fn reject_missing_define() {
        let def = list(vec![
            sym("not-define"),
            sym("name"),
            list(vec![]),
            sym("@a"),
        ]);
        assert!(parse_dialect(&def).is_err());
    }

    #[test]
    fn reject_too_short() {
        let def = list(vec![sym("define"), sym("name")]);
        assert!(parse_dialect(&def).is_err());
    }

    #[test]
    fn parse_dialect_with_examples() {
        let def = list(vec![
            sym("define"),
            sym("my-dialect"),
            list(vec![sym("cbcl")]),
            sym("@author"),
            list(vec![
                kw("examples"),
                list(vec![sym("share-conditional"), sym("a"), sym("b")]),
            ]),
        ]);
        let d = parse_dialect(&def).unwrap();
        assert_eq!(d.examples.len(), 1);
    }

    #[test]
    fn parse_multiple_extends() {
        let def = list(vec![
            sym("define"),
            sym("multi"),
            list(vec![sym("cbcl"), sym("cbcl-planning")]),
            sym("@author"),
        ]);
        let d = parse_dialect(&def).unwrap();
        assert_eq!(d.extends, vec!["cbcl", "cbcl-planning"]);
    }

    #[test]
    fn default_resource_bounds() {
        let d = parse_dialect(&make_minimal_dialect()).unwrap();
        assert_eq!(d.resources.max_depth, 16);
        assert_eq!(d.resources.max_expansion_size, 1024);
        assert_eq!(d.resources.verification_time_ms, 50);
    }

    #[test]
    fn parse_from_text_round_trip() {
        let input = "(define my-dialect (cbcl) @author (extend greet (name) (effect greet-action)) (:resource-requirements ((max-depth 8) (max-expansion-size 512) (verification-time 10))) (:protocol \"ed25519\"))";
        let sexpr = crate::parser::parse(input).unwrap();
        let d = parse_dialect(&sexpr).unwrap();
        assert_eq!(d.name, "my-dialect");
        assert_eq!(d.performatives.len(), 1);
        assert_eq!(d.performatives[0].name, "greet");
        assert_eq!(d.resources.max_depth, 8);
        assert_eq!(d.protocol, Some(String::from("ed25519")));
    }

    // ---- SPEC-014 role annotations (REQ-600/621, CON-600) ----

    fn oauth_dialect_src() -> &'static str {
        "(define oauth (cbcl) @example \
           (:roles (server client authoriser)) \
           (extend login (session scope) :from server :to (client authoriser) \
             (tell @client)) \
           (extend passwd (session credential) :from client :to (authoriser server) \
             (tell @authoriser)) \
           (extend auth (session grant) (tell @server) :from authoriser :to server))"
    }

    #[test]
    fn parses_roles_attribute() {
        let sexpr: SExpr = oauth_dialect_src().parse().unwrap();
        let d = parse_dialect(&sexpr).unwrap();
        assert_eq!(d.roles.len(), 3);
        assert!(d
            .roles
            .iter()
            .all(|r| matches!(r.cardinality, cbcl_core::role::RoleCardinality::Singleton)));
    }

    #[test]
    fn parses_indexed_role_marker() {
        let sexpr: SExpr = "(define auction (cbcl) @a (:roles (auctioneer (* bidder))))"
            .parse()
            .unwrap();
        let d = parse_dialect(&sexpr).unwrap();
        assert_eq!(d.roles[1].name, "bidder");
        assert!(matches!(
            d.roles[1].cardinality,
            cbcl_core::role::RoleCardinality::Indexed
        ));
    }

    #[test]
    fn parses_from_to_before_and_after_template() {
        let sexpr: SExpr = oauth_dialect_src().parse().unwrap();
        let d = parse_dialect(&sexpr).unwrap();
        let login = d.find_performative("login").unwrap();
        let ann = login.role.as_ref().unwrap();
        assert_eq!(ann.from, "server");
        assert!(ann.to.contains("client") && ann.to.contains("authoriser"));
        // :from/:to after the template also parses (auth)
        let auth = d.find_performative("auth").unwrap();
        assert_eq!(auth.role.as_ref().unwrap().from, "authoriser");
    }

    /// TEST-621 (REQ-621): the parser populates the role data on the
    /// `Dialect` value itself — `Dialect.roles` and `PerformativeDef.role` —
    /// so `r6_violations`/`project` are functions of the `Dialect` alone.
    #[test]
    fn test_621_role_data_lands_on_dialect_types() {
        let sexpr: SExpr = oauth_dialect_src().parse().unwrap();
        let d = parse_dialect(&sexpr).unwrap();
        // Dialect carries the declared roles.
        let role_names: alloc::vec::Vec<&str> = d.roles.iter().map(|r| r.name.as_str()).collect();
        assert_eq!(role_names, ["server", "client", "authoriser"]);
        // Every protocol performative carries its annotation.
        for name in ["login", "passwd", "auth"] {
            assert!(
                d.find_performative(name).unwrap().role.is_some(),
                "{name} should carry a role annotation"
            );
        }
        // A role-free dialect carries neither.
        let plain: SExpr = "(define plain (cbcl) @a (extend p (x) (tell @x)))"
            .parse()
            .unwrap();
        let pd = parse_dialect(&plain).unwrap();
        assert!(pd.roles.is_empty());
        assert!(pd.find_performative("p").unwrap().role.is_none());
    }

    #[test]
    fn rejects_half_annotation() {
        let sexpr: SExpr = "(define x (cbcl) @a (:roles (r)) (extend p (a) :from r (tell @r)))"
            .parse()
            .unwrap();
        assert!(parse_dialect(&sexpr).is_err());
    }

    #[test]
    fn rejects_empty_roles() {
        let sexpr: SExpr = "(define x (cbcl) @a (:roles ()))".parse().unwrap();
        assert!(parse_dialect(&sexpr).is_err());
    }

    #[test]
    fn rejects_postfix_indexed_marker() {
        let sexpr: SExpr = "(define x (cbcl) @a (:roles (a (bidder *))))"
            .parse()
            .unwrap();
        assert!(parse_dialect(&sexpr).is_err());
    }

    #[test]
    fn empty_to_parses_as_terminal() {
        let sexpr: SExpr =
            "(define x (cbcl) @a (:roles (r)) (extend done (v) :from r :to () (tell @r)))"
                .parse()
                .unwrap();
        let d = parse_dialect(&sexpr).unwrap();
        assert!(d
            .find_performative("done")
            .unwrap()
            .role
            .as_ref()
            .unwrap()
            .to
            .is_empty());
    }
}
