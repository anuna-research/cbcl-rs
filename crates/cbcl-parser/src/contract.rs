//! SPEC-087: the JSON authoring contract and its compilation to one CBCL
//! dialect carrying the state clause (SPEC-019). A contract is data an agent
//! writes; the dialect it compiles to is what every host installs, verifies,
//! and folds. One implementation, so every host that authors from JSON gets
//! the same dialect, and therefore the same self-address, for the same
//! contract (SPEC-087 REQ-001, REQ-002).
//!
//! ```text
//! compile_contract(<json>) → {"name": "sha256-…", "label": …, "dialect": "(define sha256-… …)"}
//! ```
//!
//! Recognition (CON-001) rejects a malformed record before anything is
//! compiled; the compiled dialect is then installed through R1–R7 and any
//! blame is returned verbatim. The name is `dialect_hash` over the body, so
//! the contract's `name` is a label and no part of identity.

use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use cbcl_core::canonical::dialect_name;
use cbcl_core::state::Value;
use serde_json::{Map, Value as Json};

pub const CONTRACT_VERSION: u64 = 3;
pub const MAX_CONTRACT_BYTES: usize = 16384;

/// The eight core performatives plus `lang`, never a contract verb.
const CORE: &[&str] = &["tell", "ask", "reply", "error", "ok", "cancel", "hello", "bye", "lang"];
/// Keywords the binder owns; never a field name.
const ROUTING: &[&str] = &[
    "from", "thread", "dialect", "caused-by", "to", "sender", "replaces", "audience", "sig", "key",
    "signing-key",
];
const RESERVED_NAMES: &[&str] = &["begin", "constructor", "prototype", "__proto__"];
const RESOURCE_KEYS: &[(&str, &str, u64)] = &[
    ("maxDepth", "max-depth", 16),
    ("maxExpansionSize", "max-expansion-size", 4096),
    ("verificationTime", "verification-time", 1000),
];
const BOUND_KEYS: &[(&str, &str)] = &[
    ("maxString", "max-string"),
    ("maxList", "max-list"),
    ("maxNumber", "max-number"),
    ("maxFields", "max-fields"),
];

/// Argument kinds of a rule: a verb, a keyword field, a state field, an optional verb.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Arg {
    Verb,
    Key,
    Field,
    OptVerb,
}

/// The fourteen rule heads (SPEC-019 R.1) as JSON spells them, with the
/// dialect head and the shape of their arguments.
const RULES: &[(&str, &str, &[Arg])] = &[
    ("last", "last", &[Arg::Verb, Arg::Key]),
    ("latestPerSigner", "latest-per-signer", &[Arg::Verb, Arg::Key]),
    ("latestPerKey", "latest-per-key", &[Arg::Verb, Arg::Key, Arg::Key]),
    ("exists", "exists", &[Arg::Verb]),
    ("count", "count", &[Arg::Verb]),
    ("events", "events", &[Arg::Verb, Arg::Key]),
    ("setUnion", "set-union", &[Arg::Verb, Arg::Key]),
    ("values", "values", &[Arg::Verb, Arg::Key]),
    ("valuesPerKey", "values-per-key", &[Arg::Verb, Arg::Key, Arg::Key, Arg::OptVerb]),
    ("registerPerKey", "register-per-key", &[Arg::Verb, Arg::Key, Arg::Key, Arg::OptVerb]),
    ("observedSet", "observed-set", &[Arg::Verb, Arg::Verb, Arg::Key]),
    ("counter", "counter", &[Arg::Verb, Arg::Verb, Arg::Key]),
    ("histogram", "histogram", &[Arg::Field]),
    ("sum", "sum", &[Arg::Field]),
];

fn err<T>(message: impl AsRef<str>) -> Result<T, String> {
    Err(format!("contract: {}", message.as_ref()))
}

fn identifier(s: &str) -> bool {
    let mut chars = s.chars();
    let ok_head = matches!(chars.next(), Some(c) if c.is_ascii_lowercase());
    ok_head
        && s.len() <= 48
        && s.chars().all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-')
        && !ROUTING.contains(&s)
        && !RESERVED_NAMES.contains(&s)
}

fn handle(s: &str) -> bool {
    s.len() >= 2
        && s.len() <= 64
        && s.starts_with('@')
        && s[1..].chars().all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '.' | '-'))
}

fn record<'a>(
    value: &'a Json,
    required: &[&str],
    optional: &[&str],
    what: &str,
) -> Result<&'a Map<String, Json>, String> {
    let Some(map) = value.as_object() else {
        return err(format!("{what} must be a record"));
    };
    for key in map.keys() {
        if !required.contains(&key.as_str()) && !optional.contains(&key.as_str()) {
            return err(format!("unknown record field {key} in {what}"));
        }
    }
    for key in required {
        if !map.contains_key(*key) {
            return err(format!("missing record field {key} in {what}"));
        }
    }
    Ok(map)
}

fn positive_int(value: &Json, what: &str) -> Result<u64, String> {
    match value.as_u64() {
        Some(n) if n > 0 => Ok(n),
        _ => err(format!("{what} must be a positive integer")),
    }
}

/// A recognised contract, ready to emit.
struct Contract<'a> {
    name: &'a str,
    author: &'a str,
    resources: Vec<(&'static str, u64)>,
    bounds: Vec<(&'static str, u64)>,
    roles: Vec<(&'a str, bool)>, // (role, indexed)
    verbs: Vec<Verb<'a>>,
    state: Vec<(&'a str, &'a str, Vec<(Arg, &'a str)>)>, // (field, head, args)
}

struct Verb<'a> {
    name: &'a str,
    after: Vec<&'a str>,
    fields: Vec<(&'a str, &'a str, Option<&'a str>)>, // (field, type, enumOf)
    from: Option<&'a str>,
    to: Vec<&'a str>,
}

fn recognize(json: &Json) -> Result<Contract<'_>, String> {
    let top = record(
        json,
        &["version", "kind", "name", "verbs", "state"],
        &["author", "requirements", "bounds", "roles"],
        "contract",
    )?;
    if top["version"].as_u64() != Some(CONTRACT_VERSION) || top["kind"].as_str() != Some("contract") {
        return err("unsupported contract version");
    }
    let name = top["name"].as_str().filter(|n| identifier(n));
    let Some(name) = name else { return err("invalid contract name") };
    let author = match top.get("author") {
        None => "@object",
        Some(a) => match a.as_str() {
            Some(h) if handle(h) => h,
            _ => return err("invalid author handle"),
        },
    };
    let mut resources = Vec::new();
    if let Some(r) = top.get("requirements") {
        let map = record(r, &[], &RESOURCE_KEYS.iter().map(|k| k.0).collect::<Vec<_>>(), "requirements")?;
        for (json_key, cbcl_key, _) in RESOURCE_KEYS {
            if let Some(v) = map.get(*json_key) {
                resources.push((*cbcl_key, positive_int(v, json_key)?));
            }
        }
    }
    let mut bounds = Vec::new();
    if let Some(b) = top.get("bounds") {
        let map = record(b, &[], &BOUND_KEYS.iter().map(|k| k.0).collect::<Vec<_>>(), "bounds")?;
        // Emit in declaration order.
        for (key, value) in map {
            let cbcl = BOUND_KEYS.iter().find(|k| k.0 == key).map(|k| k.1).unwrap();
            bounds.push((cbcl, positive_int(value, key)?));
        }
    }
    let mut roles = Vec::new();
    if let Some(r) = top.get("roles") {
        let Some(map) = r.as_object() else { return err("roles must be a record") };
        if map.is_empty() || map.len() > 16 {
            return err("a contract declares between 1 and 16 roles");
        }
        for (role, kind) in map {
            let indexed = match kind.as_str() {
                Some("singleton") => false,
                Some("indexed") => true,
                _ => return err(format!("invalid role kind for {role}")),
            };
            if !identifier(role) {
                return err(format!("invalid role name {role}"));
            }
            roles.push((role.as_str(), indexed));
        }
    }
    let has_roles = !roles.is_empty();
    let Some(verb_map) = top["verbs"].as_object() else { return err("verbs must be a record") };
    if verb_map.is_empty() || verb_map.len() > 16 {
        return err("a contract declares between 1 and 16 verbs");
    }
    let mut verbs = Vec::new();
    let mut openers = 0;
    for (verb, rule) in verb_map {
        if !identifier(verb) || CORE.contains(&verb.as_str()) {
            return err(format!("invalid verb {verb}"));
        }
        let optional: &[&str] = if has_roles { &["from", "to"] } else { &[] };
        let map = record(rule, &["after", "fields"], optional, verb)?;
        let Some(after) = map["after"].as_array() else { return err(format!("invalid predecessors of {verb}")) };
        if after.is_empty() || after.len() > 16 {
            return err(format!("invalid predecessors of {verb}"));
        }
        let mut preds = Vec::new();
        for p in after {
            match p.as_str() {
                Some("begin") => preds.push("begin"),
                Some(other) if verb_map.contains_key(other) => preds.push(other),
                _ => return err(format!("unknown predecessor of {verb}")),
            }
        }
        if preds.contains(&"begin") {
            if preds.len() != 1 {
                return err("an opener follows only begin");
            }
            openers += 1;
        }
        let Some(field_map) = map["fields"].as_object() else { return err(format!("invalid fields of {verb}")) };
        if field_map.len() > 16 {
            return err(format!("too many fields on {verb}"));
        }
        let mut fields = Vec::new();
        for (field, ty) in field_map {
            if !identifier(field) {
                return err(format!("invalid field name {field}"));
            }
            match ty {
                Json::String(t) if matches!(t.as_str(), "string" | "number" | "bool" | "list") => {
                    fields.push((field.as_str(), t.as_str(), None))
                }
                Json::Object(_) => {
                    let m = record(ty, &["enumOf"], &[], field)?;
                    match m["enumOf"].as_str() {
                        Some(target) if identifier(target) => fields.push((field.as_str(), "string", Some(target))),
                        _ => return err("invalid domain"),
                    }
                }
                _ => return err(format!("invalid type of {verb} {field}")),
            }
        }
        let (from, to) = if has_roles {
            let from = map.get("from").and_then(Json::as_str);
            let to = map.get("to").and_then(Json::as_array);
            let (Some(from), Some(to)) = (from, to) else {
                return err(format!("roles require from and to on {verb}"));
            };
            if !roles.iter().any(|(r, _)| *r == from) {
                return err(format!("unknown sender role of {verb}"));
            }
            let mut names = Vec::new();
            for r in to {
                match r.as_str() {
                    Some(role) if roles.iter().any(|(x, _)| *x == role) => names.push(role),
                    _ => return err(format!("unknown recipient role of {verb}")),
                }
            }
            (Some(from), names)
        } else {
            (None, Vec::new())
        };
        verbs.push(Verb { name: verb.as_str(), after: preds, fields, from, to });
    }
    if openers != 1 {
        return err("exactly one opener required");
    }
    let Some(state_map) = top["state"].as_object() else { return err("state must be a record") };
    if state_map.is_empty() || state_map.len() > 32 {
        return err("a state declares between 1 and 32 fields");
    }
    let mut state = Vec::new();
    for (field, expr) in state_map {
        if !identifier(field) {
            return err(format!("invalid state field {field}"));
        }
        let Some(items) = expr.as_array() else { return err(format!("unknown rule for {field}")) };
        let Some(op) = items.first().and_then(Json::as_str) else { return err(format!("unknown rule for {field}")) };
        let Some((_, head, shape)) = RULES.iter().find(|r| r.0 == op) else {
            return err(format!("unknown rule for {field}"));
        };
        let args = &items[1..];
        let fixed = shape.iter().filter(|a| **a != Arg::OptVerb).count();
        if args.len() < fixed || args.len() > shape.len() {
            return err(format!("wrong arity for {field}"));
        }
        let mut out = Vec::new();
        for (kind, arg) in shape.iter().zip(args) {
            match arg.as_str() {
                Some(a) if identifier(a) => out.push((*kind, a)),
                _ => return err(format!("invalid argument in {field}")),
            }
        }
        state.push((field.as_str(), *head, out));
    }
    for verb in &verbs {
        for (_, _, domain) in &verb.fields {
            if let Some(target) = domain {
                if !state_map.contains_key(*target) {
                    return err(format!("domain {target} is not a state field"));
                }
            }
        }
    }
    Ok(Contract { name, author, resources, bounds, roles, verbs, state })
}

/// The dialect text of a recognised contract, named `name` (SPEC-087 CON-001).
fn emit(c: &Contract<'_>, name: &str) -> String {
    let mut out = String::new();
    out.push_str(&format!("(define {name} (cbcl) {}\n", c.author));
    let resources: Vec<String> = RESOURCE_KEYS
        .iter()
        .map(|(_, key, default)| {
            let value = c.resources.iter().find(|(k, _)| k == key).map(|(_, v)| *v).unwrap_or(*default);
            format!("({key} {value})")
        })
        .collect();
    out.push_str(&format!("  (:resource-requirements ({}))\n", resources.join(" ")));
    if !c.bounds.is_empty() {
        let bounds: Vec<String> = c.bounds.iter().map(|(k, v)| format!("({k} {v})")).collect();
        out.push_str(&format!("  (:state-bounds {})\n", bounds.join(" ")));
    }
    if !c.roles.is_empty() {
        let roles: Vec<String> = c
            .roles
            .iter()
            .map(|(r, indexed)| if *indexed { format!("(* {r})") } else { r.to_string() })
            .collect();
        out.push_str(&format!("  (:roles ({}))\n", roles.join(" ")));
    }
    for v in &c.verbs {
        let params: Vec<&str> = v.fields.iter().map(|f| f.0).collect();
        let annotation = match v.from {
            Some(from) => format!(" :from {from} :to ({})", v.to.join(" ")),
            None => String::new(),
        };
        let template: String = v.fields.iter().map(|f| format!(" :{} {}", f.0, f.0)).collect();
        let param_list = if params.is_empty() { String::new() } else { format!(" {}", params.join(" ")) };
        out.push_str(&format!("  (extend {} (to{param_list}){annotation} (tell to{template}))\n", v.name));
    }
    for v in &c.verbs {
        if v.fields.is_empty() {
            continue;
        }
        let rules: String = v.fields.iter().map(|(f, t, _)| format!(" (require :{f} {t})")).collect();
        out.push_str(&format!("  (shape {}{rules})\n", v.name));
    }
    let steps: String = c
        .verbs
        .iter()
        .map(|v| {
            let pred = if v.after.len() == 1 { v.after[0].to_string() } else { format!("(any {})", v.after.join(" ")) };
            format!(" (then {pred} {})", v.name)
        })
        .collect();
    out.push_str(&format!("  (protocol{steps})\n"));
    let domains: Vec<(&str, String)> = c
        .verbs
        .iter()
        .flat_map(|v| {
            v.fields.iter().filter_map(move |(f, _, d)| {
                d.map(|target| (target, format!("(domain {} :{f} {target})", v.name)))
            })
        })
        .collect();
    let mut entries = Vec::new();
    for (field, head, args) in &c.state {
        let rendered: String = args
            .iter()
            .map(|(kind, a)| match kind {
                Arg::Key => format!(" :{a}"),
                _ => format!(" {a}"),
            })
            .collect();
        entries.push(format!("({field} ({head}{rendered}))"));
        for (reads, entry) in &domains {
            if reads == field {
                entries.push(entry.clone());
            }
        }
    }
    out.push_str(&format!("  (state {}))", entries.join(" ")));
    out
}

/// Compile a JSON contract to its dialect: recognise, emit, name by
/// self-address, install through R1–R7. Returns JSON
/// `{"name": …, "label": …, "dialect": …}` or a reason.
pub fn compile_contract_str(input: &str) -> Result<String, String> {
    if input.len() > MAX_CONTRACT_BYTES {
        return err("contract exceeds 16 KiB");
    }
    let json: Json = serde_json::from_str(input).map_err(|e| format!("contract: invalid JSON: {e}"))?;
    let contract = recognize(&json)?;
    let draft = emit(&contract, contract.name);
    let parsed = crate::parser::parse(&draft).map_err(|e| format!("contract: emitted dialect does not parse: {e}"))?;
    let dialect = crate::parse_dialect(&parsed).map_err(|e| format!("contract: emitted dialect is malformed: {e}"))?;
    let name = dialect_name(&dialect);
    let text = emit(&contract, &name);
    let sexpr = crate::parser::parse(&text).map_err(|e| format!("contract: emitted dialect does not parse: {e}"))?;
    crate::state_exports::parse_and_install_dialect(&sexpr)?;
    Ok(format!(
        "{{\"name\":{},\"label\":{},\"dialect\":{}}}",
        Value::Str(name).render(),
        Value::Str(contract.name.into()).render(),
        Value::Str(text).render()
    ))
}
