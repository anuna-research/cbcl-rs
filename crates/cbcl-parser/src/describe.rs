//! Reading dialects and acts for a host, so no host re-encodes CBCL's grammar
//! to look inside one (SPEC-013 REQ-018, SPEC-010 REQ-002). Three reads, each
//! the parser's and the installed structures' view, returned as JSON:
//!
//! ```text
//! define_text(<define | (meta (define …)) | (meta (teach (define …)))>) → canonical "(define …)"
//! describe_dialect(<dialect text>)  → {name, author, opener, verbs, roles, state, domains, bounds, text}
//! read_act(<message text>)          → {dialect, address, verb, recipients, fields, thread, from, causedBy}
//! ```

use alloc::string::{String, ToString};
use alloc::vec::Vec;
use cbcl_core::dialect::Dialect;
use cbcl_core::message::{CausedBy, Message};
use cbcl_core::protocol::NodeRef;
use cbcl_core::role::RoleCardinality;
use cbcl_core::serializer::serialize;
use cbcl_core::sexpr::{Atom, SExpr};
use cbcl_core::shape::ShapeRule;
use cbcl_core::state::{Act, Entry, Rule, RESERVED_REPLACES};
use serde_json::{json, Map, Value as Json};

fn symbol(s: &SExpr) -> Option<&str> {
    match s {
        SExpr::Atom(Atom::Symbol(x)) => Some(x),
        _ => None,
    }
}

/// The `(define …)` form of a dialect text, a `(meta (define …))`, or a
/// `(meta (teach (define …)))` teach frame, in canonical serialisation.
pub fn define_form(input: &str) -> Result<SExpr, String> {
    let form = crate::parser::parse(input).map_err(|e| alloc::format!("parse error: {e}"))?;
    let mut current = &form;
    loop {
        let SExpr::List(items) = current else {
            return Err(String::from("expected a (define …), (meta (define …)) or (meta (teach (define …))) form"));
        };
        match items.first().and_then(symbol) {
            Some("define") => return Ok(current.clone()),
            Some("meta") | Some("teach") if items.len() >= 2 => current = &items[1],
            _ => return Err(String::from("expected a (define …), (meta (define …)) or (meta (teach (define …))) form")),
        }
    }
}

/// `define_text`: the canonical text of the `(define …)` a frame carries.
pub fn define_text_str(input: &str) -> Result<String, String> {
    Ok(serialize(&define_form(input)?))
}

fn json_of_sexpr(s: &SExpr) -> Json {
    match s {
        SExpr::List(items) => Json::Array(items.iter().map(json_of_sexpr).collect()),
        SExpr::Atom(Atom::Str(x)) | SExpr::Atom(Atom::Symbol(x)) => Json::String(x.clone()),
        SExpr::Atom(Atom::Keyword(k)) => Json::String(alloc::format!(":{k}")),
        SExpr::Atom(Atom::Num(n)) => json!(n),
        SExpr::Atom(Atom::Bool(b)) => Json::Bool(*b),
    }
}

/// A rule of the state clause as JSON's spelling: `[op, arg…]`, keys without their colon.
fn rule_json(rule: &Rule) -> Json {
    let (op, args): (&str, Vec<&str>) = match rule {
        Rule::Last { verb, key } => ("last", alloc::vec![verb, key]),
        Rule::LatestPerSigner { verb, key } => ("latestPerSigner", alloc::vec![verb, key]),
        Rule::LatestPerKey { verb, key, value } => ("latestPerKey", alloc::vec![verb, key, value]),
        Rule::Exists { verb } => ("exists", alloc::vec![verb]),
        Rule::Count { verb } => ("count", alloc::vec![verb]),
        Rule::Events { verb, key } => ("events", alloc::vec![verb, key]),
        Rule::SetUnion { verb, key } => ("setUnion", alloc::vec![verb, key]),
        Rule::Values { verb, key } => ("values", alloc::vec![verb, key]),
        Rule::ValuesPerKey { verb, key, value, delete } => {
            let mut v = alloc::vec![verb.as_str(), key, value];
            if let Some(d) = delete { v.push(d); }
            ("valuesPerKey", v)
        }
        Rule::RegisterPerKey { verb, key, value, delete } => {
            let mut v = alloc::vec![verb.as_str(), key, value];
            if let Some(d) = delete { v.push(d); }
            ("registerPerKey", v)
        }
        Rule::ObservedSet { add, remove, key } => ("observedSet", alloc::vec![add, remove, key]),
        Rule::Counter { inc, dec, key } => ("counter", alloc::vec![inc, dec, key]),
        Rule::Histogram { field } => ("histogram", alloc::vec![field]),
        Rule::Sum { field } => ("sum", alloc::vec![field]),
    };
    let mut out = alloc::vec![Json::String(op.to_string())];
    out.extend(args.into_iter().map(|a| Json::String(a.to_string())));
    Json::Array(out)
}

/// What a host or a view needs to know about a dialect, from the installed structures.
pub fn describe(d: &Dialect, text: &str) -> Json {
    let mut verbs = Map::new();
    for p in &d.performatives {
        let params: Vec<Json> = p.params.iter().map(json_of_sexpr).collect();
        let mut fields = Map::new();
        for shape in d.shapes.iter().filter(|s| s.performative == p.name) {
            for rule in &shape.rules {
                if let ShapeRule::Require { keyword, type_constraint, .. } = rule {
                    if keyword == RESERVED_REPLACES {
                        continue;
                    }
                    let ty = type_constraint.map(|t| t.to_string()).unwrap_or_default();
                    fields.insert(keyword.clone(), Json::String(ty));
                }
            }
        }
        let after: Vec<Json> = d
            .causal_protocol
            .as_ref()
            .and_then(|proto| proto.steps.get(&p.name))
            .map(|step| {
                step.predecessors
                    .iter()
                    .flat_map(|n| match n {
                        NodeRef::Single(s) => alloc::vec![s.clone()],
                        NodeRef::Any(set) | NodeRef::All(set) => set.iter().cloned().collect(),
                    })
                    .map(Json::String)
                    .collect()
            })
            .unwrap_or_default();
        let mut entry = json!({ "params": params, "fields": fields, "after": after });
        if let Some(ann) = &p.role {
            entry["from"] = Json::String(ann.from.clone());
            entry["to"] = Json::Array(ann.to.iter().cloned().map(Json::String).collect());
        }
        verbs.insert(p.name.clone(), entry);
    }
    let opener = d
        .causal_protocol
        .as_ref()
        .and_then(cbcl_core::state::opener_verb)
        .map(|v| Json::String(v.to_string()))
        .unwrap_or(Json::Null);
    let mut roles = Map::new();
    for r in &d.roles {
        let kind = match r.cardinality {
            RoleCardinality::Singleton => "singleton",
            RoleCardinality::Indexed => "indexed",
        };
        roles.insert(r.name.clone(), Json::String(kind.to_string()));
    }
    let mut state = Map::new();
    let mut domains = Vec::new();
    if let Some(clause) = &d.state {
        for entry in &clause.entries {
            match entry {
                Entry::Field { name, rule } => {
                    state.insert(name.clone(), rule_json(rule));
                }
                Entry::Domain { verb, key, field } => {
                    domains.push(json!({ "verb": verb, "key": key, "field": field }));
                }
            }
        }
    }
    let bounds = match &d.state_bounds {
        Some(b) => json!({ "max-string": b.max_string, "max-list": b.max_list, "max-number": b.max_number, "max-fields": b.max_fields }),
        None => json!({}),
    };
    json!({
        "name": d.name,
        "author": d.author,
        "opener": opener,
        "verbs": verbs,
        "roles": roles,
        "state": state,
        "domains": domains,
        "bounds": bounds,
        "text": text,
    })
}

/// `describe_dialect`: a dialect text (or teach frame) → its description as JSON.
pub fn describe_dialect_str(input: &str) -> Result<String, String> {
    let form = define_form(input)?;
    let d = crate::parse_dialect(&form).map_err(|e| alloc::format!("dialect parse error: {e}"))?;
    Ok(describe(&d, &serialize(&form)).to_string())
}

fn dialect_of(m: &Message) -> Option<&str> {
    match m {
        Message::Dialect { dialect_name, .. } => Some(dialect_name),
        Message::Wrapped { content, .. } => dialect_of(content),
        _ => None,
    }
}

/// `read_act`: an act's wire text → its dialect, address, verb, recipients,
/// data fields (routing excluded), and routing, as JSON.
pub fn read_act_str(input: &str) -> Result<String, String> {
    let form = crate::parser::parse(input).map_err(|e| alloc::format!("parse error: {e}"))?;
    let message = crate::parse_message(&form).map_err(|e| alloc::format!("message parse error: {e}"))?;
    let dialect = dialect_of(&message).map(|s| s.to_string());
    let act = Act::from_message(message, "")?;
    let simple = act.simple();
    let from = match simple {
        Message::Simple { params, .. } => {
            let mut found = None;
            let mut i = 0;
            while i + 1 < params.len() {
                if matches!(&params[i], SExpr::Atom(Atom::Keyword(k)) if k == "from") {
                    found = symbol(&params[i + 1]).map(|s| s.to_string()).or_else(|| match &params[i + 1] {
                        SExpr::Atom(Atom::Str(s)) => Some(s.clone()),
                        _ => None,
                    });
                }
                i += 2;
            }
            found
        }
        _ => None,
    };
    let caused_by = match simple.caused_by() {
        None | Some(CausedBy::Begin) => Json::String("begin".into()),
        Some(CausedBy::Single(h)) => Json::String(h.clone()),
        Some(CausedBy::Multiple(hs)) => Json::Array(hs.iter().cloned().map(Json::String).collect()),
    };
    let mut fields = Map::new();
    for (k, v) in &act.fields {
        fields.insert(k.clone(), json_of_sexpr(v));
    }
    Ok(json!({
        "dialect": dialect,
        "address": act.address,
        "verb": act.verb,
        "recipients": act.recipients.iter().cloned().collect::<Vec<_>>(),
        "fields": fields,
        "thread": simple.thread(),
        "from": from,
        "causedBy": caused_by,
    })
    .to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    const D: &str = "(define d (cbcl) @a (extend open (to title) (tell to :title title)) (extend vote (to choice) (tell to :choice choice)) (shape open (require :title string)) (shape vote (require :choice string)) (protocol (then begin open) (then open vote)) (state (title (last open :title)) (ballots (latest-per-signer vote :choice))))";

    #[test]
    fn define_text_unwraps_meta_and_teach() {
        let bare = define_text_str(D).unwrap();
        assert!(bare.starts_with("(define d (cbcl) @a"));
        assert_eq!(define_text_str(&alloc::format!("; c\n(meta {D})")).unwrap(), bare);
        assert_eq!(define_text_str(&alloc::format!("(meta (teach {D}))")).unwrap(), bare);
        assert!(define_text_str("(tell @a \"x\")").is_err());
    }

    #[test]
    fn describe_reads_the_installed_structures() {
        let v: Json = serde_json::from_str(&describe_dialect_str(D).unwrap()).unwrap();
        assert_eq!(v["opener"], "open");
        assert_eq!(v["verbs"]["vote"]["fields"]["choice"], "string");
        assert_eq!(v["verbs"]["vote"]["after"], json!(["open"]));
        assert_eq!(v["state"]["ballots"], json!(["latestPerSigner", "vote", "choice"]));
        assert_eq!(v["roles"], json!({}));
    }

    #[test]
    fn read_act_gives_routing_and_fields() {
        let v: Json = serde_json::from_str(&read_act_str("(lang d (vote (@a @b) :choice \"x\" :n 3 :ok #t :caused-by begin :thread \"t\" :from @b))").unwrap()).unwrap();
        assert_eq!(v["dialect"], "d");
        assert_eq!(v["verb"], "vote");
        assert_eq!(v["recipients"], json!(["@a", "@b"]));
        assert_eq!(v["fields"], json!({"choice": "x", "n": 3, "ok": true}));
        assert_eq!(v["thread"], "t");
        assert_eq!(v["from"], "@b");
        assert_eq!(v["causedBy"], "begin");
        assert!(v["address"].as_str().unwrap().starts_with("sha256-"));
    }
}
