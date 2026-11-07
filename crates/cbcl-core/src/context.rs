//! SPEC-038 CON-3804: read-only installed metadata and sealed cast context.
#![forbid(unsafe_code)]
use crate::dialect::Dialect;
use crate::role::{Cast, RoleCardinality, RoleDecl};
use crate::state::{Act, Rule, StateBounds, Value};
use alloc::boxed::Box;
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::{String, ToString};
use alloc::vec::Vec;

/// Rebuilt from the dialect; excluded from the authored canonical body.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Definition {
    pub name: String,
    pub address: String,
    pub body_address: String,
    pub author: Option<String>,
    pub roles: Vec<RoleDecl>,
    pub bounds: StateBounds,
    pub opener: Option<String>,
}
pub fn resolve(d: &mut Dialect) {
    if !d
        .state
        .as_ref()
        .is_some_and(|s| s.fields().any(|(_, r)| matches!(r, Rule::Context { .. })))
    {
        return;
    }
    let definition = Definition {
        name: d.name.clone(),
        address: crate::canonical::dialect_hash(d),
        body_address: crate::canonical::dialect_name(d),
        author: d.author.clone(),
        roles: d.roles.clone(),
        bounds: crate::r7::bounds_of(d),
        opener: d
            .causal_protocol
            .as_ref()
            .and_then(crate::state::opener_verb)
            .map(String::from),
    };
    if let Some(clause) = &mut d.state {
        for entry in &mut clause.entries {
            if let crate::state::Entry::Field {
                rule: Rule::Context {
                    definition: cache, ..
                },
                ..
            } = entry
            {
                *cache = Some(Box::new(definition.clone()));
            }
        }
    }
}
fn map(items: impl IntoIterator<Item = (String, Value)>) -> Value {
    Value::Map(
        items
            .into_iter()
            .collect::<BTreeMap<_, _>>()
            .into_iter()
            .map(|(k, v)| (Value::Str(k), v))
            .collect(),
    )
}
fn obj<const N: usize>(items: [(&str, Value); N]) -> Value {
    map(items.into_iter().map(|(k, v)| (k.into(), v)))
}
fn text(s: &str) -> Value {
    Value::Str(s.into())
}
fn lookup(value: &Value, key: &str) -> Value {
    if value.fault_evidence().is_some() {
        return value.clone();
    }
    match value {
        Value::Map(items) => items
            .iter()
            .find(|(k, _)| *k == text(key))
            .map(|(_, v)| v.clone())
            .unwrap_or(Value::Absent),
        _ => Value::Absent,
    }
}
pub fn roster_role(path: &[String]) -> Option<&str> {
    match path {
        [a, b, role] if a == "thread" && b == "roles" => Some(role),
        _ => None,
    }
}
pub fn stable_path(path: &[String]) -> bool {
    match path.first().map(String::as_str) {
        Some("dialect") => true,
        Some("thread") if path.len() >= 2 => path.get(1).is_some_and(|p| {
            matches!(p.as_str(), "id" | "root" | "initiator" | "opener" | "roles")
        }),
        _ => false,
    }
}

pub fn schema(path: &[String]) -> crate::state::StateType {
    use crate::state::{ScalarType as S, StateType as T};
    let string = || T::OptScalar(S::Str);
    let set = || T::Set(S::Str);
    let object = |fields: Vec<(&str, T)>| {
        T::Object(fields.into_iter().map(|(k, v)| (k.into(), v)).collect())
    };
    let dialect = object(alloc::vec![
        ("address", string()),
        ("body-address", string()),
        ("name", string()),
        ("author", string()),
        ("roles", T::Map(S::Str, Box::new(string()))),
        (
            "bounds",
            object(alloc::vec![
                ("max-fields", T::Int),
                ("max-list", T::Int),
                ("max-number", T::Int),
                ("max-string", T::Int)
            ])
        )
    ]);
    let thread = object(alloc::vec![
        ("id", string()),
        ("root", string()),
        ("initiator", string()),
        ("opener", string()),
        ("roles", T::Map(S::Str, Box::new(set())))
    ]);
    let observation = object(alloc::vec![("accepted-count", T::Int), ("frontier", set())]);
    let mut value = object(alloc::vec![
        ("dialect", dialect),
        ("thread", thread),
        ("observation", observation)
    ]);
    for key in path {
        value = match value {
            T::Object(fields) => fields
                .into_iter()
                .find(|(k, _)| k == key)
                .map(|(_, v)| v)
                .unwrap_or(T::Unknown),
            T::Map(_, v) => *v,
            _ => T::Unknown,
        };
    }
    value
}
impl Definition {
    pub fn valid_path(&self, path: &[String]) -> bool {
        let p: Vec<&str> = path.iter().map(String::as_str).collect();
        match p.as_slice() {
            [] | ["dialect"] | ["thread"] | ["observation"] => true,
            ["dialect", "address" | "body-address" | "name" | "author" | "roles" | "bounds"] => {
                true
            }
            ["dialect", "bounds", "max-fields" | "max-list" | "max-number" | "max-string"] => true,
            ["dialect", "roles", role] => self.roles.iter().any(|r| r.name == *role),
            ["thread", "id" | "root" | "initiator" | "opener" | "roles"] => true,
            ["thread", "roles", role] => self.roles.iter().any(|r| r.name == *role),
            ["observation", "accepted-count" | "frontier"] => true,
            _ => false,
        }
    }
    fn dialect(&self) -> Value {
        obj([
            ("name", text(&self.name)),
            ("address", text(&self.address)),
            ("body-address", text(&self.body_address)),
            (
                "author",
                self.author.as_deref().map(text).unwrap_or(Value::Absent),
            ),
            (
                "roles",
                map(self.roles.iter().map(|r| {
                    (
                        r.name.clone(),
                        text(match r.cardinality {
                            RoleCardinality::Singleton => "singleton",
                            RoleCardinality::Indexed => "indexed",
                        }),
                    )
                })),
            ),
            (
                "bounds",
                obj([
                    ("max-fields", Value::Int(self.bounds.max_fields as i128)),
                    ("max-list", Value::Int(self.bounds.max_list as i128)),
                    ("max-number", Value::Int(self.bounds.max_number as i128)),
                    ("max-string", Value::Int(self.bounds.max_string as i128)),
                ]),
            ),
        ])
    }
    fn cast(&self, root: &Act) -> Result<Cast, String> {
        let mut message = &root.message;
        loop {
            match message {
                crate::message::Message::Wrapped {
                    wrapper: crate::message::WrapperType::WithRoles,
                    params,
                    ..
                } => {
                    let cast = crate::role::parse_wrapper_cast(params, &self.roles)
                        .map_err(|e| e.to_string())?;
                    if cast
                        .dialect_pin
                        .as_ref()
                        .is_some_and(|pin| *pin != self.address)
                    {
                        return Err("wrong context dialect pin".into());
                    }
                    return Ok(cast);
                }
                crate::message::Message::Wrapped { content, .. } => message = content,
                crate::message::Message::Dialect { inner, .. } => message = inner,
                _ if self.roles.is_empty() => {
                    return Ok(Cast {
                        singleton: BTreeMap::new(),
                        indexed: BTreeMap::new(),
                        dialect_pin: None,
                    })
                }
                _ => return Err("context root is missing its sealed cast".into()),
            }
        }
    }
    fn thread(&self, acts: &[Act]) -> Value {
        let roots: Vec<&Act> = acts.iter().filter(|a| a.predecessors.is_empty()).collect();
        if roots.is_empty() {
            return Value::Absent;
        }
        let evidence = || roots.iter().map(|a| a.address.clone()).collect();
        let root = roots[0];
        if roots
            .iter()
            .any(|other| other.address != root.address || other.signer != root.signer)
        {
            return crate::state::conflict_top("incompatible thread roots or casts", evidence());
        }
        let casts: Vec<Result<Cast, String>> = roots.iter().map(|r| self.cast(r)).collect();
        if let Some(reason) = casts.iter().filter_map(|c| c.as_ref().err()).min() {
            return crate::state::conflict_top(reason, evidence());
        }
        let cast = casts[0].as_ref().unwrap();
        if casts.iter().any(|c| c.as_ref().ok() != Some(cast)) {
            return crate::state::conflict_top("incompatible thread roots or casts", evidence());
        }
        if acts
            .iter()
            .any(|a| a.simple().thread() != root.simple().thread())
        {
            return crate::state::conflict_top(
                "mixed thread context",
                acts.iter().map(|a| a.address.clone()).collect(),
            );
        }
        let roles = map(cast
            .singleton
            .iter()
            .map(|(r, k)| (r.clone(), Value::Set(alloc::vec![text(&k.0)])))
            .chain(cast.indexed.iter().map(|(r, ks)| {
                (
                    r.clone(),
                    Value::Set(ks.iter().map(|k| text(&k.0)).collect()),
                )
            })));
        let openers: BTreeMap<&str, &Act> = acts
            .iter()
            .filter(|a| self.opener.as_ref().is_some_and(|v| *v == a.verb))
            .map(|a| (a.address.as_str(), a))
            .collect();
        let opener = match openers.len() {
            0 => Value::Absent,
            1 => text(openers.keys().next().unwrap()),
            _ => crate::state::conflict_top(
                "opener fork",
                openers.keys().map(|s| s.to_string()).collect(),
            ),
        };
        obj([
            (
                "id",
                root.simple().thread().map(text).unwrap_or(Value::Absent),
            ),
            ("root", text(&root.address)),
            ("initiator", text(&root.signer)),
            ("opener", opener),
            ("roles", roles),
        ])
    }
    pub fn read(&self, path: &[String], acts: &[Act]) -> Value {
        let observation = || {
            obj([
                (
                    "accepted-count",
                    Value::Int(
                        acts.iter()
                            .map(|a| &a.address)
                            .collect::<BTreeSet<_>>()
                            .len() as i128,
                    ),
                ),
                (
                    "frontier",
                    Value::Set(
                        crate::state::frontier(acts)
                            .into_iter()
                            .map(Value::Str)
                            .collect(),
                    ),
                ),
            ])
        };
        let thread = || {
            let value = self.thread(acts);
            if path.is_empty() || path.len() == 1 {
                let opener = lookup(&value, "opener");
                if opener.fault_evidence().is_some() {
                    return opener;
                }
            }
            value
        };
        let full = match path.first().map(String::as_str) {
            Some("dialect") => self.dialect(),
            Some("thread") => thread(),
            Some("observation") => observation(),
            None => {
                let thread = thread();
                if thread.fault_evidence().is_some() {
                    return thread;
                }
                obj([
                    ("dialect", self.dialect()),
                    ("thread", thread),
                    ("observation", observation()),
                ])
            }
            _ => return Value::Absent,
        };
        path.iter()
            .skip(1)
            .fold(full, |value, key| lookup(&value, key))
    }
}
