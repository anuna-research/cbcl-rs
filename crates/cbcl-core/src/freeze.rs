//! SPEC-038 CON-3802: exact reads of accepted causal cuts.
//!
//! Pure orchestration over the existing field evaluators. Memoization keys
//! include the scope and field; dependencies always point to earlier fields.
//! Raw initializer/resource faults are checked before taking a historical cut,
//! so freezing cannot conceal an already inconsistent accepted history.
use crate::protocol::CausalProtocol;
use crate::state::{self, Act, Entry, FreezePolicy, Rule, StateClause, Value};
use alloc::collections::{BTreeMap, BTreeSet, VecDeque};
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use hashbrown::{HashMap, HashSet};

#[derive(Clone)]
struct Plan {
    root: Option<String>,
    scope: usize,
    late: HashSet<String>,
    fault: Option<Value>,
    policy: FreezePolicy,
}

/// Linear graph traversal under the core's hash-index lookup model. Ready
/// order is irrelevant: causal cuts are sets and evidence is rendered sorted.
fn order(acts: &[Act]) -> Vec<&Act> {
    let mut index = HashMap::new();
    let mut unique = Vec::new();
    for a in acts {
        if !index.contains_key(a.address.as_str()) {
            index.insert(a.address.as_str(), unique.len());
            unique.push(a);
        }
    }
    let mut incoming = alloc::vec![0usize; unique.len()];
    let mut children = alloc::vec![Vec::new(); unique.len()];
    for (i, act) in unique.iter().enumerate() {
        for p in &act.predecessors {
            if let Some(&parent) = index.get(p.as_str()) {
                incoming[i] += 1;
                children[parent].push(i);
            }
        }
    }
    let mut ready: VecDeque<usize> = incoming
        .iter()
        .enumerate()
        .filter_map(|(i, n)| (*n == 0).then_some(i))
        .collect();
    let mut out = Vec::new();
    while let Some(i) = ready.pop_front() {
        out.push(unique[i]);
        for &child in &children[i] {
            incoming[child] -= 1;
            if incoming[child] == 0 {
                ready.push_back(child);
            }
        }
    }
    out
}

fn past(root: &str, ordered: &[&Act]) -> HashSet<String> {
    let by_address: HashMap<&str, &Act> =
        ordered.iter().map(|a| (a.address.as_str(), *a)).collect();
    let mut found = HashSet::new();
    let mut pending = alloc::vec![root.to_string()];
    while let Some(addr) = pending.pop() {
        if !found.insert(addr.clone()) {
            continue;
        }
        if let Some(a) = by_address.get(addr.as_str()) {
            pending.extend(
                a.predecessors
                    .iter()
                    .filter(|p| by_address.contains_key(p.as_str()))
                    .cloned(),
            );
        }
    }
    found
}

fn verbs(clause: &StateClause, rule: &Rule) -> Vec<String> {
    let mut rule = rule;
    let mut seen = BTreeSet::new();
    loop {
        match rule {
            Rule::Context { path, definition }
                if path.len() == 1 && path[0] == "thread"
                    || path.iter().map(String::as_str).eq(["thread", "opener"]) =>
            {
                return definition
                    .as_ref()
                    .and_then(|d| d.opener.clone())
                    .into_iter()
                    .collect();
            }
            Rule::Histogram { field } | Rule::Sum { field } if seen.insert(field) => {
                match clause.rule_of(field) {
                    Some(source) => rule = source,
                    None => return Vec::new(),
                }
            }
            _ => return rule.verbs().iter().map(|s| (*s).to_string()).collect(),
        }
    }
}

fn contributors(clause: &StateClause, field: &str, acts: &[Act]) -> HashSet<String> {
    let Some(rule) = clause.rule_of(field) else {
        return HashSet::new();
    };
    if matches!(rule,Rule::Context {path,..} if path.is_empty() || path.first().is_some_and(|p|p=="observation"))
    {
        // Observation metadata depends on every accepted act, even when its
        // application contribution is excluded by a data domain.
        return acts.iter().map(|a| a.address.clone()).collect();
    }
    state::contribution_addresses(clause, acts, &verbs(clause, rule))
}

struct Reader<'a> {
    clause: &'a StateClause,
    protocol: Option<&'a CausalProtocol>,
    scopes: Vec<Vec<Act>>,
    plans: BTreeMap<String, Plan>,
    values: BTreeMap<(usize, String), Value>,
}

impl Reader<'_> {
    fn field(&mut self, scope: usize, name: &str) -> Value {
        let key = (scope, name.to_string());
        if let Some(v) = self.values.get(&key) {
            return v.clone();
        }
        let Some(rule) = self.clause.rule_of(name).cloned() else {
            return Value::Absent;
        };
        let dependency = match &rule {
            Rule::Histogram { field } | Rule::Sum { field } => Some(field.clone()),
            _ => None,
        };
        let mut done = Vec::new();
        if let Some(source) = dependency {
            let v = self.field(scope, &source);
            done.push((source, v.unfrozen().clone()));
        }
        let normal = state::scoped_rule(
            self.clause,
            self.protocol,
            &self.scopes[scope],
            &rule,
            &done,
        );
        let plan = self.plans.get(name).cloned();
        let freeze_fault = plan.as_ref().and_then(|p| p.fault.clone()).or_else(|| {
            let p = plan.as_ref()?;
            if p.policy == FreezePolicy::Fault && !p.late.is_empty() {
                Some(state::conflict_top(
                    "write after or concurrent with freeze",
                    p.root
                        .iter()
                        .cloned()
                        .chain(p.late.iter().cloned())
                        .collect(),
                ))
            } else {
                None
            }
        });
        let value = match (normal.fault_evidence(), freeze_fault) {
            (Some(mut evidence), Some(fault)) => {
                evidence.extend(fault.fault_evidence().unwrap_or_default());
                state::conflict_top("state conflicts", evidence)
            }
            (Some(_), None) => normal,
            (None, Some(fault)) => fault,
            (None, None) => match plan {
                Some(plan)
                    if plan.root.as_ref().is_some_and(|root| {
                        self.scopes[scope].iter().any(|a| a.address == *root)
                    }) =>
                {
                    let root = plan.root.unwrap();
                    let value = if scope == plan.scope {
                        normal
                    } else {
                        self.field(plan.scope, name).unfrozen().clone()
                    };
                    let mut excluded = self.scopes[scope]
                        .iter()
                        .filter(|a| plan.late.contains(&a.address))
                        .map(|a| a.address.clone())
                        .collect::<Vec<_>>();
                    state::sort_addresses(&mut excluded);
                    Value::Map(alloc::vec![
                        (Value::Str("frozen".into()), Value::Str(root)),
                        (
                            Value::Str("superseded".into()),
                            Value::List(excluded.into_iter().map(Value::Str).collect())
                        ),
                        (Value::Str("value".into()), value),
                    ])
                }
                _ => normal,
            },
        };
        self.values.insert(key, value.clone());
        value
    }
}

pub(crate) fn fold(
    clause: &StateClause,
    protocol: Option<&CausalProtocol>,
    acts: &[Act],
) -> Vec<(String, Value)> {
    let ordered = order(acts);
    let unique: Vec<Act> = ordered.iter().map(|a| (*a).clone()).collect();
    let mut scopes = alloc::vec![unique.clone()];
    let mut cuts: BTreeMap<String, usize> = BTreeMap::new();
    let mut plans = BTreeMap::new();
    for (field, verb, policy) in clause.freezes() {
        let mut seen: HashMap<&str, bool> = HashMap::new();
        let mut frontier = Vec::new();
        for a in &ordered {
            let earlier = a
                .predecessors
                .iter()
                .any(|p| seen.get(p.as_str()).copied().unwrap_or(false));
            if a.verb == verb && !earlier {
                frontier.push(a.address.clone());
            }
            seen.insert(&a.address, earlier || a.verb == verb);
        }
        if frontier.len() > 1 {
            let mut evidence = frontier.clone();
            if policy == FreezePolicy::Fault {
                let candidates = contributors(clause, field, &unique);
                for root in &frontier {
                    let cut = past(root, &ordered);
                    evidence.extend(candidates.iter().filter(|a| !cut.contains(*a)).cloned());
                }
            }
            plans.insert(
                field.to_string(),
                Plan {
                    root: None,
                    scope: 0,
                    late: HashSet::new(),
                    fault: Some(state::conflict_top("concurrent freezes", evidence)),
                    policy,
                },
            );
        } else if let Some(root) = frontier.pop() {
            let cut = past(&root, &ordered);
            let scope = *cuts.entry(root.clone()).or_insert_with(|| {
                scopes.push(
                    unique
                        .iter()
                        .filter(|a| cut.contains(&a.address))
                        .cloned()
                        .collect(),
                );
                scopes.len() - 1
            });
            let late = contributors(clause, field, &unique)
                .into_iter()
                .filter(|a| !cut.contains(a))
                .collect();
            plans.insert(
                field.to_string(),
                Plan {
                    root: Some(root),
                    scope,
                    late,
                    fault: None,
                    policy,
                },
            );
        }
    }
    let mut reader = Reader {
        clause,
        protocol,
        scopes,
        plans,
        values: BTreeMap::new(),
    };
    let mut out = Vec::new();
    for entry in &clause.entries {
        match entry {
            Entry::Field { name, .. } => out.push((name.clone(), reader.field(0, name))),
            Entry::Threshold {
                name,
                field,
                elements,
            } => {
                let value = reader.field(0, field);
                let scope = if value.fault_evidence().is_some() {
                    0
                } else {
                    reader.plans.get(field).map(|p| p.scope).unwrap_or(0)
                };
                let ctx = crate::lattice::Ctx::new(clause, &reader.scopes[scope]);
                let result = state::threshold_read(
                    &ctx,
                    clause,
                    field,
                    elements,
                    &[(field.clone(), value.unfrozen().clone())],
                );
                out.push((name.clone(), result));
            }
            _ => {}
        }
    }
    out
}
