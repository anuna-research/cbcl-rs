//! SPEC-038 CON-3803: finite lattice tables, recognized as data and verified
//! exhaustively before use. No user-supplied executable merge is accepted.
use crate::sexpr::{Atom, SExpr};
use alloc::boxed::Box;
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Definition {
    pub name: String,
    pub elements: Vec<String>,
    pub bottom: String,
    pub top: String,
    pub rows: Vec<(String, String, String)>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Row {
    pub key: String,
    pub value: SExpr,
    pub element: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Projection {
    pub stable: bool,
    pub rows: Vec<(String, SExpr)>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Lift {
    pub verb: String,
    pub lattice: String,
    pub rows: Vec<Row>,
    pub projection: Option<Projection>,
    /// Resolved from the clause, never included in the canonical signed body.
    pub table: Option<Box<Table>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Table {
    pub name: String,
    pub elements: Vec<String>,
    pub bottom: usize,
    pub top: usize,
    pub join: Vec<usize>,
}

impl Table {
    pub fn merge(&self, a: usize, b: usize) -> usize {
        self.join[a * self.elements.len() + b]
    }
    pub fn index(&self, name: &str) -> Option<usize> {
        self.elements.iter().position(|x| x == name)
    }
    pub fn le(&self, a: usize, b: usize) -> bool {
        self.merge(a, b) == b
    }
}

impl Definition {
    pub fn to_sexpr(&self) -> SExpr {
        let sym = |s: &str| SExpr::Atom(Atom::Symbol(s.into()));
        let mut elements = alloc::vec![sym("elements")];
        elements.extend(self.elements.iter().map(|x| sym(x)));
        let mut join = alloc::vec![sym("join")];
        join.extend(
            self.rows
                .iter()
                .map(|(a, b, c)| SExpr::List(alloc::vec![sym(a), sym(b), sym(c)])),
        );
        SExpr::List(alloc::vec![
            sym("lattice"),
            sym(&self.name),
            SExpr::List(elements),
            SExpr::List(alloc::vec![sym("bottom"), sym(&self.bottom)]),
            SExpr::List(alloc::vec![sym("top"), sym(&self.top)]),
            SExpr::List(join)
        ])
    }
    /// Compile only a total, single-valued table. The allocation is bounded by
    /// the supplied row count; a sparse declaration cannot expand quadratically.
    pub fn compile(&self) -> Result<Table, String> {
        let n = self.elements.len();
        if n == 0 {
            return Err("lattice elements cannot be empty".into());
        }
        let indices: BTreeMap<&str, usize> = self
            .elements
            .iter()
            .enumerate()
            .map(|(i, s)| (s.as_str(), i))
            .collect();
        if indices.len() != n {
            return Err("duplicate lattice element".into());
        }
        let index = |name: &str| {
            indices
                .get(name)
                .copied()
                .ok_or_else(|| format!("undeclared element '{name}'"))
        };
        let bottom = index(&self.bottom)?;
        let top = index(&self.top)?;
        if bottom == top {
            return Err("lattice bottom and conflict top must be distinct".into());
        }
        let mut rows = BTreeMap::new();
        for (a, b, c) in &self.rows {
            let (a, b, c) = (index(a)?, index(b)?, index(c)?);
            if rows.insert((a, b), c).is_some() {
                return Err(format!(
                    "duplicate join row: ({} {})",
                    self.elements[a], self.elements[b]
                ));
            }
        }
        let mut join = Vec::with_capacity(rows.len());
        for a in 0..n {
            for b in 0..n {
                join.push(*rows.get(&(a, b)).ok_or_else(|| {
                    format!(
                        "join not total: missing ({} {})",
                        self.elements[a], self.elements[b]
                    )
                })?);
            }
        }
        Ok(Table {
            name: self.name.clone(),
            elements: self.elements.clone(),
            bottom,
            top,
            join,
        })
    }

    pub fn validate(&self, max_elements: usize) -> Result<Table, String> {
        self.validate_counted(max_elements, || {})
    }

    fn validate_counted(
        &self,
        max_elements: usize,
        mut triple: impl FnMut(),
    ) -> Result<Table, String> {
        if self.elements.len() > max_elements {
            return Err(format!(
                "lattice '{}' exceeds max-list ({max_elements})",
                self.name
            ));
        }
        let t = self.compile()?;
        let n = t.elements.len();
        for a in 0..n {
            for b in 0..n {
                if t.merge(a, b) != t.merge(b, a) {
                    return Err(format!(
                        "join not commutative: ({} {}) != ({} {})",
                        t.elements[a], t.elements[b], t.elements[b], t.elements[a]
                    ));
                }
            }
        }
        for a in 0..n {
            for b in 0..n {
                for c in 0..n {
                    triple();
                    if t.merge(t.merge(a, b), c) != t.merge(a, t.merge(b, c)) {
                        return Err(format!(
                            "join not associative: ({} {} {})",
                            t.elements[a], t.elements[b], t.elements[c]
                        ));
                    }
                }
            }
        }
        for a in 0..n {
            if t.merge(a, a) != a {
                return Err(format!("join not idempotent: ({})", t.elements[a]));
            }
            if t.merge(a, t.bottom) != a || t.merge(t.bottom, a) != a {
                return Err(format!("bottom not identity: ({})", t.elements[a]));
            }
            if t.merge(a, t.top) != t.top || t.merge(t.top, a) != t.top {
                return Err(format!("top not absorbing: ({})", t.elements[a]));
            }
        }
        Ok(t)
    }
}

fn scalar(value: &SExpr) -> bool {
    matches!(
        value,
        SExpr::Atom(Atom::Str(_) | Atom::Num(_) | Atom::Bool(_))
    )
}

impl Lift {
    pub fn arguments(&self) -> Vec<SExpr> {
        let sym = |s: &str| SExpr::Atom(Atom::Symbol(s.into()));
        let mut rows = alloc::vec![sym("contribute")];
        rows.extend(self.rows.iter().map(|row| {
            SExpr::List(alloc::vec![
                SExpr::Atom(Atom::Keyword(row.key.clone())),
                row.value.clone(),
                sym(&row.element)
            ])
        }));
        let mut args = alloc::vec![
            sym(&self.verb),
            SExpr::List(alloc::vec![sym("into"), sym(&self.lattice)]),
            SExpr::List(rows)
        ];
        if let Some(project) = &self.projection {
            let mut p = alloc::vec![sym("project")];
            if project.stable {
                p.push(sym("stable"));
            }
            p.push(SExpr::List(
                project
                    .rows
                    .iter()
                    .map(|(element, value)| SExpr::List(alloc::vec![sym(element), value.clone()]))
                    .collect(),
            ));
            args.push(SExpr::List(p));
        }
        args
    }
    pub fn evaluate<'a>(
        &self,
        acts: impl IntoIterator<Item = &'a crate::state::Act>,
    ) -> crate::state::Value {
        let Some(table) = &self.table else {
            return crate::state::Value::Absent;
        };
        let mut index = table.bottom;
        let mut evidence = BTreeSet::new();
        for act in acts {
            let value = self.contribution(table, &act.fields);
            if value != table.bottom {
                evidence.insert(act.address.clone());
            }
            index = table.merge(index, value);
        }
        if index == table.top {
            return crate::state::conflict_top(
                "finite lattice conflict",
                evidence.into_iter().collect(),
            );
        }
        self.project(table, index)
    }

    pub fn validate(&self, table: &Table) -> Result<(), String> {
        for row in &self.rows {
            if !scalar(&row.value) {
                return Err(format!("contribution :{} must compare a scalar", row.key));
            }
            if table.index(&row.element).is_none() {
                return Err(format!(
                    "contribution targets undeclared element '{}'",
                    row.element
                ));
            }
        }
        if let Some(project) = &self.projection {
            let mut outputs = BTreeMap::new();
            for (element, value) in &project.rows {
                let Some(i) = table.index(element) else {
                    return Err(format!("projection names undeclared element '{element}'"));
                };
                if !scalar(value) || outputs.insert(i, value).is_some() {
                    return Err(format!("invalid or duplicate projection row '{element}'"));
                }
            }
            for (i, element) in table.elements.iter().enumerate() {
                if !outputs.contains_key(&i) {
                    return Err(format!("projection not total: missing '{element}'"));
                }
            }
            if project.stable {
                for a in 0..table.elements.len() {
                    for b in 0..table.elements.len() {
                        if table.le(a, b) {
                            let ordered = match (outputs[&a], outputs[&b]) {
                                (SExpr::Atom(Atom::Num(x)), SExpr::Atom(Atom::Num(y))) => x <= y,
                                (SExpr::Atom(Atom::Bool(x)), SExpr::Atom(Atom::Bool(y))) => {
                                    !*x || *y
                                }
                                _ => false,
                            };
                            if !ordered {
                                return Err(format!(
                                    "stable projection not monotone: ({} {})",
                                    table.elements[a], table.elements[b]
                                ));
                            }
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// Every matching row contributes; simultaneous matches are joined.
    pub fn contribution(&self, table: &Table, fields: &BTreeMap<String, SExpr>) -> usize {
        self.rows
            .iter()
            .filter(|row| fields.get(&row.key) == Some(&row.value))
            .filter_map(|row| table.index(&row.element))
            .fold(table.bottom, |a, b| table.merge(a, b))
    }

    pub fn project(&self, table: &Table, element: usize) -> crate::state::Value {
        project(&self.projection, table, element)
    }
}

pub fn project(
    projection: &Option<Projection>,
    table: &Table,
    element: usize,
) -> crate::state::Value {
    projection
        .as_ref()
        .and_then(|p| {
            p.rows
                .iter()
                .find(|(name, _)| *name == table.elements[element])
        })
        .map(|(_, value)| crate::state::Value::from_sexpr(value))
        .unwrap_or_else(|| crate::state::Value::Str(table.elements[element].clone()))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn verification_visits_exactly_n_cubed_associativity_triples() {
        let n = 64;
        let elements: Vec<String> = (0..n).map(|i| format!("e{i}")).collect();
        let mut rows = Vec::new();
        for a in 0..n {
            for b in 0..n {
                rows.push((
                    elements[a].clone(),
                    elements[b].clone(),
                    elements[a.max(b)].clone(),
                ));
            }
        }
        let d = Definition {
            name: "chain".into(),
            bottom: elements[0].clone(),
            top: elements[n - 1].clone(),
            elements,
            rows,
        };
        let mut visited = 0;
        d.validate_counted(n, || visited += 1).unwrap();
        assert_eq!(visited, n * n * n);
    }
}
