//! SPEC-026: declaration defaults. Resolving a committee grants no certification.
#![forbid(unsafe_code)]
use crate::sexpr::{Atom, SExpr};
use alloc::{
    string::{String, ToString},
    vec::Vec,
};

#[derive(Debug, Clone, PartialEq, Eq, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Certification {
    #[default]
    HostGate,
    QuorumBudget {
        validators: Option<Vec<String>>,
        faults: Option<u32>,
    },
}
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Committee {
    pub validators: Vec<String>,
    pub faults: u32,
    pub quorum: usize,
}
fn roster(keys: &[String]) -> Result<Vec<String>, String> {
    if keys.is_empty() {
        return Err("validator roster must not be empty".into());
    }
    let mut result = keys.to_vec();
    if result.iter().any(|k| {
        !k.starts_with('@')
            || k.len() < 2
            || !k
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || "_-./!?+*<>=@".contains(c))
    }) {
        return Err("validators must be whole @key symbols".into());
    }
    result.sort();
    if result.windows(2).any(|w| w[0] == w[1]) {
        return Err("duplicate validator".into());
    }
    Ok(result)
}
impl Committee {
    pub fn new(validators: &[String], faults: Option<u32>) -> Result<Self, String> {
        let validators = roster(validators)?;
        let n = validators.len();
        let f = match faults {
            Some(f) => f,
            None => u32::try_from((n - 1) / 3).map_err(|_| "committee too large")?,
        };
        let f_usize = usize::try_from(f).map_err(|_| "fault bound too large")?;
        if f_usize.checked_mul(3).and_then(|x| x.checked_add(1)) != Some(n) {
            return Err("quorum-budget requires exactly 3f+1 validators".into());
        }
        Ok(Self {
            validators,
            faults: f,
            quorum: 2 * f_usize + 1,
        })
    }
    pub fn contains(&self, key: &str) -> bool {
        self.validators
            .binary_search_by(|k| k.as_str().cmp(key))
            .is_ok()
    }
}
impl Certification {
    pub fn quorum_budget(
        validators: Option<Vec<String>>,
        faults: Option<u32>,
    ) -> Result<Self, String> {
        if let Some(keys) = validators {
            let c = Committee::new(&keys, faults)?;
            Ok(Self::QuorumBudget {
                validators: Some(c.validators),
                faults: Some(c.faults),
            })
        } else {
            Ok(Self::QuorumBudget {
                validators: None,
                faults,
            })
        }
    }
    pub fn validate(&self) -> Result<(), String> {
        if let Self::QuorumBudget {
            validators: Some(keys),
            faults,
        } = self
        {
            Committee::new(keys, *faults)?;
        }
        Ok(())
    }
    /// `instance` is trusted, authenticated deployment configuration, not a request field.
    pub fn resolve(&self, instance: Option<&[String]>) -> Result<Committee, String> {
        let Self::QuorumBudget { validators, faults } = self else {
            return Err("counter uses host-gate certification".into());
        };
        let keys = validators
            .as_deref()
            .or(instance)
            .ok_or("quorum-budget requires a pinned instance validator roster")?;
        let c = Committee::new(keys, *faults)?;
        if validators.is_some() {
            if let Some(bound) = instance {
                if roster(bound)? != c.validators {
                    return Err("instance validator roster differs from dialect".into());
                }
            }
        }
        Ok(c)
    }
    pub fn is_quorum(&self) -> bool {
        matches!(self, Self::QuorumBudget { .. })
    }
    /// Omitted/explicit legacy mode retain identical pre-extension canonical bytes.
    pub fn canonical_option(&self) -> Option<SExpr> {
        let Self::QuorumBudget { validators, faults } = self else {
            return None;
        };
        let symbol = |s: &str| SExpr::Atom(Atom::Symbol(s.to_string()));
        let mut parts = alloc::vec![symbol("certification"), symbol("quorum-budget")];
        if let Some(keys) = validators {
            let mut ordered = keys.clone();
            ordered.sort();
            let mut xs = alloc::vec![symbol("validators")];
            xs.extend(ordered.iter().map(|key| symbol(key)));
            parts.push(SExpr::List(xs));
        }
        let bound = if let Some(keys) = validators {
            Committee::new(keys, *faults).ok().map(|c| c.faults)
        } else {
            *faults
        };
        if let Some(f) = bound {
            parts.push(SExpr::List(alloc::vec![
                symbol("faults"),
                SExpr::Atom(Atom::Num(i64::from(f)))
            ]));
        }
        Some(SExpr::List(parts))
    }
}
