//! Role layer types and parsing (SPEC-014).
//!
//! Types and SExpr-level recognisers for the role layer: role declarations
//! (REQ-600, CON-600), per-performative `:from`/`:to` annotations (REQ-601,
//! CON-600), and the thread cast nominated by a `with-roles` wrapper
//! (REQ-611, CON-601). Fail-closed: malformed annotations are rejected, never
//! repaired (LangSec principle 4).
//!
//! The indexed-role marker is the head-position form `(* name)` (ADR-600).
//! Key identifiers ([`AgentKey`]) are whole symbols (e.g. `@alice`), compared
//! for equality as strings; cryptographic validity of the signature binding a
//! message to its key is an R4-layer precondition (CON-602).

#![forbid(unsafe_code)]

use crate::sexpr::{Atom, SExpr};
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

/// How many occupants a role admits (SPEC-014 §Terminology).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum RoleCardinality {
    /// Exactly one occupant, pinned by the cast (REQ-612).
    Singleton,
    /// Many occupants, membership sealed at thread open (REQ-614);
    /// declared `(* name)` (ADR-600).
    Indexed,
}

/// A declared role (CON-600, REQ-600).
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct RoleDecl {
    pub name: String,
    pub cardinality: RoleCardinality,
}

/// Per-performative `:from`/`:to` annotation (CON-600, REQ-601).
///
/// `to` is a set from the start: bare symbol = singleton, list = multicast,
/// `()` = empty (a terminal act addressed to no other role).
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct RoleAnnotation {
    pub from: String,
    pub to: BTreeSet<String>,
}

/// Key identifier as it appears in casts and signed messages (e.g. `@alice`).
///
/// Equality is whole-symbol string equality; cryptographic validity of the
/// signature that binds a message to this identifier is an R4-layer
/// precondition, outside this module (CON-602).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct AgentKey(pub String);

/// The assignment of agents to roles for one thread (CON-601, REQ-611).
///
/// Nominated by the initiator at the causal root; tamper-evident because the
/// root's content hash anchors every subsequent `:caused-by` link. Indexed
/// memberships are *sealed*: occupant-dependent checks read them exclusively
/// from here (REQ-614).
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Cast {
    pub singleton: BTreeMap<String, AgentKey>,
    pub indexed: BTreeMap<String, BTreeSet<AgentKey>>,
    /// REQ-628: the `sha256:<hex64>` content hash of the dialect that
    /// governs the thread, from the wrapper's optional `:dialect` field.
    /// `None` for an unpinned root (accepted during the spec's
    /// warn-then-reject transition window).
    #[cfg_attr(feature = "serde", serde(default))]
    pub dialect_pin: Option<String>,
}

impl Cast {
    /// Whether `key` may occupy `role` under this cast.
    pub fn admits(&self, role: &str, key: &AgentKey) -> bool {
        match self.singleton.get(role) {
            Some(k) => k == key,
            None => self.indexed.get(role).is_some_and(|ks| ks.contains(key)),
        }
    }
}

/// A `(role, occupant)` pair; `occupant` is `None` for singleton roles
/// (CON-602).
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Endpoint {
    pub role: String,
    pub occupant: Option<AgentKey>,
}

/// R6 violation (CON-603): one variant per rejectable condition, each
/// carrying the names needed to locate the defect.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum R6Violation {
    /// REQ-601: a protocol performative lacks `:from` or `:to`.
    MissingFromTo { performative: String },
    /// REQ-602: `:from`/`:to` names a role absent from `:roles`.
    UndeclaredRole { performative: String, role: String },
    /// REQ-602: `:from`/`:to` present while no `:roles` is declared.
    StrayAnnotation { performative: String },
    /// REQ-603: a choice whose members do not share one sender role.
    ChooserIncoherent { members: Vec<String> },
    /// REQ-604: an endpoint role of `performative` is not an endpoint role
    /// of `predecessor`.
    NotCausallyLocal {
        performative: String,
        predecessor: String,
        role: String,
    },
    /// REQ-605: a declared role unreachable from `begin`.
    UnreachableRole { role: String },
    /// CON-600: malformed `:roles` value.
    MalformedRoles { detail: String },
    /// CON-600: malformed `:from`/`:to` value.
    MalformedFromTo {
        performative: String,
        detail: String,
    },
    /// CON-601: malformed `with-roles` bindings.
    MalformedCast { detail: String },
    /// CON-601: a cast binding names a role not declared in `:roles`.
    UnknownRole { role: String },
    /// CON-601: a singleton role bound to a number of keys other than one.
    ArityMismatch { role: String, keys: usize },
    /// REQ-608: per-occupant causal locality fails at `occupant`.
    PerOccupantLocalityFailure {
        performative: String,
        occupant: String,
    },
    /// REQ-628: the root's `:dialect` pin differs from the installed
    /// dialect's content hash.
    DialectPinMismatch { pinned: String, installed: String },
}

impl fmt::Display for R6Violation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            R6Violation::MissingFromTo { performative } => write!(
                f,
                "R6 violation: performative '{performative}' lacks :from or :to (REQ-601)"
            ),
            R6Violation::UndeclaredRole { performative, role } => write!(
                f,
                "R6 violation: performative '{performative}' names undeclared role '{role}' (REQ-602)"
            ),
            R6Violation::StrayAnnotation { performative } => write!(
                f,
                "R6 violation: performative '{performative}' carries :from/:to but the dialect declares no :roles (REQ-602)"
            ),
            R6Violation::ChooserIncoherent { members } => write!(
                f,
                "R6 violation: choice {members:?} has no common sender role (REQ-603)"
            ),
            R6Violation::NotCausallyLocal {
                performative,
                predecessor,
                role,
            } => write!(
                f,
                "R6 violation: role '{role}' is an endpoint of '{performative}' but not of its predecessor '{predecessor}' (REQ-604)"
            ),
            R6Violation::UnreachableRole { role } => write!(
                f,
                "R6 violation: role '{role}' is not an endpoint of any performative reachable from begin (REQ-605)"
            ),
            R6Violation::MalformedRoles { detail } => {
                write!(f, "R6 violation: malformed :roles — {detail} (CON-600)")
            }
            R6Violation::MalformedFromTo {
                performative,
                detail,
            } => write!(
                f,
                "R6 violation: malformed :from/:to on '{performative}' — {detail} (CON-600)"
            ),
            R6Violation::MalformedCast { detail } => {
                write!(f, "R6 violation: malformed cast — {detail} (CON-601)")
            }
            R6Violation::UnknownRole { role } => write!(
                f,
                "R6 violation: cast binds unknown role '{role}' (CON-601)"
            ),
            R6Violation::ArityMismatch { role, keys } => write!(
                f,
                "R6 violation: singleton role '{role}' bound to {keys} keys (CON-601)"
            ),
            R6Violation::PerOccupantLocalityFailure {
                performative,
                occupant,
            } => write!(
                f,
                "R6 violation: '{performative}' fails per-occupant causal locality at occupant '{occupant}' (REQ-608)"
            ),
            R6Violation::DialectPinMismatch { pinned, installed } => write!(
                f,
                "R6 violation: root pins dialect '{pinned}' but the installed dialect hashes to '{installed}' (REQ-628)"
            ),
        }
    }
}

/// Parse the value of a `:roles` attribute (CON-600, REQ-600).
///
/// `(auctioneer (* bidder))` → `[auctioneer: Singleton, bidder: Indexed]`.
/// Rejects (fail closed): a non-list value, an empty list, non-symbol
/// entries, a marker form that is not exactly `(* name)`, and duplicate role
/// names.
pub fn parse_roles(roles_value: &SExpr) -> Result<Vec<RoleDecl>, R6Violation> {
    let items = match roles_value {
        SExpr::List(items) if !items.is_empty() => items,
        SExpr::List(_) => {
            return Err(R6Violation::MalformedRoles {
                detail: String::from("empty :roles ()"),
            })
        }
        _ => {
            return Err(R6Violation::MalformedRoles {
                detail: String::from(":roles value is not a list"),
            })
        }
    };
    let mut decls: Vec<RoleDecl> = Vec::with_capacity(items.len());
    for item in items {
        let decl = match item {
            SExpr::Atom(Atom::Symbol(name)) => RoleDecl {
                name: name.clone(),
                cardinality: RoleCardinality::Singleton,
            },
            SExpr::List(marker) => match marker.as_slice() {
                [SExpr::Atom(Atom::Symbol(star)), SExpr::Atom(Atom::Symbol(name))]
                    if star == "*" =>
                {
                    RoleDecl {
                        name: name.clone(),
                        cardinality: RoleCardinality::Indexed,
                    }
                }
                _ => {
                    return Err(R6Violation::MalformedRoles {
                        detail: format!(
                            "role declaration must be a symbol or (* name), got {item}"
                        ),
                    })
                }
            },
            _ => {
                return Err(R6Violation::MalformedRoles {
                    detail: format!("role declaration must be a symbol or (* name), got {item}"),
                })
            }
        };
        if decls.iter().any(|d| d.name == decl.name) {
            return Err(R6Violation::MalformedRoles {
                detail: format!("duplicate role name '{}'", decl.name),
            });
        }
        decls.push(decl);
    }
    Ok(decls)
}

/// Parse the value of a `:from` annotation: exactly one role symbol
/// (CON-600).
pub fn parse_from(performative: &str, from_value: &SExpr) -> Result<String, R6Violation> {
    match from_value {
        SExpr::Atom(Atom::Symbol(role)) => Ok(role.clone()),
        other => Err(R6Violation::MalformedFromTo {
            performative: String::from(performative),
            detail: format!(":from must be exactly one role symbol, got {other}"),
        }),
    }
}

/// Parse the value of a `:to` annotation into a recipient set (CON-600):
/// bare symbol = singleton set, list = multicast, `()` = empty. Rejects
/// non-symbol members and duplicate members.
pub fn parse_recipient_set(
    performative: &str,
    to_value: &SExpr,
) -> Result<BTreeSet<String>, R6Violation> {
    match to_value {
        SExpr::Atom(Atom::Symbol(role)) => {
            let mut set = BTreeSet::new();
            set.insert(role.clone());
            Ok(set)
        }
        SExpr::List(items) => {
            let mut set = BTreeSet::new();
            for item in items {
                let SExpr::Atom(Atom::Symbol(role)) = item else {
                    return Err(R6Violation::MalformedFromTo {
                        performative: String::from(performative),
                        detail: format!(":to members must be role symbols, got {item}"),
                    });
                };
                if !set.insert(role.clone()) {
                    return Err(R6Violation::MalformedFromTo {
                        performative: String::from(performative),
                        detail: format!("duplicate :to member '{role}'"),
                    });
                }
            }
            Ok(set)
        }
        other => Err(R6Violation::MalformedFromTo {
            performative: String::from(performative),
            detail: format!(":to must be a role symbol or a list, got {other}"),
        }),
    }
}

/// Parse a `with-roles` bindings list into a [`Cast`] (CON-601, REQ-611).
///
/// Every declared role must be bound exactly once (a cast *assigns* each
/// role, REQ-611); a singleton role takes exactly one key
/// ([`R6Violation::ArityMismatch`] otherwise); an indexed role takes one or
/// more keys (its sealed membership, REQ-614); an undeclared role is
/// [`R6Violation::UnknownRole`].
pub fn parse_cast(bindings: &SExpr, roles: &[RoleDecl]) -> Result<Cast, R6Violation> {
    let SExpr::List(items) = bindings else {
        return Err(R6Violation::MalformedCast {
            detail: String::from("bindings must be a list of (role key+) forms"),
        });
    };
    let mut cast = Cast {
        singleton: BTreeMap::new(),
        indexed: BTreeMap::new(),
        dialect_pin: None,
    };
    for item in items {
        let SExpr::List(binding) = item else {
            return Err(R6Violation::MalformedCast {
                detail: format!("binding must be a (role key+) list, got {item}"),
            });
        };
        let [SExpr::Atom(Atom::Symbol(role_name)), keys @ ..] = binding.as_slice() else {
            return Err(R6Violation::MalformedCast {
                detail: format!("binding must start with a role symbol, got {item}"),
            });
        };
        let Some(decl) = roles.iter().find(|d| &d.name == role_name) else {
            return Err(R6Violation::UnknownRole {
                role: role_name.clone(),
            });
        };
        if cast.singleton.contains_key(role_name) || cast.indexed.contains_key(role_name) {
            return Err(R6Violation::MalformedCast {
                detail: format!("duplicate binding for role '{role_name}'"),
            });
        }
        let mut key_set: BTreeSet<AgentKey> = BTreeSet::new();
        for key in keys {
            let SExpr::Atom(Atom::Symbol(k)) = key else {
                return Err(R6Violation::MalformedCast {
                    detail: format!("key must be a symbol, got {key}"),
                });
            };
            if !key_set.insert(AgentKey(k.clone())) {
                return Err(R6Violation::MalformedCast {
                    detail: format!("duplicate key '{k}' for role '{role_name}'"),
                });
            }
        }
        match decl.cardinality {
            RoleCardinality::Singleton => {
                if key_set.len() != 1 {
                    return Err(R6Violation::ArityMismatch {
                        role: role_name.clone(),
                        keys: key_set.len(),
                    });
                }
                let key = key_set.into_iter().next().expect("len == 1");
                cast.singleton.insert(role_name.clone(), key);
            }
            RoleCardinality::Indexed => {
                if key_set.is_empty() {
                    return Err(R6Violation::MalformedCast {
                        detail: format!("indexed role '{role_name}' bound to no keys"),
                    });
                }
                cast.indexed.insert(role_name.clone(), key_set);
            }
        }
    }
    for decl in roles {
        let bound =
            cast.singleton.contains_key(&decl.name) || cast.indexed.contains_key(&decl.name);
        if !bound {
            return Err(R6Violation::MalformedCast {
                detail: format!("declared role '{}' is not bound by the cast", decl.name),
            });
        }
    }
    Ok(cast)
}

/// Length of the lowercase-hex digest in a `sha256:<hex64>` pin (REQ-628).
const PIN_HEX_LEN: usize = 64;

/// Parse the value of a `with-roles` `:dialect` field (REQ-628): exactly
/// the symbol `sha256:<lowercase-hex64>`, the form [`Dialect::hash`] takes
/// at install. Fail closed (LangSec principle 4): a bad prefix, a wrong
/// digest length, or a non-hex character is rejected, never repaired.
///
/// [`Dialect::hash`]: crate::dialect::Dialect::hash
pub fn parse_dialect_pin(value: &SExpr) -> Result<String, R6Violation> {
    let SExpr::Atom(Atom::Symbol(pin)) = value else {
        return Err(R6Violation::MalformedCast {
            detail: format!(":dialect value must be a sha256:<hex64> symbol, got {value}"),
        });
    };
    let Some(hex) = pin.strip_prefix("sha256:") else {
        return Err(R6Violation::MalformedCast {
            detail: format!(":dialect value must start with 'sha256:', got '{pin}'"),
        });
    };
    if hex.len() != PIN_HEX_LEN || !hex.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f')) {
        return Err(R6Violation::MalformedCast {
            detail: format!(
                ":dialect digest must be exactly {PIN_HEX_LEN} lowercase hex characters, got '{hex}'"
            ),
        });
    }
    Ok(pin.clone())
}

/// Parse a `with-roles` wrapper's parameter list into a [`Cast`] (CON-601,
/// REQ-628): the bindings list, optionally followed by
/// `:dialect sha256:<hex64>` in that fixed position. Any other shape —
/// extra fields, a misplaced pin, an unknown keyword — is rejected, never
/// repaired (LangSec principle 4).
pub fn parse_wrapper_cast(params: &[SExpr], roles: &[RoleDecl]) -> Result<Cast, R6Violation> {
    let (bindings, pin) = match params {
        [bindings] => (bindings, None),
        [bindings, SExpr::Atom(Atom::Keyword(k)), value] if k == "dialect" => {
            (bindings, Some(parse_dialect_pin(value)?))
        }
        _ => {
            return Err(R6Violation::MalformedCast {
                detail: String::from(
                    "with-roles wrapper must carry exactly one bindings list, \
                     optionally followed by :dialect sha256:<hex64> (CON-601, REQ-628)",
                ),
            })
        }
    };
    let mut cast = parse_cast(bindings, roles)?;
    cast.dialect_pin = pin;
    Ok(cast)
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::string::ToString;
    use alloc::vec;

    fn sx(s: &str) -> SExpr {
        s.parse().expect("test fixture parses")
    }

    // ---- R6Violation Display (CON-603: violations are Display-formatted
    // like ProtocolViolation, carrying the names needed to locate the
    // defect) ----

    #[test]
    fn violation_display_carries_locating_names() {
        use alloc::string::ToString as _;
        let v = R6Violation::NotCausallyLocal {
            performative: "dispatch".to_string(),
            predecessor: "accept".to_string(),
            role: "warehouse".to_string(),
        };
        let s = alloc::format!("{v}");
        assert!(s.contains("dispatch") && s.contains("accept") && s.contains("warehouse"));
        assert!(s.contains("REQ-604"));

        let a = R6Violation::ArityMismatch {
            role: "auctioneer".to_string(),
            keys: 2,
        };
        let s = alloc::format!("{a}");
        assert!(s.contains("auctioneer") && s.contains('2') && s.contains("CON-601"));
    }

    fn auction_roles() -> Vec<RoleDecl> {
        vec![
            RoleDecl {
                name: "auctioneer".to_string(),
                cardinality: RoleCardinality::Singleton,
            },
            RoleDecl {
                name: "bidder".to_string(),
                cardinality: RoleCardinality::Indexed,
            },
        ]
    }

    // ---- parse_roles (REQ-600, TEST-600) ----

    #[test]
    fn roles_positive_singleton_and_indexed() {
        let decls = parse_roles(&sx("(auctioneer (* bidder))")).unwrap();
        assert_eq!(decls, auction_roles());
    }

    #[test]
    fn roles_negative_empty_list() {
        assert!(matches!(
            parse_roles(&sx("()")),
            Err(R6Violation::MalformedRoles { .. })
        ));
    }

    #[test]
    fn roles_negative_not_a_list() {
        assert!(matches!(
            parse_roles(&sx("auctioneer")),
            Err(R6Violation::MalformedRoles { .. })
        ));
    }

    #[test]
    fn roles_negative_postfix_marker() {
        // (bidder *) is the rejected postfix form — dispatch is on the head.
        assert!(matches!(
            parse_roles(&sx("((bidder *))")),
            Err(R6Violation::MalformedRoles { .. })
        ));
    }

    #[test]
    fn roles_negative_marker_arity() {
        assert!(matches!(
            parse_roles(&sx("((*))")),
            Err(R6Violation::MalformedRoles { .. })
        ));
        assert!(matches!(
            parse_roles(&sx("((* a b))")),
            Err(R6Violation::MalformedRoles { .. })
        ));
    }

    #[test]
    fn roles_negative_non_symbol_entry() {
        assert!(matches!(
            parse_roles(&sx("(auctioneer 42)")),
            Err(R6Violation::MalformedRoles { .. })
        ));
    }

    #[test]
    fn roles_negative_duplicate_names() {
        assert!(matches!(
            parse_roles(&sx("(a (* a))")),
            Err(R6Violation::MalformedRoles { .. })
        ));
    }

    // ---- parse_from / parse_recipient_set (REQ-601 values, TEST-601) ----

    #[test]
    fn from_positive_symbol() {
        assert_eq!(parse_from("login", &sx("server")).unwrap(), "server");
    }

    #[test]
    fn from_negative_list() {
        assert!(matches!(
            parse_from("login", &sx("(server client)")),
            Err(R6Violation::MalformedFromTo { .. })
        ));
    }

    #[test]
    fn to_positive_bare_symbol_is_singleton_set() {
        let set = parse_recipient_set("login", &sx("client")).unwrap();
        assert_eq!(set.len(), 1);
        assert!(set.contains("client"));
    }

    #[test]
    fn to_positive_multicast() {
        let set = parse_recipient_set("login", &sx("(client authoriser)")).unwrap();
        assert_eq!(set.len(), 2);
        assert!(set.contains("client") && set.contains("authoriser"));
    }

    #[test]
    fn to_positive_empty_terminal() {
        let set = parse_recipient_set("declare-winner", &sx("()")).unwrap();
        assert!(set.is_empty());
    }

    #[test]
    fn to_negative_non_symbol_member() {
        assert!(matches!(
            parse_recipient_set("login", &sx("(client 7)")),
            Err(R6Violation::MalformedFromTo { .. })
        ));
    }

    #[test]
    fn to_negative_duplicate_member() {
        assert!(matches!(
            parse_recipient_set("login", &sx("(client client)")),
            Err(R6Violation::MalformedFromTo { .. })
        ));
    }

    // ---- parse_cast (REQ-611/614, TEST-611/614) ----

    #[test]
    fn cast_positive_auction() {
        let cast = parse_cast(
            &sx("((auctioneer @auc) (bidder @b1 @b2 @b3))"),
            &auction_roles(),
        )
        .unwrap();
        assert_eq!(
            cast.singleton.get("auctioneer"),
            Some(&AgentKey("@auc".to_string()))
        );
        let members = cast.indexed.get("bidder").unwrap();
        assert_eq!(members.len(), 3);
        assert!(cast.admits("bidder", &AgentKey("@b2".to_string())));
        assert!(!cast.admits("bidder", &AgentKey("@b4".to_string())));
        assert!(cast.admits("auctioneer", &AgentKey("@auc".to_string())));
    }

    #[test]
    fn cast_negative_singleton_two_keys() {
        assert!(matches!(
            parse_cast(&sx("((auctioneer @a @b) (bidder @b1))"), &auction_roles()),
            Err(R6Violation::ArityMismatch { keys: 2, .. })
        ));
    }

    #[test]
    fn cast_negative_unknown_role() {
        assert!(matches!(
            parse_cast(
                &sx("((auctioneer @auc) (bidder @b1) (ghost @g))"),
                &auction_roles()
            ),
            Err(R6Violation::UnknownRole { .. })
        ));
    }

    #[test]
    fn cast_negative_missing_binding() {
        assert!(matches!(
            parse_cast(&sx("((auctioneer @auc))"), &auction_roles()),
            Err(R6Violation::MalformedCast { .. })
        ));
    }

    #[test]
    fn cast_negative_duplicate_binding() {
        assert!(matches!(
            parse_cast(
                &sx("((auctioneer @auc) (auctioneer @b) (bidder @b1))"),
                &auction_roles()
            ),
            Err(R6Violation::MalformedCast { .. })
        ));
    }

    #[test]
    fn cast_negative_indexed_no_keys() {
        assert!(matches!(
            parse_cast(&sx("((auctioneer @auc) (bidder))"), &auction_roles()),
            Err(R6Violation::MalformedCast { .. })
        ));
    }

    #[test]
    fn cast_negative_non_list_binding() {
        assert!(matches!(
            parse_cast(&sx("(auctioneer @auc)"), &auction_roles()),
            Err(R6Violation::MalformedCast { .. })
        ));
    }

    // ---- parse_wrapper_cast / parse_dialect_pin (REQ-628, TEST-642) ----

    fn hex64(c: char) -> String {
        core::iter::repeat(c).take(64).collect()
    }

    #[test]
    fn wrapper_cast_without_pin_has_none() {
        let cast =
            parse_wrapper_cast(&[sx("((auctioneer @auc) (bidder @b1))")], &auction_roles())
                .unwrap();
        assert_eq!(cast.dialect_pin, None);
    }

    #[test]
    fn wrapper_cast_with_wellformed_pin_carries_it() {
        let pin = alloc::format!("sha256:{}", hex64('a'));
        let cast = parse_wrapper_cast(
            &[
                sx("((auctioneer @auc) (bidder @b1))"),
                sx(":dialect"),
                sx(&pin),
            ],
            &auction_roles(),
        )
        .unwrap();
        assert_eq!(cast.dialect_pin.as_deref(), Some(pin.as_str()));
    }

    #[test]
    fn pin_negative_bad_prefix() {
        assert!(matches!(
            parse_dialect_pin(&sx(&alloc::format!("md5:{}", hex64('a')))),
            Err(R6Violation::MalformedCast { .. })
        ));
    }

    #[test]
    fn pin_negative_wrong_length() {
        assert!(matches!(
            parse_dialect_pin(&sx("sha256:abc")),
            Err(R6Violation::MalformedCast { .. })
        ));
        assert!(matches!(
            parse_dialect_pin(&sx(&alloc::format!("sha256:{}a", hex64('a')))),
            Err(R6Violation::MalformedCast { .. })
        ));
    }

    #[test]
    fn pin_negative_non_hex_digits() {
        // 'g' is outside the hex alphabet; 'A' is uppercase — both rejected,
        // never case-folded or repaired (LangSec principle 4).
        assert!(matches!(
            parse_dialect_pin(&sx(&alloc::format!("sha256:{}", hex64('g')))),
            Err(R6Violation::MalformedCast { .. })
        ));
        assert!(matches!(
            parse_dialect_pin(&sx(&alloc::format!("sha256:{}", hex64('A')))),
            Err(R6Violation::MalformedCast { .. })
        ));
    }

    #[test]
    fn pin_negative_non_symbol_value() {
        assert!(matches!(
            parse_dialect_pin(&sx("(sha256 x)")),
            Err(R6Violation::MalformedCast { .. })
        ));
    }

    #[test]
    fn wrapper_cast_negative_extra_fields() {
        let pin = alloc::format!("sha256:{}", hex64('a'));
        // Trailing garbage after the pin.
        assert!(matches!(
            parse_wrapper_cast(
                &[
                    sx("((auctioneer @auc) (bidder @b1))"),
                    sx(":dialect"),
                    sx(&pin),
                    sx("junk"),
                ],
                &auction_roles(),
            ),
            Err(R6Violation::MalformedCast { .. })
        ));
        // Unknown keyword field in the pin position.
        assert!(matches!(
            parse_wrapper_cast(
                &[
                    sx("((auctioneer @auc) (bidder @b1))"),
                    sx(":lang"),
                    sx(&pin),
                ],
                &auction_roles(),
            ),
            Err(R6Violation::MalformedCast { .. })
        ));
    }
}
