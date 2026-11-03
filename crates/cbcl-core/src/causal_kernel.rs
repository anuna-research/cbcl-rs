//! Allocation-free causal decisions, shared by the production verifier and its
//! extracted Lean semantics. Adapters supply lookup/membership/coverage evidence;
//! they do not supply a precomputed verification verdict.
//!
//! The fan-in machine deliberately preserves eager rejection: wrong evidence
//! dominates missing evidence. Admission separately enforces resolution first.
#![forbid(unsafe_code)]

pub(crate) enum Lookup {
    Missing,
    Allowed,
    Wrong,
}

#[derive(Clone, Copy)]
pub(crate) enum FanIn {
    Clear,
    Missing,
    Wrong,
}

pub(crate) enum Decision {
    Valid,
    Unknown,
    MissingCausedBy,
    InvalidPredecessor,
    ExtraneousPredecessor,
    FanInWithoutAllDecl,
    IncompleteFanIn,
}

pub(crate) fn absent(has_predecessors: bool) -> Decision {
    if has_predecessors {
        Decision::MissingCausedBy
    } else {
        Decision::Valid
    }
}

pub(crate) fn literal_begin(allowed: bool) -> Decision {
    if allowed {
        Decision::Valid
    } else {
        Decision::InvalidPredecessor
    }
}

pub(crate) fn single(has_predecessors: bool, lookup: Lookup) -> Decision {
    match lookup {
        Lookup::Missing => Decision::Unknown,
        Lookup::Allowed => Decision::Valid,
        Lookup::Wrong => {
            if has_predecessors {
                Decision::InvalidPredecessor
            } else {
                Decision::ExtraneousPredecessor
            }
        }
    }
}

/// Consume one lookup. Wrong is absorbing; missing persists until a wrong lookup.
pub(crate) fn observe(state: FanIn, lookup: Lookup) -> FanIn {
    match (state, lookup) {
        (FanIn::Wrong, _) | (_, Lookup::Wrong) => FanIn::Wrong,
        (FanIn::Missing, _) | (_, Lookup::Missing) => FanIn::Missing,
        (FanIn::Clear, Lookup::Allowed) => FanIn::Clear,
    }
}

/// Coverage only decides the result after every supplied lookup was allowed.
pub(crate) fn finish(has_all: bool, state: FanIn, complete: bool) -> Decision {
    if !has_all {
        return Decision::FanInWithoutAllDecl;
    }
    match state {
        FanIn::Wrong => Decision::InvalidPredecessor,
        FanIn::Missing => Decision::Unknown,
        FanIn::Clear => {
            if complete {
                Decision::Valid
            } else {
                Decision::IncompleteFanIn
            }
        }
    }
}
