//! adapters: per-operator [`ProtocolAdapter`](super::ProtocolAdapter) impls.
//!
//! One module per arena operator. The current set:
//!
//! - [`psi`] — Private Set Intersection (PSI), the original calibration
//!   challenge. Five performatives: psi-salt, psi-commit, psi-reveal,
//!   psi-claim, psi-final. Tools include a `hash_element` utility for
//!   the LLM to compute salt-element digests in-context.
//!
//! Future modules (per `IMPL-arena-evals`):
//!
//! - `millionaire` — Yao's Millionaire (REQ-1111).
//! - `auction` — sealed-bid auction (SPEC-004).
//! - `dining` — Dining Cryptographers (REQ-1112).
//! - `ultimatum` — ultimatum game (eval extension).

pub mod auction;
pub mod dining;
pub mod millionaire;
pub mod psi;

pub use auction::AuctionDisciplinedAdapter;
pub use dining::DiningDisciplinedAdapter;
pub use millionaire::YaoDisciplinedAdapter;
pub use psi::PsiDisciplinedAdapter;
