//! Bounded adversarial workloads for the benchmark host, outside Replica.
//! A compromised node may bypass its journal and sign contradictory statements.
use crate::{model::ByzantineMode, transport::Request};
use cbcl_core::quorum::{Vote, VoteKind};
use ed25519_dalek::{Signer, SigningKey};
use serde::Serialize;

pub const INVALID_REPLIES_PER_REQUEST: usize = 8;

#[derive(Default, Serialize)]
pub struct Faults {
    pub requests: usize,
    pub withheld: usize,
    pub conflicting_pairs: usize,
    pub invalid_sent: usize,
    pub votes_sent: usize,
    effects_requests: usize,
}
impl Faults {
    pub fn respond(
        &mut self,
        mode: ByzantineMode,
        request: &Request,
        context: &str,
        signer: &str,
        key: &SigningKey,
    ) -> Vec<Vote> {
        let (kind, payload) = match request {
            Request::Operation { signed } => (VoteKind::Operation, &signed.act.address),
            Request::Effects { certificate } => (VoteKind::Effects, &certificate.payload),
            Request::Final { .. } | Request::Stop => return vec![],
        };
        assert_ne!(mode, ByzantineMode::None);
        self.requests += 1;
        let sign = |kind| {
            let mut vote = Vote {
                context: context.into(),
                kind,
                payload: payload.clone(),
                signer: signer.into(),
                signature: vec![],
            };
            vote.signature = key.sign(&vote.preimage()).to_bytes().to_vec();
            vote
        };
        let votes = match mode {
            ByzantineMode::Withhold => {
                if kind == VoteKind::Effects {
                    self.effects_requests += 1;
                    if self.effects_requests % 2 == 1 {
                        self.withheld += 1;
                        return vec![];
                    }
                }
                vec![sign(kind)]
            }
            ByzantineMode::Equivocate if kind == VoteKind::Effects => {
                self.conflicting_pairs += 1;
                // Both signatures are genuine, but an honest node cannot issue
                // both effects and cancellation for this same transaction.
                vec![sign(VoteKind::Cancel), sign(VoteKind::Effects)]
            }
            ByzantineMode::Equivocate => vec![sign(kind)],
            ByzantineMode::InvalidFlood => {
                let mut bad = sign(kind);
                bad.signature[0] ^= 1;
                self.invalid_sent += INVALID_REPLIES_PER_REQUEST;
                vec![bad; INVALID_REPLIES_PER_REQUEST]
            }
            ByzantineMode::None => unreachable!(),
        };
        self.votes_sent += votes.len();
        votes
    }
}
