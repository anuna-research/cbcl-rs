//! Experimental bounded admission/state proofs. See experiments/state-proof/BRIEF.md.
//! The verifier compiles the complete relation from CBCL, not from prover tables.
#![forbid(unsafe_code)]

mod candidate;
mod chain;
mod circuit;
mod profile;

pub use candidate::Candidate;
pub use chain::{Chain, MAX_LINKS};
use circuit::StateCircuit;
use ff::PrimeField;
use halo2_proofs::{
    pasta::{EqAffine, Fp},
    plonk::{
        create_proof, keygen_pk, keygen_vk, verify_proof, ProvingKey, SingleVerifier, VerifyingKey,
    },
    poly::commitment::Params,
    transcript::{Blake2bRead, Blake2bWrite, Challenge255},
};
pub use profile::{Checkpoint, Profile, Statement, MAX_CANDIDATES, SEMANTICS_VERSION};
use rand_core::OsRng;
use serde::{Deserialize, Serialize};
use serde_json::Value;

pub type Result<T> = std::result::Result<T, String>;
const MAX_TRANSCRIPT: usize = 16_384;
const MAX_PACKAGE: usize = 100_000;
/// Chain package limit (SPEC-035 v0.2.1 CON-3502): 64 links of the largest
/// proof the proof limit admits, with room for the envelope.
const MAX_CHAIN_PACKAGE: usize = 1_048_576;

/// Authentication is a host precondition; this proof does not verify signatures.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Proof {
    pub statement: Statement,
    pub transcript: Vec<u8>,
}
impl Proof {
    /// Writes CON-3502 member order with no whitespace. Rejects an invalid
    /// transcript size and a package over `MAX_PACKAGE` (100,000) bytes.
    pub fn to_json(&self) -> Result<Vec<u8>> {
        self.check_size()?;
        let bytes = serde_json::to_vec(self).map_err(|e| e.to_string())?;
        if bytes.len() > MAX_PACKAGE {
            return Err("proof package exceeds limit".into());
        }
        Ok(bytes)
    }
    /// Recognises against CON-3502: unknown or duplicate members, non-integer
    /// or out-of-range bytes, trailing input other than JSON whitespace, a
    /// package over `MAX_PACKAGE` bytes and an invalid transcript size are
    /// rejected.
    pub fn from_json(bytes: &[u8]) -> Result<Self> {
        if bytes.len() > MAX_PACKAGE {
            return Err("proof package exceeds limit".into());
        }
        Self::check_shape(&serde_json::from_slice(bytes).map_err(|e| e.to_string())?)?;
        let proof: Self = serde_json::from_slice(bytes).map_err(|e| e.to_string())?;
        proof.check_size()?;
        Ok(proof)
    }
    /// CON-3502: every struct position (`Proof`, `statement`, `before`,
    /// `after`) is a JSON object; serde alone would also accept a positional
    /// array. Missing or mistyped members are left to typed deserialisation.
    pub(crate) fn check_shape(value: &Value) -> Result<()> {
        let proof = object(value)?;
        if let Some(statement) = proof.get("statement") {
            let statement = object(statement)?;
            for side in ["before", "after"] {
                if let Some(checkpoint) = statement.get(side) {
                    object(checkpoint)?;
                }
            }
        }
        Ok(())
    }
    fn check_size(&self) -> Result<()> {
        let n = self.transcript.len();
        if !(32..=MAX_TRANSCRIPT).contains(&n) || n % 32 != 0 {
            return Err("invalid transcript size".into());
        }
        Ok(())
    }
}

pub(crate) fn object(value: &Value) -> Result<&serde_json::Map<String, Value>> {
    value
        .as_object()
        .ok_or_else(|| "expected a JSON object".to_string())
}

/// Parameters and proving key are reusable for this exact public profile.
pub struct Prover {
    profile: Profile,
    params: Params<EqAffine>,
    pk: ProvingKey<EqAffine>,
}
/// Construct independently from the verifier's expected dialect/thread/candidates.
pub struct Verifier {
    profile: Profile,
    params: Params<EqAffine>,
    vk: VerifyingKey<EqAffine>,
}

impl Prover {
    pub fn new(profile: Profile) -> Result<Self> {
        let circuit = StateCircuit::empty(&profile);
        let params = Params::new(circuit.k());
        let vk = keygen_vk(&params, &circuit).map_err(|e| e.to_string())?;
        let pk = keygen_pk(&params, vk, &circuit).map_err(|e| e.to_string())?;
        Ok(Self {
            profile,
            params,
            pk,
        })
    }
    /// Proves `profile.statement(before, after)`. Fails closed (REQ-3508 d):
    /// the transcript must be 32 to 16,384 bytes in 32-byte steps or `prove`
    /// returns `Err` instead of a proof no recogniser would accept.
    pub fn prove(&self, before: u16, after: u16) -> Result<Proof> {
        let statement = self.profile.statement(before, after)?;
        let circuit = StateCircuit::witness(&self.profile, before, after);
        let instance = statement.instance();
        let mut transcript = Blake2bWrite::<_, EqAffine, Challenge255<_>>::init(Vec::new());
        create_proof(
            &self.params,
            &self.pk,
            &[circuit],
            &[&[&instance]],
            OsRng,
            &mut transcript,
        )
        .map_err(|e| e.to_string())?;
        let proof = Proof {
            statement,
            transcript: transcript.finalize(),
        };
        proof.check_size()?;
        Ok(proof)
    }
}
impl Verifier {
    pub fn new(profile: Profile) -> Result<Self> {
        let circuit = StateCircuit::empty(&profile);
        let params = Params::new(circuit.k());
        let vk = keygen_vk(&params, &circuit).map_err(|e| e.to_string())?;
        Ok(Self {
            profile,
            params,
            vk,
        })
    }
    pub fn verify(&self, proof: &Proof, expected: &Statement) -> Result<()> {
        proof.check_size()?;
        if expected.profile != self.profile.id() || &proof.statement != expected {
            return Err("unexpected checkpoint statement".into());
        }
        let instance = expected.instance();
        let mut remaining = proof.transcript.as_slice();
        let mut reader = Blake2bRead::<_, EqAffine, Challenge255<_>>::init(&mut remaining);
        verify_proof(
            &self.params,
            &self.vk,
            SingleVerifier::new(&self.params),
            &[&[&instance]],
            &mut reader,
        )
        .map_err(|_| "invalid proof".to_string())?;
        if !remaining.is_empty() {
            return Err("trailing transcript bytes".into());
        }
        Ok(())
    }
}

pub(crate) fn limbs(bytes: [u8; 32]) -> [Fp; 2] {
    std::array::from_fn(|i| {
        let mut repr = [0; 32];
        repr[..16].copy_from_slice(&bytes[16 * i..16 * i + 16]);
        Option::<Fp>::from(Fp::from_repr(repr)).expect("128-bit limb fits Pasta Fp")
    })
}

#[cfg(test)]
mod chain_tests;
#[cfg(test)]
mod package_tests;
#[cfg(test)]
mod tests;
