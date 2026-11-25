//! Browser bindings for public keys and certified checkpoint continuation.
use alloc::{
    collections::{BTreeMap, BTreeSet},
    string::{String, ToString},
    vec::Vec,
};
use cbcl_checkpoint::{
    certificate::{Certificate, Context, KeyVerifier, Policy, SignedMessage},
    coverage::Proof,
    member::{Client, Step},
    summary::Summary,
};
use cbcl_core::{
    keyid::KeyId,
    multikey::{Multikey, PublicKeyCodec},
};
use ed25519_dalek::{Signature, VerifyingKey};
use serde::Deserialize;
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn inspect_multikey(source: &str) -> Result<String, String> {
    let key = Multikey::parse(source).map_err(|e| e.to_string())?;
    Ok(serde_json::json!({"codec":key.codec().code(),"bytes":key.public_key_bytes()}).to_string())
}
#[wasm_bindgen]
pub fn encode_multikey(codec: u32, bytes: &[u8]) -> Result<String, String> {
    PublicKeyCodec::from_code(codec.into())
        .and_then(|c| Multikey::new(c, bytes))
        .map(|k| k.to_multibase())
        .map_err(|e| e.to_string())
}
#[wasm_bindgen]
pub fn multikey_identity(source: &str) -> Result<String, String> {
    Multikey::parse(source)
        .and_then(|k| KeyId::from_multikey(&k))
        .map(|k| k.canonical_spelling())
        .map_err(|e| e.to_string())
}

struct Keys(BTreeMap<String, VerifyingKey>);
impl KeyVerifier for Keys {
    fn verify(&self, key: &str, message: &[u8], sig: &[u8]) -> bool {
        self.0
            .get(key)
            .zip(Signature::from_slice(sig).ok())
            .is_some_and(|(key, sig)| key.verify_strict(message, &sig).is_ok())
    }
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct TrustedContext {
    dialect: String,
    target_root: String,
    companion_root: String,
    policy: Policy,
    public_keys: BTreeMap<String, String>,
}
fn signed(text: &str) -> Result<SignedMessage, String> {
    cbcl_parser::parse_message(&cbcl_parser::parse(text).map_err(|e| e.to_string())?)
        .map(SignedMessage::from_message)
        .map_err(|e| e.to_string())
}

/// A verified in-memory client. Only authenticated continuation can mutate it.
#[wasm_bindgen]
pub struct CheckpointClient {
    context: Context,
    client: Client,
    keys: Keys,
}

#[wasm_bindgen]
pub fn open_checkpoint(context: &str, certificate: &[u8]) -> Result<CheckpointClient, String> {
    let input: TrustedContext = serde_json::from_str(context).map_err(|e| e.to_string())?;
    let mut keys = Keys(BTreeMap::new());
    let mut seen = BTreeSet::new();
    for (id, source) in input.public_keys {
        let key = Multikey::parse(&source).map_err(|e| e.to_string())?;
        if key.codec() != PublicKeyCodec::Ed25519 || !seen.insert(source) {
            return Err("expected distinct Ed25519 verification keys".into());
        }
        let bytes = key
            .public_key_bytes()
            .try_into()
            .map_err(|_| "Ed25519 key length")?;
        keys.0.insert(
            id,
            VerifyingKey::from_bytes(bytes).map_err(|e| e.to_string())?,
        );
    }
    let form = cbcl_parser::describe::define_form(&input.dialect)?;
    let registry = cbcl_parser::parse_and_install_dialect(&form)?;
    let dialect = registry
        .iter()
        .last()
        .ok_or("missing target dialect")?
        .clone();
    let profile = Summary::expected_profile_hash_for(
        dialect.state.as_ref().ok_or("missing target state")?,
        dialect.causal_protocol.as_ref(),
    )
    .map_err(|e| e.to_string())?;
    let context = Context::new(
        dialect,
        signed(&input.target_root)?,
        signed(&input.companion_root)?,
        input.policy,
        profile,
        &keys,
    )
    .map_err(|e| e.to_string())?;
    let cert = Certificate::decode(certificate, &context).map_err(|e| e.to_string())?;
    let client = Client::from_certificate(&context, &cert, &keys).map_err(|e| e.to_string())?;
    Ok(CheckpointClient {
        context,
        client,
        keys,
    })
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireStep {
    message: String,
    ancestry: Vec<(String, Proof)>,
    identity: Proof,
    replacements: Vec<(String, Proof)>,
}

impl WireStep {
    fn recognize(self) -> Result<Step, String> {
        Ok(Step {
            message: signed(&self.message)?,
            ancestry: self
                .ancestry
                .into_iter()
                .map(|(m, p)| Ok((signed(&m)?, p)))
                .collect::<Result<_, String>>()?,
            identity: self.identity,
            replacements: self.replacements,
        })
    }
}

#[wasm_bindgen]
impl CheckpointClient {
    pub fn state(&self) -> String {
        self.client.summary.render_json()
    }
    pub fn apply(&mut self, text: &str) -> Result<(), String> {
        let wire: WireStep = serde_json::from_str(text).map_err(|e| e.to_string())?;
        self.client
            .apply(&wire.recognize()?, &self.context, &self.keys)
            .map_err(|e| e.to_string())
    }

    pub fn frontier(&self) -> Vec<String> {
        self.client.frontier.clone()
    }

    /// Replace only after the certificate, tail, and inclusion of the local frontier all verify.
    pub fn replace(&mut self, certificate: &[u8], tail: &str, proofs: &str) -> Result<(), String> {
        let cert = Certificate::decode(certificate, &self.context).map_err(|e| e.to_string())?;
        let mut next = Client::from_certificate(&self.context, &cert, &self.keys)
            .map_err(|e| e.to_string())?;
        let steps: Vec<WireStep> = serde_json::from_str(tail).map_err(|e| e.to_string())?;
        for step in steps {
            next.apply(&step.recognize()?, &self.context, &self.keys)
                .map_err(|e| e.to_string())?;
        }
        let proofs: Vec<(String, Proof)> =
            serde_json::from_str(proofs).map_err(|e| e.to_string())?;
        next.check_floor(&self.client.floor(), &proofs)
            .map_err(|e| e.to_string())?;
        next.retain_from(&self.client).map_err(|e| e.to_string())?;
        self.client = next;
        Ok(())
    }
}

/// Encode integer balances outside JavaScript's exact number range as decimal strings.
#[wasm_bindgen]
pub fn resource_check_exact(input: &str) -> Result<String, String> {
    use cbcl_core::state::Value;
    fn encode(value: &mut Value) {
        match value {
            Value::Int(n) if n.unsigned_abs() > (1_u128 << 53) - 1 => {
                *value = Value::Str(n.to_string());
            }
            Value::Map(entries) => {
                for (_, child) in entries {
                    encode(child);
                }
            }
            _ => {}
        }
    }
    let mut outcome = cbcl_parser::state_exports::resource_check_value(input)?;
    encode(&mut outcome);
    Ok(outcome.render())
}
