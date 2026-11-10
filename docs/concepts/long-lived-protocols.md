# Long-lived CBCL protocols

CBCL language editions are intended to evolve much more slowly than implementation
releases. The proposed edition design is in
[SPEC-043](../../specs/SPEC-043-explicit-cbcl-release.md). The `cbcl-1` declaration
is a design proposal, not syntax supported by the current runtime.

A later edition must retain earlier interpretations, canonical bytes and identities.
An older receiver can learn additional vocabulary when its complete definition is
expressible using the receiver's existing primitives and passes its resource checks.
It cannot learn a new parser primitive or cryptographic algorithm merely by receiving
its name. Resource exhaustion is an operational refusal, not a new interpretation.

## Public keys with Multikey

The Rust core provides the public-key payload encoding used by
[W3C Multikey](https://www.w3.org/TR/cid-1.0/#multikey): an algorithm-tagged binary
key encoded in base58btc. It recognizes Ed25519, X25519, compressed P-256 and
compressed P-384 payloads. Recognition checks codec, length and compressed prefix;
it does not establish curve-point validity, possession or authorization.

```rust
use cbcl_core::{keyid::KeyId, multikey::Multikey};

let public = Multikey::parse(
    "z6MkmM42vxfqZQsv4ehtTjFFxQ4sQKS2w6WR7emozFAn5cxu"
)?;
let identity = KeyId::from_multikey(&public)?;
// @ed25519:z6MkmM42vxfqZQsv4ehtTjFFxQ4sQKS2w6WR7emozFAn5cxu
// The host must bind public.public_key_bytes() to its cryptographic verifier.
# Ok::<(), Box<dyn std::error::Error>>(())
```

Conversion to a signing identity currently supports Ed25519 only. X25519 is a
key-agreement key; recognizing ECDSA key material does not add ECDSA signing support.
Only public-key codecs are accepted. Text is bounded before decoding, and unsupported
codecs and noncanonical encodings fail closed. This is not a complete controlled
identifier document, key directory or DID resolver.

Existing `KeyId::parse` behavior is unchanged. In particular, `@multikey:...` is
still an unknown-suite principal; use the explicit constructor for conversion.
An existing `@alice` identity is not automatically associated with a public key,
and a newly generated key is a new principal unless a host authenticates continuity.
The existing signature preimages and dialect/message address formats are unchanged.

Inspect a public payload from the CLI:

```bash
cargo run -p cbcl-cli -- multikey z6MkmM42vxfqZQsv4ehtTjFFxQ4sQKS2w6WR7emozFAn5cxu
```

The JSON result includes the codec, public bytes and supported signing identity
(or `null` for a recognized key without a supported signing suite).

## Identity and algorithm renewal

A dialect's self-name hashes its canonical body with the designated name slot
empty. Its signature then binds the populated name. The separate named-form
integrity hash is not its self-name. Parent references in the proposed edition
format use self-names, avoiding a recursive self-hash computation.

Multikey describes which public-key algorithm to use; it does not make an obsolete
algorithm secure. Likewise, the current multihash and Merkle implementation still
support SHA2-256 only. Supporting another hash needs explicit construction and proof
formats, not just accepting another prefix. Verification, policy acceptance and
permission to execute effects remain separate decisions.

For long-term preservation, retain original bytes and verification material. A host
may authenticate renewal evidence under newer algorithms while retaining the original
identities. A renewal policy needs a trusted authority and authenticated evidence;
an archive cannot authorize its own contents, and replacing a hash prefix or adding
a new signature after a compromise does not recover lost authenticity.

## Offline recovery

A complete package needs dialect dependencies, causal predecessors, any checkpoint
certificates, the intended interpretation, and sufficient authentication evidence.
The existing `CausalClosureBundle` helps transfer message evidence; it does not supply
a complete dialect archive or historical trust policy. Missing evidence must remain
explicit. Pending-queue TTL and eviction are live delivery policies, not durable
archival retention.

Provision trust anchors and historical verification policy independently of the
archive. If authenticated historical time or revocation evidence is unavailable,
report that limitation rather than asserting historical authorization. No network
lookup or negotiation should be needed to select the meaning of a complete package.

## What remains before an edition is frozen

The design requires an authoritative language report, pinned dependencies, portable
canonical numeric rules, explicit resource profiles, cryptographic transition policy
and old/new conformance evidence. Canonical float selection now has an independent exact-rational conformance
oracle, including an explicit decimal tie rule preserving current bytes. The
production formatter remains Rust's implementation; passing samples is not a
universal proof. Current Unicode 16 and regex dependencies remain pinned. Regex compiler-generated state counts are a current resource-profile choice,
not a universal semantic cost model. The implementation plan records these boundaries
in [IMPL-043](../../plans/IMPL-043-longevity.md).
