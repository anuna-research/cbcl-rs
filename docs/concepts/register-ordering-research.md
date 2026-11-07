---
title: Register ordering research
mode: explanation
status: draft
last-updated: 2026-11-06
---

# Register ordering research

[[SPEC-035-register-semantics]] separates conflict policy, replacement and authority
from the mechanism used to order candidates. This note records source provenance
for that draft. The sources do not establish correctness of a CBCL amendment.

## Causality and domain-specific resolution

Zawirski, Baquero, Bieniusa, Preguiça and Shapiro, *Eventually Consistent Register
Revisited* (2015), sections 1–3, define a multi-value register through causally
maximal writes and apply a separate resolution function to those values. A
predefined partial order on application values can remove dominated alternatives;
an empty order retains all conflicts, and a total order yields at most one value.
Source: https://arxiv.org/html/1511.05010v1

CBCL inference: explicit replacement and candidate arbitration should have separate
contracts. A semantic merge can be more meaningful than choosing the greatest
hash, but must express an actual application policy. Existing `:replaces` is not
automatically equivalent to all causal visibility: its scope, bounded binding and
out-of-order-reference rules remain those of [[SPEC-019-state-rules]].

## Byzantine evidence and logical timestamps

Kleppmann, *Making CRDTs Byzantine Fault Tolerant* (PaPoC 2022), sections 3.3–3.4,
uses update hashes as unique identifiers and describes checking update validity
against immutable causal predecessors. For a causality-consistent ordered ID,
the paper describes checking that a logical timestamp is exactly one greater than
the maximum over its causal predecessors. Its general applicability claim is
explicitly presented as a conjecture requiring algorithm-specific proof.
Source: https://martin.kleppmann.com/papers/bft-crdt-papoc22.pdf

CBCL inference: deriving ranks from evidence can avoid trusting an arbitrary
sender-supplied integer, but cannot reveal omitted observations, identify true
physical recency, or make chain length a fair arbitration rule. Hash identity
and hash-based preference are separate uses of a hash.

Kleppmann and Howard, *Byzantine Eventual Consistency and the Fundamental Limits
of Peer-to-Peer Databases* (2020), characterize their Byzantine eventual consistency
model using invariant confluence and Byzantine causal broadcast. This is not a
universal guarantee for scarce-resource operations or arbitrary shared registers.
Source: https://arxiv.org/html/2012.00472v1

## Displaying a winner versus resolving a conflict

Automerge's *Merge Rules* documentation states that competing assignments to the
same key are resolved by an arbitrary choice made consistently across replicas.
Its *Conflicts* documentation describes inspecting conflicting assignments.
Sources: https://automerge.org/docs/reference/under-the-hood/merge-rules/
and https://automerge.org/docs/reference/documents/conflicts/

CBCL inference: a convenience display can choose one candidate while authoritative
state preserves conflicts. This would require an explicit state/presentation API
contract; it is not accomplished by renaming a single-value rule.

## Clock-trusting profiles

A clock-trusting last-writer-wins profile is an explicit CBCL design option, not
a conclusion that arbitrary senders provide honest clocks. The implemented trusted-host HLC profile is
[[SPEC-035-register-semantics#ADR-3502]]. Lamport and per-signer sequence profiles
remain research alternatives.
An accepted profile needs authoritative source review of its exact clock algorithm,
wire evidence, persistence, range and trust policy before implementation. No
statement here claims that timestamps supply Byzantine finality or physical
ordering of concurrent events.


## Adopted HLC advancement algorithm

Kulkarni, Demirbas, Madeppa, Avva and Leone, *Logical Physical Clocks and
Consistent Snapshots in Globally Distributed Databases* (2014), section 3,
describe physical/logical clock advancement for local/send and receive events.
The helper follows those maximum-and-logical-increment cases with explicit host
inputs. CBCL uses a separate fixed-width u64/u32 encoding and checked logical
overflow refusal; it does not claim the paper's compact NTP representation or
inherit its deployment assumptions as a Rust correctness proof.
Source: https://cse.buffalo.edu/tech-reports/2014-04.pdf
