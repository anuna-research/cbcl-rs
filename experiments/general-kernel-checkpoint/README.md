# General kernel checkpoint experiment

This isolated workspace proves the existing CBCL consumer admission/fold
computation with the dialect supplied as input. One guest image handles different
dialects; the client verifies a receipt and snapshot without message history.

[[experiments/general-kernel-checkpoint/RESULTS]] records actual RISC Zero proving,
compression, verification and bandwidth measurements. The small measured bundles
are larger than compressed replay; practical savings are not yet demonstrated.
[[experiments/general-kernel-checkpoint/BACKENDS]] assesses SP1, Nexus and Jolt
against the same statement, without claiming unmeasured backend performance.

[[experiments/general-kernel-checkpoint/BRIEF]] defines the bounded prototype and
[[experiments/general-kernel-checkpoint/REPRODUCE]] gives commands. The shared
common crate calls the unmodified core/parser; methods/guest contains only VM I/O.
Signer authentication remains a host assumption. This is not production wiring
or an independently authenticated, resumable snapshot protocol.
