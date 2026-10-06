# Fresh-context comprehension review

Source: only `outputs/issue18/comprehension-prompt.txt`, including its supplied Orientation. No implementation or other files consulted.

Intent: a dialect's `(state …)` clause defines recomputed queries over its accepted acts. The accepted-act set converges by union; state and intent binding are pure functions of that set, with total, order-independent, duplicate-insensitive state rules (R7). Supersession is bookkeeping in compiler-inserted `:replaces`, not mutation of ledger entries.

Predictions from the Orientation:

- **Sequential own writes:** A writes x, observes x, then writes y. y supersedes x even when y's content address is lower than x's. The explicit sentence “Sequential signer writes replace observed own writes” establishes this; address ordering applies to concurrent writes rather than defeating observed supersession.
- **Concurrent own writes:** Concurrent A writes do not supersede one another through observation. They retain address ordering. The Orientation also describes a register that keeps concurrent writes. Thus concurrent writes remain candidates and address ordering supplies deterministic selection where a rule selects by address. The Orientation does not identify a particular state rule in this scenario, so it does not determine whether the displayed field is a collection of retained values or a single selected value, nor the direction of address selection.
- **Cross-signer replacement:** If B names A's x in `:replaces`, B cannot supersede A's ballot. The governing requirement is **SPEC-019-state-rules REQ-1933**, explicitly linked in Controls. A caller supplying `:replaces` through the intent interface is additionally rejected as a forge under REQ-1921–REQ-1925. For an already submitted act, the Orientation does not say whether a cross-signer reference is ignored during folding or causes rejection; it guarantees the protection, not that mechanism.

Ambiguities: the concrete state rule, address-selection direction, and treatment of an incoming cross-signer `:replaces` reference are unspecified here. Those details cannot be inferred from implementation in this review. They do not prevent predicting the requested supersession and concurrency properties or locating their protection requirement.

**PASS** for the comprehension gate: a reader can predict observed sequential replacement despite a lower address, preservation/address ordering of concurrent own writes, and cross-signer replacement protection, and can identify REQ-1933. Exact field output and incoming-act handling require the normative Reference.
