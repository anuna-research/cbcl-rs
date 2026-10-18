# SPEC-020 adversarial review — round 5 (Codex)

Reviewed SPEC-020 v0.5.0 in full, then checked SPEC-014, SPEC-002, SPEC-003 and the four requested concept pages. This is an independent specification review, with hand-executed counterexamples; it is not an implementation test result. No web sources were used. All scenarios below assume valid signatures, complete authority pasts and sufficient recipients unless a finding specifically changes those conditions. Symbols such as `G`, `A` and `E1` denote distinct content hashes.

## Findings

1. **BLOCKER — REQ-2017; Terminology, Chain, Principal seat and Termination: the set function has unresolved recursive definitions.**

   Quoted phrases: “every seat in its chain is live”; “when `X` is that position's principal seat”.

   Scenario: with no meta acts, the commander's root seat `C` has chain `[C]`. The live predicate reduces to `live(C) iff live(C)`: neither a fixed-point convention nor an exception for the seat itself is specified. More substantially, let Dana transfer `C` to Fay through `T, A`, then let observer Oli issue reseat `H` for `(commander, @dana)`, with `A` in `A(H)`. `H` names a position, not the replaced seat. Terminology calls both `C` and `Moved(A)` principal seats. If `H` terminates both, `C` has terminations `{A,H}`, so REQ-2017 issues neither `Moved(A)` nor its reseated successor. If `H` terminates only the principal resolved in `A(H)`, the replacement chain is `C → Moved(A) → Reseated(H)` and the new seat issues. These are different seat states for the same set. For a contested position, the spec additionally needs to say what seat a reseat terminates when admission has issued no successor. REQ-2031's imperative description of the epoch fold does not define this order-independent admission function.

   **Proposed fix:** define liveness over proper ancestors, and bind each admission reseat to an explicitly specified replacement target determined from its own authority past, including the contested case.

2. **BLOCKER — REQ-2017, REQ-2020, REQ-2047; Terminology, Emptied position: cascade removal and vacancy disagree.**

   Quoted phrases: “A seat is removed when `S` contains a termination of it”; “After the accept, every seat issued under the parent seat is removed”; “Its terminations contain no accept.”

   Scenario: in a policy variant permitting transfer and sharing, root responder seat `R` belongs to Eli. Share `G` seats Diag, and facet `H` under `G` seats Tidy, giving chains `[R,G]` and `[R,G,H]`. Accept `A` transfers `R` to Fay. REQ-2017 marks `R` removed and issues `Moved(A)`; neither `G` nor `H` has a termination. They are non-live because an ancestor is removed, but they are not removed under step 2. REQ-2020 explicitly requires them to be removed. The emptied-position predicate requires every principal seat to be removed, so it does not discharge Diag's position, contrary to the cascade rule in REQ-2047. An ancestor reseat produces the same discrepancy. Independently, transfer `R → Moved(A)`, followed by a resign of `Moved(A)`, leaves every principal removed but a historical accept in the position's terminations. Reading “no accept” across the position prevents its discharge forever; reading it only on the last replacement can discharge it. Neither scope is defined. A contested position whose ancestors subsequently disappear has the same unresolved distinction between a historical accept and a current vacancy.

   **Proposed fix:** define effective removal as a cascade closure, and define vacancy from the issued replacement structure and its surviving authority, distinguishing unresolved contests from a later effective discharge.

3. **BLOCKER — REQ-2009, REQ-2020; Terminology, Seat attributes: accepting a narrowed transfer restores the authority it removed.**

   Quoted phrase: “A `Moved` or `Reseated` seat copies the attributes of the seat it replaces.”

   Scenario: responder's policy permits transfer and redelegation; its principal seat covers `report`, `finding`, `propose-fix`. Grant `T` transfers it to Fay with `:acts (report finding) :redelegate #f :until (epoch 2)`. This is narrowing and keeps the fixture's stated Send steps. Fay accepts as `A`. `Moved(A)` copies the old seat's entire act set, redelegate flag and absent bound, rather than `T`'s restrictions. Fay can send `propose-fix`, delegate further and continue after epoch 2. All three restrictions disappeared. Even an implementation that intersects act sets along chains misses them: the moved chain substitutes `Moved(A)` for the parent and never includes the transfer grant as a restricting seat.

   **Proposed fix:** derive a moved seat's effective attributes from the accepted transfer grant intersected with the replaced seat, and specify the resulting chain and bound explicitly.

4. **BLOCKER — REQ-2027, REQ-2025, NFR-2001: the one-pass fold has multiple legal outcomes for one epoch.**

   Quoted phrase: “Take grants in authority order and removals in `:order` order, merged so that every message follows its authority links.”

   Scenario: Dana concurrently issues facet grant `G` under commander seat `C` and resign `R` of `C`; both have valid admission. `E1` covers both and has `:order (R)`. Both traversals `G,R` and `R,G` respect every specified order. The first adds `G`, making the grant `Final`, then removes its authority by cascade. The second removes `C` first and rejects `G` for current-state liveness, making the same grant `Void(GrantRejected)`. This is a difference in the returned verdict, not just traversal bookkeeping. An honest Tidy act under `G`, also covered by `E1`, can likewise obtain different failure reasons (`SeatRemoved` versus `SeatNotIssued`). The Orientation's grants-first description selects the first traversal, but the REQ does not. Ordered Rust collections do not supply the missing semantic order, and a hash ordering would introduce an unapproved tie-break.

   **Proposed fix:** specify a confluent placement of grants relative to ordered removals, or explicitly include their placement in the arbiter's signed ordering.

5. **BLOCKER — REQ-2027, REQ-2025 versus REQ-2039, REQ-2032, REQ-2048: the fold can finalise grants that fail non-liveness admission checks.**

   Quoted phrase: “A grant is added if it passes REQ-2007 through REQ-2012 with liveness judged in the current state.”

   Scenario: Eli issues a responder share `G` with `:acts (finding)`. Its admission is `Violation(UnliveGrant)` under REQ-2048. It nevertheless passes REQ-2007–2012: Eli holds the parent, share is permitted, the set narrows and the chain is short. In an epoch covering `G`, step 1 adds it and REQ-2025 declares it `Final`. Omitting required meta recipients has the same hole, because REQ-2032 is also outside the listed checks. Appointment authorisation under REQ-2039 and its bound checks likewise need explicit treatment. Re-evaluating liveness in the fold is a deliberate design choice; dropping these other checks is not justified by ADR-2004's rejection of admission's no-holder rule.

   **Proposed fix:** enumerate and preserve every non-liveness grant check in the fold, then identify exactly which admission-state checks are recomputed against the current finalised state.

6. **BLOCKER — REQ-2046, REQ-2047, REQ-2022 versus SPEC-002 REQ-203 and SPEC-014 REQ-616/617: a fully discharged round cannot pass unchanged R5.**

   Quoted phrase: “Three resigns and a `close` that references no report, citing all three, is `Valid`.” (TEST-2052.)

   Scenario: request `O` opens a round with responder positions Eli, Fay and Gus. Each resigns without reporting. `close C :anchor O` carries all three resigns in `:seen` and references no report. REQ-2047 and TEST-2052 demand `Valid`. Unchanged R5 still requires predecessor type `report` for the `(all report)` fan-in; an empty predecessor set cannot provide it. Putting resigns in `:caused-by` instead violates SPEC-014 REQ-616 because `resign` is not a protocol predecessor. The root and request are also the wrong predecessor types. Meeting a positive seat-layer result with that R5 violation remains `Violation`. This is a missing composition rule, not a missing discharge fixture.

   **Proposed fix:** specify the precise fan-in verification adaptation for discharges, including zero counted acts and empty `:caused-by`, while keeping meta acts outside ordinary R5 predecessor checking.

7. **MAJOR — REQ-2046, REQ-2005: zero counted acts bypass anchor validation.**

   Quoted phrase: “For each referenced act of the counted performative, the system SHALL run the anchor walk”.

   Scenario: Eli shares to Diag as `G` before request `O`, with `G ∈ A(O)`. Eli and Fay then resign; Diag stays live and does not report. The genuine round anchored at `O` cannot close. With no referenced reports, the collector instead names thread root `h0` as `:anchor`, cites the two resigns, and obtains membership `{Eli,Fay}`. Every member of that substituted set is discharged, and no walk checks that the protocol's `report` actually follows a `request`, rather than the root. The round clauses therefore accept this fabricated anchor once their intended zero-report R5 path exists; the current R5 contradiction in finding 6 merely masks it. The root-anchor acceptance example is not limited to protocols whose static walk actually ends at the root.

   **Proposed fix:** check the anchor against the statically determined stopping performative/root even when there are no counted acts, before evaluating membership or discharges.

8. **MAJOR — REQ-2005, REQ-2041, REQ-2046: mixed-role conjunctions have no defined round treatment.**

   Quoted phrases: “whose predecessor role is dynamic”; “A fan-in over a fixed role omits `:anchor`”.

   Scenario: a legal SPEC-002 conjunction is `(all report note)`, with `report` sent by dynamic indexed responder and `note` by fixed indexed observer. Both follow singleton commander `request`. Choose endpoint annotations containing commander on both predecessors and all relevant roles on request, so the type-level locality check passes. Does the close require an anchor because it counts responder, or forbid one because it also counts fixed observer? Is membership and discharge computed separately for each `(performative, role)`, or as one set of positions? If the two types have different singleton openers, a single `:anchor` cannot represent both walks. SPEC-002 permits heterogeneous conjunctions, and no installation rule rejects or defines this shape. “One position never counts twice” also does not say whether two required performatives from the same role each require coverage of that position.

   **Proposed fix:** define counting and anchors per required performative/role, or explicitly reject the unsupported conjunction shapes at installation.

9. **MAJOR — REQ-2048 versus SPEC-014 REQ-608/CON-602: the grant-time cast is not a defined input to the existing checker.**

   Quoted phrase: “Its cast is the root cast, the live principal positions of `A(grant)`, and the new position.”

   Scenario: root responder Eli shares a second position to Eli himself; no rule forbids this. A second grant now needs a check with two distinct responder positions held by the same key. SPEC-014 `Cast.indexed` is a set of keys, so it collapses those positions. Conversely, after root Eli moves to Fay, combining the root cast with live positions can retain old Eli, substitute Fay, or include both; the sentence gives no construction. A moved singleton creates the same old-key/current-key question. R6 evaluates `(performative, occupant)` instances, while the new runtime obligation is attached to positions. An implementer cannot simply call the old API with the three listed ingredients and obtain a specified result. The admitted BUG-640 limitation is separate from this representation problem.

   **Proposed fix:** define position-instantiated locality and an exact conversion/checking API, including removed roots, moved holders and multiple positions sharing one key.

10. **MAJOR — REQ-2039, REQ-2008/2009; CON-2000/2002: appointment has no complete policy or attenuation semantics.**

    Quoted phrases: “whose mode or redelegate flag the dialect policy of its role does not permit”; “`facet` < `share` < `transfer`”.

    Scenario: commander declares `:appoint (responder)` and appoints New into responder. REQ-2039 permits this. If REQ-2008 checks the granted role's mode policy, responder cannot permit `appoint` in `:delegate` at all: CON-2000 has no such mode. The spec must explicitly make the source's appointment clause the relevant permission. Even granting that exception, the new seat's mode is `Appoint` because granted seats take the grant's attributes. Suppose it has `:redelegate #t` and New shares responder onward. Comparing `Share` to parent mode `Appoint` is undefined by the narrowing order. An appointment thus does not establish a specified delegation ceiling for its otherwise permitted descendants.

    **Proposed fix:** distinguish appointment permission from within-role delegation strength and assign the appointee an explicit delegation ceiling from the target role's policy.

11. **MAJOR — REQ-2040, REQ-2017, REQ-2045; TEST-2037: revoking a transfer intent lacks an authority path.**

    Quoted phrases: “The transfer grant itself is never a live seat and issues nothing”; “That seat SHALL be in `G`'s chain before `G`.”

    Scenario: Dana offers commander to Fay in transfer grant `T`; Fay accepts in `A`. Dana concurrently withdraws `T` with `V :grant T :under (root commander @dana)`, whose own past omits `A`. To admit `V`, REQ-2040 needs the chain of target seat `G=T`. But transfer `T` has no seat, no `Grant(T)` and no chain under Terminology. One reader rejects `V` as not a seat; another invents an intent chain `[C,T]` and admits it. For the second reader, REQ-2017 suppresses `Moved(A)` when `{T,A,V}` is observed; for the first reader it remains issued. The revoke-of-transfer subcase in TEST-2037 relies on the unspecified second reading. Directly revoking accept hash `A` is also not defined as revoking a grant; it cannot be assumed to mean the same operation.

    **Proposed fix:** define a separate revocable transfer-intent target and its authorising ancestor path, with explicit pre-accept, concurrent and post-accept withdrawal semantics.

12. **MAJOR — REQ-2025/2026/2027, NFR-2003; TEST-2055: finality is not total over messages.**

    Quoted phrases: “a finality verdict for each message `m`”; “its `:order` lists every removal in its batch whose admission verdict is `Valid`”.

    Scenario: let `E2` cite admitted `E1` as `:prev`: `E1` itself is in `B2`, since an epoch is excluded from its own authority past. Epochs are neither dialect acts, grants nor removals, and have no finality rule. The same totality question applies to the thread-root wrapper. TEST-2055 nevertheless demands that every covered message leave `Pending`. Admission-invalid removals also need an explicit traversal rule: Cy's unauthorised resign `Rbad` cannot appear in `E1.:order`, yet a literal traversal of only ordered removals never marks it void. If “Walk the batch” is intended to visit these unlisted messages separately and use step 2's `Otherwise`, say so. Epochs still lack a verdict under either interpretation.

    **Proposed fix:** provide finality cases for every message category, and explicitly mark covered, admission-invalid removals void without listing them as applicable removals.

13. **MAJOR — REQ-2025/2047; Terminology, Discharge: finality depends on an unspecified discharge witness.**

    Quoted phrase: “The same when a discharge its count relied on is `Void`.”

    Scenario: Fay signs two concurrent resigns `R1` and `R2` of her root responder seat, as TEST-2027 expressly permits. Close `C` cites both in `:seen` and Eli's report in `:caused-by`. Fay's position is empty and the admission count succeeds. Epoch `E1` covers everything and lists `R1,R2`: `R1` applies and is `Final`; `R2` is `Void`. One reader uses `{R1}` as the discharge that the count relies on and finalises `C`; another treats the collected emptying removals `{R1,R2}` as its discharge and returns `Void(EntryVoid)`. No witness is designated in the message or returned by admission, and no existential, universal or minimal-proof rule selects one. The same ambiguity arises from redundant ancestor and direct removals. A redundant, losing removal can therefore poison an otherwise justified close depending on the verifier's unstated proof selection.

    **Proposed fix:** define finality by whether the position has a sufficient effective discharge in the covering fold, or specify an explicit, deterministic discharge witness and its validation.

14. **MAJOR — OBS-2000, CON-2003: rejection reasons are incomplete and the uniqueness contract contradicts its table.**

    Quoted phrases: “one variant per rejecting REQ”; “Every admission rejection SHALL carry exactly one `CapViolation` variant.”

    Scenario: a well-formed close names the correct anchor and references Eli's report, but omits live member Fay's report and any discharge. It fails coverage; neither `MixedRounds` nor `PositionOutsideRound` applies, and no missing-member variant is provided. A dynamic fan-in omitting `:anchor` similarly lacks a named semantic error. An inherited R5 rejection has no wrapper variant despite OBS-2000 applying to every admission rejection. Conversely, REQ-2003 has three table variants, and `LacksAuthorityToRemove` covers two REQs, contradicting literal one-to-one attribution. For an act whose signer is wrong and seat is dead, two variants apply without a specified selection rule, so reason-level determinism is also unspecified.

    **Proposed fix:** specify one variant per rejecting condition, wrappers for inherited failures, complete coverage/anchor errors, and deterministic precedence when several checks fail.

15. **MAJOR — CON-2001, REQ-2002, NFR-2001: fixed field positions do not establish one canonical serialisation.**

    Quoted phrase: “That order is the canonical form for hashing, so each value has exactly one serialisation.”

    Scenario: the same typed grant value has omitted `:redelegate` or explicit `:redelegate #f`. `:acts (report finding)` and `:acts (finding report)` express the same set. `:seen (H1 H2)` and its reversal express the same authority links; `:fixed` and role policy sets have analogous permutations. `nat` also admits `01` and `1` as written, without a stated canonical decimal rule in this contract. The optional keywords each have a shown position, but the contract does not say whether these syntactic distinctions remain part of the hashed value or are normalised after interpretation. Fixed field placement alone does not establish the claimed uniqueness. `:order` is different: sorting it would destroy its intended meaning.

    **Proposed fix:** define hash identity at the raw-AST or typed-value level and its default/set/numeral rules, while preserving arbiter `:order` as an ordered sequence.

16. **MAJOR — REQ-2043; CON-2001: `anchor` can collide with a dialect parameter.**

    Quoted phrase: “a performative parameter named `under` or `seen`”.

    Scenario: an otherwise valid dialect declares a fan-in performative with its own parameter named `anchor`, intended to carry an application hash. REQ-2043 permits installation. CON-2001 now attaches capability `:anchor` to that same act. One occurrence cannot unambiguously serve the application parameter and the round anchor; two occurrences conflict with canonical field recognition. This affects parsing and signing before any seat check.

    **Proposed fix:** reserve `anchor` alongside the other authority parameters and define the full placement of authority attributes relative to dialect parameters and ordinary message metadata.

17. **MAJOR — REQ-2035, REQ-2001/2006/2040; Purity Boundary Map: installation rejection is neither a complete enable gate nor rollback.**

    Quoted phrases: “Rejecting by default keeps every deployed consumer on SPEC-014 behaviour until it opts in”; “Setting the option back to `Reject` is the rollback”.

    Scenario: a policy-free SPEC-014 dialect installs under `Reject`. Its root can still name an arbiter, and a root holder can resign: REQ-2040 has no policy check, while REQ-2001 forbids grants/transfers/reseats but does not forbid resign. The capability verifier can therefore change recipients and discharge obligations without any policy-bearing installation being accepted. Separately, after a hub enables a policy-bearing dialect and opens threads, switching the installer to `Reject` stops no existing grant, removal or finality processing. It cannot roll back the failing active traffic. The consumer has no specified runtime scope, observe-only mode, notification point, rejection/finality rollout criteria or procedure for already-enabled threads. Even the evidence path needs wiring: `CapVerdict::finality` can say `Frozen` without carrying hashes, so the shell must separately obtain the evidence exposed by `epoch_fold`. Naming cbcl-bus wiring as unwritten does not supply these controls.

    **Proposed fix:** define an explicit per-consumer/per-thread activation contract, observe-only rollout and runtime stop/continuation policy that preserves established verdicts, with notifications and observable seat/finality events.

18. **MAJOR — Orientation, Terminology, REQ-2001/2006/2017/2027/2031/2046; ADR-2009 and the concept pages: the entry vocabulary predicts different behaviour.**

    Quoted phrases and concrete divergences:

    | Phrase | Scenario and conflicting definition |
    |---|---|
    | Orientation: “It passes to a successor only when its single termination is one accept.” | A unique observer reseat `H` issues `Reseated(H)` under REQ-2017/2031, but the Orientation's seat-state algorithm cannot issue it. ADR-2009 separately says reseat takes effect only in the fold, whereas REQ-2023 explicitly applies it at admission. |
    | Orientation: “add new grants, then apply the listed removals one by one” | In `G,R` from finding 4, this predicts `G` is added; REQ-2027 permits the current-state merge to reject it. |
    | Orientation: “any other role; its positions are the root positions.” | A singleton commander permitting only transfer/facet is fixed by this definition and still allows those grants. REQ-2001 uses fixed to mean no grants/transfers/reseats; REQ-2006's `:fixed` override and REQ-2008 disable grants. With `:fixed (commander)`, REQ-2031 nevertheless has no explicit recovery-policy override check. For a dialect-dynamic responder listed in thread `:fixed`, REQ-2046 does not say which dynamic/fixed anchor rule wins. |
    | ADR-2006/Orientation decision caption: “positions live at the round anchor” | A commander/responder position contested before an opener has no live seat. Terminology excludes only emptied positions, deliberately retaining that contested member; “live” would exclude it. |
    | `round-anchor.md`: “the one message that every counted act cites as its protocol predecessor” | Auction reveal cites its own commit, not open. REQ-2046 walks through commit. The concept page also requires a live principal seat, excluding the contested member retained by the body. |
    | ADR-2014: “a later fan-in that holds it is `Violation`” | If a later close actually references Fay's report and the other required reports, also holding Fay's resign does not invalidate admission: REQ-2047 merely stops using the resign as a substitute. The ADR needs to restrict its claim to a close that still omits the required report reference. |
    | `capability-seat.md`: “A seat never authorises more than the seat it derives from.” | A commander appointment creates a responder seat covering `report`, which the commander parent cannot send. REQ-2039 explicitly starts the target role's act set; the unconditional concept claim describes same-role narrowing only. |

    These differences affect the answers to recovery, concurrent-grant and membership examples, rather than merely shortening their explanations.

    **Proposed fix:** use distinct names for policy-disabled versus constant-position roles, and regenerate the Orientation and concept definitions from the corrected admission/fold/round rules.

19. **MAJOR — Test Specifications preamble; TEST-2020/2031/2047/2050/2052/2053: some expected results contradict the rules or need undefined fixtures.**

    Quoted phrases: “Before an epoch lists it, the reseat has no effect”; “Responder's Send steps are `{report}` and `{finding, propose-fix}`.”

    Scenario: run TEST-2031 and verify Dana's act whose authority past contains the admitted reseat before any epoch. REQ-2023 requires `Violation`, and REQ-2017 changes admission seats; the unqualified no-effect assertion requires the opposite. In TEST-2020, if “@dana's facet to @tidy” means a new grant after transfer, its error is `IssuerLacksSeat` under REQ-2007, not the promised `SeatNotLive`; if it means a pre-existing facet's use, the test must say so. TEST-2047 writes `(all bidder)`, but bidder is a role, not the auction's counted performative `reveal`; it also needs explicit facet/transfer policy variants. TEST-2050 cannot reseat an immediate shared parent (only root positions are reseatable), and the incident responder has no recovery policy. A suitable appointed descendant of commander, or a policy variant, must be specified. TEST-2052's three root resigns need a three-responder cast, and its zero-report success contradicts unchanged R5 as in finding 6. Finally, the preamble never declares a choice between `finding` and `propose-fix`, their predecessors or complete endpoint annotations. Its listed further sends do not determine TEST-2053's Send-step partition or a successful REQ-608 call. Treating them as independent sends would reject the test's supposedly live `(finding report)` share.

    **Proposed fix:** provide complete installable dialect/cast variants with explicit choices, endpoints and causal links, and make the before-epoch, facet-use and all-discharge assertions match the chosen normative semantics.

20. **MAJOR — TEST-2005/2020/2027/2037/2045–2055: the rewritten suite leaves the new mechanisms partially untested.**

    Quoted phrase: “Each covers the positive case, the negative-input case and, where the REQ prohibits an action, the prohibited case.”

    The following are concrete surviving mutations or missing assertions. A surviving mutation means the described test can pass with the named part of its requirement unimplemented; it does not mean the entire test is worthless.

    | Test | Adversarial adequacy check |
    |---|---|
    | 2005 | A checker rejecting only `(all …)` stops can pass both installation cases while accepting forbidden multi-alternative predecessors and stops at another indexed role. Add each stop shape. |
    | 2020 | An accept implementation copying all parent attributes passes the described before/after and facet cases while ignoring transfer restrictions (finding 3). Specify a narrowed, bounded transfer and assert the moved attributes. |
    | 2027 | A fold supporting just ordered accept conflicts and duplicate resigns passes, while having arbitrary grant/removal merges, omitting expiry or admitting unlive grants. Assert both concurrent-grant placements and the full grant/removal checks. |
    | 2031 | Resolve the admission/finality contradiction in finding 19 first. The positive root recovery does not exercise a moved or contested target, sequential reseats or recovery under a thread `:fixed` override. |
    | 2037 | The two-transfer case does not test two distinct concurrent accepts of the *same* transfer. The revoke-of-transfer case needs the target-chain definition in finding 11. |
    | 2045 | `parse(serialise(x)) == x` alone can pass a permissive parser that also accepts duplicate/misordered authority fields and malformed inputs. It does not test canonical uniqueness of equal values. Add negative recognition and canonical-equivalence oracles. |
    | 2046 | Rejecting Cy by key comparison passes while ignoring seat liveness for a former holder's resign. Add a former holder whose own past includes its accepted transfer or earlier resign, plus a legitimate granted-seat holder. |
    | 2047 | After fixing its fixture, counting positions correctly on the listed cases does not check per-performative coverage for heterogeneous conjunctions. It also needs a complete fan-in result with surplus non-member references, not only a position-count helper. |
    | 2048 | In the first case, the transfer already fails issuer admission, so rejecting its accept as an invalid designation can pass without checking accept-time parent liveness or withdrawal. The wrong-recipient signer tests one independent clause. Add a valid transfer whose parent has since terminated, a revoked intent and a successful accept. |
    | 2049 | The two-hop case exercises live descendants of a contest, but only asserts no live seat. An implementation can leave spurious seats issued and mask them as non-live. Assert the entire issued/successor structure; finality distinguishes non-issued from removed. |
    | 2050 | A verifier marking descendants non-live, without marking them effectively removed or their positions emptied, can pass seat-use checks and fail discharge. State whether the assertion is removal, non-liveness or vacancy, and check all relevant outputs. |
    | 2051 | The positive/negative membership and mixed-request cases detect their respective omissions. They do not cover a fabricated anchor with zero counted acts (finding 7), mixed-role conjunctions or a contested position in the anchor past. |
    | 2052 | The explicit direct-resign and parent-revoke discharge cases are useful, but require a precise cascade assertion. A predicate forbidding every position with a historical accept still passes the transfer-then-report case while failing transfer-then-resign. Add the latter, a contested-then-cascade case and multiple possible discharge witnesses. |
    | 2053 | Repair the undeclared choice fixture first. Its unlive-subset examples can pass while the fold entirely omits REQ-2048. A root-only grant-time locality check can also pass the stated BUG-640 shape while losing position multiplicity from finding 9. Add an epoch and the aliased-position cast. |
    | 2054 | The core schedule has Eli report and Fay resign; a checker supporting only direct resign discharges passes. Diag is outside the round, so revoking its share does not exercise a member cascade discharge. The property half merely excludes residual `Unknown`: a verifier returning `Violation` for every fully resolved fan-in satisfies it while implementing no deadlock-freedom guarantee. Assert existence of a `Valid` close for eligible generated rounds. |
    | 2055 | `no finality stays Pending` accepts a verifier that returns `Final` for every covered message, including invalid ones. Require the correct `Final`/`Void(reason)`/`Frozen` result and include admission-invalid removals and epochs (finding 12). The admission arrival cases also need all unrelated checks initially satisfied. |

    **Proposed fix:** supply isolated fixtures for each clause and assert full states and exact verdicts, then demonstrate that each named mutation fails a core example or property.

21. **MINOR — REQ-2045/2037; Orientation Open: retried accepts are a documented but still actionable denial-of-seat case.**

    Quoted phrases: “two or more terminations in `S`, at least one an accept”; “retried accepts”.

    Scenario: Fay signs concurrent accepts `A1` and `A2` of the same transfer `T`, with different authority metadata producing distinct hashes. Both pass REQ-2045 independently. A message seeing both has no successor, even though both accept the same offer for the same holder. No adversary or conflicting recipient is needed. The Open entry acknowledges the issue; TEST-2037 currently covers different transfers instead. This is distinct from re-delivering the same hash, which the set naturally deduplicates.

    **Proposed fix:** state whether acceptance identity is the transfer or the accept hash, and either coalesce equivalent accepts or explicitly expose the retry hazard in the API and core tests.

22. **MINOR — Orientation and Terminology: several load-bearing terms arrive before a usable definition.**

    Quoted phrases: “through its own position's acts”; “whose projection has no Send step”.

    Scenario: the Orientation-only reader meets `act`, `meta act`, `authority past`, `indexed`, `singleton`, counted fan-in, and later `principal seat` before their full definitions; singleton/indexed are never defined locally beyond naming the cardinalities. The Orientation explains fan-in after already using it in the anchor definition. REQ-2038 uses Send step before REQ-2048 introduces its new grouped meaning, while SPEC-014 uses Send step for one performative's `LocalStep::Send`. In the fixture, `{finding, propose-fix}` is therefore either two SPEC-014 Send steps or one SPEC-020 Send step, with a different narrowed-grant result. Resolving this requires reading the later grouping rule and inventing the missing fixture choice, rather than understanding the earlier term.

    **Proposed fix:** define the minimal cardinality/act/fan-in vocabulary in the Orientation and name the grouped concept separately, such as a send-choice obligation.

## Checks that did not produce an additional finding

- **Finality stability:** once `E(m)` and its entire authority past are fixed, a later non-equivocating epoch cannot change the specified verdict of `m`; removals after its covering epoch are outside its decision horizon. I found no separate `Final → Void` counterexample based solely on later information. The unresolved fold in finding 4 prevents claiming a unique verdict in the first place.
- **Fan-in finality termination:** a referenced counted act or discharge is in the fan-in's proper authority past. Recursing through counted fan-ins therefore descends the signed DAG. A discharge depending causally on that same fan-in cannot also occur in its authority past without a cycle. No extra finality-dependency cycle is required by REQ-2025.
- **Arbiter ordering:** an arbiter favouring a concurrent thief's transfer and voiding the other side is explicitly allowed by ADR-2005. That is not an undisclosed guarantee of honest-sender priority. The unspecified grant/removal merge is a different defect.
- **Non-member references:** rejecting an explicitly referenced post-anchor position is consistent with SPEC-014 TEST-639's rejection of a surplus non-member reveal. Admission of the late position's own act does not imply that a fan-in may count it.
- **Send-step information:** SPEC-014's projection identifies Send performatives and inherits the causal protocol; REQ-603 supplies the choice sets. These contain the information needed to derive the stated grouping. The ungrounded TEST-2053 fixture and the position-to-cast conversion are the concrete problems, rather than an inherent loss of choice information in `project`.
- **Purity:** read-only store access and processing arbiter epochs as input messages preserve the pure-core boundary. Runtime enablement, evidence return and operational recovery remain incomplete as identified above; purity alone does not supply them.

## Verdict

**Not implementable as written.** The next revision must first give a well-founded seat-state definition with explicit replacement targeting, cascade/vacancy semantics and transfer attenuation; make the epoch fold deterministic and preserve every non-liveness grant check; and define how discharges compose with R5. Those are prerequisites for meaningful executable examples and stability properties. Then specify anchor validation for zero-report rounds, position-instantiated locality and total verdict/error APIs, repair the contradictory fixtures, and define a consumer enable/observe/rollback contract. A successful pass of the currently written tests would not establish these properties.

## Comprehension

This prediction starts from the Orientation alone; body-dependent qualifications are explicit. Assume the intended incident policy, valid signatures and complete recipients, and interpret “citing” as Eli's report in `:caused-by` and Fay's resign in `:seen`.

- Dana's request fixes responder membership as the two root positions, Eli and Fay. Eli's later share to Diag creates a position outside that round. The share and Diag's report can be admitted without making Diag a required contributor to this close.
- Fay's resign empties her root position. Eli supplies its own position's report; the resign discharges Fay's position. Omitting Diag's report is allowed. **The close's predicted admission is `Valid`.** With complete protocol-valid inputs, the request, share, resign and two reports likewise have no stated admission failure in this scenario.
- Listing Fay's resign in epoch 1 makes that removal final when applied. It removes Fay's responder seat, rather than Dana's commander seat or Eli's responder seat. **If epoch 1 also covers the close and Eli's report, the predicted close finality is `Final`**, with a final counted report and a final discharge. The omitted Diag report does not participate in its count. Covered request/share/reports are likewise predicted `Final` in the absence of other removals.
- **The prompt does not say epoch 1 covers the close.** Listing the resign alone guarantees reachability of that resign and its authority past, not of a concurrent or later close. If the epoch contains only that past, the close remains **`Pending`**; the same qualification applies individually to the reports and share. The Orientation states that coverage is necessary but does not define batches or exactly how an epoch covers a message; Terminology in the body was needed to distinguish these cases rigorously.

The Orientation is enough to predict the intended admission outcome and the conditional finality outcome for this simple round. The body was needed to check the attribute placement against R5, the exact definition of epoch coverage, and the new `EntryVoid` dependency on counted acts and discharges, which the Orientation omits. If “citing the resign” instead means placing it in `:caused-by`, SPEC-014 REQ-616 makes the close's admission `Violation` and a covering epoch yields `Void(CheckFailed)`; the Orientation's `:seen` discharge wording suggests the intended correct placement but does not state that rejection rule itself.
