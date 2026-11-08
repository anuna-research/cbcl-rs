#!/usr/bin/env python3
"""SPEC-038: exercise concrete observation proof obligations in isolated copies."""
from pathlib import Path
import re
import subprocess
import tempfile

root = Path(__file__).resolve().parents[1]
module = "StateLVar"
source = (root / f"lean-cbcl/LeanCbcl/{module}.lean").read_text()
mutants = [
    ("dependency-fault-ignored", "if dependencyFault = true ∨ state = ⊤ then", "if state = ⊤ then", "thresholdRead_fault_first"),
    ("raw-history-discarded", "lift (fun a => FinSet.mk [a]) A", "FinSet.mk []", "rawHistory_eq"),
    ("initializer-fault-hidden", "| .top evidence => .fault evidence", "| .top _ => .value (FinSet.mk [])", "domain_fork_fault"),
    ("freeze-cut-ignored", "exact A.filter (fun a => decide (Ancestor world a f))", "exact A", "causalCut_agreement"),
    ("freezer-excluded-from-cut", "decide (Ancestor world a f)", "decide (Ancestor world a f ∧ a ≠ f)", "freezer_in_cut"),
    ("freeze-witness-address-dropped", "(address = a.addr ∨ address = b.addr)", "address = a.addr", "eventual_freeze_conflict"),
]
suites = [(module, source, mutants), ("StateContext",
    (root / "lean-cbcl/LeanCbcl/StateContext.lean").read_text(), [
    ("root-contribution-dropped", "if a.preds.isEmpty then", "if false then", "recognized_root_value"),
    ("invalid-root-hidden", "| .one address none => .fault {address}", "| .one _ none => .pending", "invalid_root_faults"),
    ("context-fault-hidden", "| .top evidence => .fault evidence", "| .top _ => .pending", "display_quasi"),
    ("context-evidence-dropped", "| .top evidence => .fault evidence", "| .top _ => .fault {}", "fault_evidence"),
])]
resource_source = (root / "lean-cbcl/LeanCbcl/StateResource.lean").read_text()
resource_tests = (root / "lean-cbcl/LeanCbcl/StateResourceTests.lean").read_text().split("\n", 1)[1]
suites.extend([
    ("StateResource", resource_source + "\n" + resource_tests, [
        ("resource-cause-hidden", "exact if Fault c decode A then", "exact if False then", "unsupported_fault"),
        ("resource-budget-invented", "checkedAdd initial (if headroom then debited else credited)",
         "checkedAdd (initial + 100) (if headroom then debited else credited)", "insufficient_budget"),
        ("resource-shorter-tip-selected", "if C.length < D.length then D else C",
         "if C.length < D.length then C else D", "merge_owner_tips_union"),
        ("headroom-key-order-matters", "∀ owner, owner ∈ (accounts op.data.selected.headroomAllocations).map Prod.fst ↔\n      owner ∈ (accounts op.data.selected.initialAllocations).map Prod.fst",
         "(accounts op.data.selected.headroomAllocations).map Prod.fst = (accounts op.data.selected.initialAllocations).map Prod.fst", "reordered_headroom_valid"),
        ("resource-overflow-ignored", "if -(2^127) ≤ n ∧ n < 2^127 then", "if True then", "checked_overflow"),
    ]),
    ("StateObservation", (root / "lean-cbcl/LeanCbcl/StateObservation.lean").read_text(), [
        ("product-fault-witness-discarded", "| some a, some b => some (a ∪ b)",
         "| some a, some _ => some a", "unionError_grows"),
    ]),
    ("StateObservationPlan", (root / "lean-cbcl/LeanCbcl/StateObservationPlan.lean").read_text(), [
        ("derived-frozen-value-discarded", "| .snapshot v | .context v | .reached v | .frozen _ v _ => some v",
         "| .snapshot v | .context v | .reached v => some v\n  | .frozen _ _ _ => none", "derived_frozen_payload"),
        ("threshold-dependency-fault-discarded", "| _, .threshold spec source => .join (.threshold spec) (path source)",
         "| _, .threshold spec _ => .threshold spec", "threshold_dependency_fault_first"),
    ]),
])
native_tests = (root / "lean-cbcl/LeanCbcl/StateNativeRefinementTests.lean").read_text()
linked_reached = re.search(r"theorem source_linked_threshold_reached[\s\S]*?(?=\ntheorem)", native_tests).group(0)
linked_source = (root / "lean-cbcl/LeanCbcl/StateObservationPlan.lean").read_text()
linked_source += "\nnamespace CBCL.StateNativeRefinementTests\nopen State StateObservationPlan\n" + linked_reached + "\nend CBCL.StateNativeRefinementTests\n"
suites.extend([
    ("StateResourceNative", (root / "lean-cbcl/LeanCbcl/StateResourceNative.lean").read_text(), [
        ("empty-native-allocation-accepted", "!rows.isEmpty && rowsCheck rows", "rowsCheck rows", "empty_allocations_rejected"),
        ("native-account-prefix-ignored", "decide (s.toList.head? = some '@') && decide (1 < s.length)",
         "decide (1 < s.length)", "accountCheck_iff"),
        ("native-incoming-chunk-discarded", "let total ← checkedSum ownerAmounts", "let total := (0 : Int)", "addIncoming_eq"),
    ]),
    ("StateResourceSummary", (root / "lean-cbcl/LeanCbcl/StateResourceSummary.lean").read_text(), [
        ("native-sequence-not-incremented", "let next := {summary with sequence := summary.sequence + 1}",
         "let next := summary", "record_refinement"),
        ("native-recipient-substituted", "update summary.sentRights recipient amount",
         "update summary.sentRights node.data.signer amount", "record_refinement"),
    ]),
    ("StateObservationPlan", linked_source, [
        ("source-linked-threshold-no-longer-reads-source", "alternatives.find? (fun q => test q value)",
         "alternatives.find? (fun _ => false)", "source_linked_threshold_reached"),
        ("source-linked-threshold-fault-discarded", "| _, .thresholdOn _ _ source => path source",
         "| _, .thresholdOn _ _ _ => .clear", "thresholdOn_dependency_fault_first"),
    ]),
    ("StateRuleRefinement", (root / "lean-cbcl/LeanCbcl/StateRuleRefinement.lean").read_text(), [
        ("native-freeze-recomputes-current-source", "(fun C => sourceData (source C)) A",
         "(fun _ => sourceData (source A)) A", "freeze_source_refinement"),
    ]),
])
kahn_tests = (root / "lean-cbcl/LeanCbcl/StateResourceKahnTests.lean").read_text()
kahn_tests = "\n".join(line for line in kahn_tests.splitlines() if not line.startswith("import "))
suites.extend([
    ("StateResourceKahn", (root / "lean-cbcl/LeanCbcl/StateResourceKahn.lean").read_text() + "\n" + kahn_tests, [
        ("structural-cycle-discarded", "  reduceFuel parents nodes.length nodes\n", "  ([] : List α)\n", "cycle_pass_retains_nodes"),
        ("missing-reference-released-by-budget-pass", "(parents node).all (fun parent => known.contains parent && !remaining.contains parent)", "(parents node).all (fun parent => !remaining.contains parent)", "budget_pass_keeps_missing_reference"),
    ]),
    ("StateResourceCycle", (root / "lean-cbcl/LeanCbcl/StateResourceCycle.lean").read_text(), [
        ("native-cycle-check-always-accepts", "(StateResourceKahn.nativeKahn (parents (nodes c F)) (nodes c F)).isEmpty", "true", "native_cycle_certificate_iff"),
    ]),
])
suites.append(("StateResourceCache", (root / "lean-cbcl/LeanCbcl/StateResourceCache.lean").read_text(), [
    ("cache-uses-empty-owner-prefix", "else (cache previous).map Prod.snd", "else some empty", "previous_prefix"),
    ("cache-tip-keeps-shorter-prefix", "left.2.sequence < right.2.sequence", "right.2.sequence < left.2.sequence", "cached_tip_union"),
    ("cache-stores-parent-summary", "some (node,next) else cache address", "some (node,own) else cache address", "advance_valid"),
]))
suites.append(("StateResourceStructure", (root / "lean-cbcl/LeanCbcl/StateResourceStructure.lean").read_text(), [
    ("foreign-owner-check-accepts-all", "parent.data.signer == node.data.signer else true", "true else true", "previousOwnerCheck_iff"),
    ("fork-check-accepts-all", "left.id == right.id else true", "true else true", "forkCheck_iff"),
]))
suites.extend([
    ("StateResourceCones", (root / "lean-cbcl/LeanCbcl/StateResourceCones.lean").read_text(), [
        ("dependency-cone-discarded", "entry == node || parents.any (fun parent => parent.2.contains entry)", "entry == node", "unionCone_member"),
        ("all-dependency-lookups-skipped", "if address = op.id then gather op cache references else do", "if true then gather op cache references else do", "gather_lookup"),
    ]),
    ("StateResourceFrontier", (root / "lean-cbcl/LeanCbcl/StateResourceFrontier.lean").read_text(), [
        ("dependency-frontier-not-merged", "| some old,some incoming => chooseTip cache old incoming", "| some old,some _ => some old", "merge_represents"),
    ]),
    ("StateResourceBudget", (root / "lean-cbcl/LeanCbcl/StateResourceBudget.lean").read_text(), [
        ("incoming-headroom-map-substituted", "if headroom then entry.2.sentHeadroom recipient else entry.2.sentRights recipient", "entry.2.sentRights recipient", "readIncoming_refinement"),
    ]),
])
suites.extend([
    ("StateResourceOutgoing", (root / "lean-cbcl/LeanCbcl/StateResourceOutgoing.lean").read_text(), [
        ("outgoing-map-side-substituted", "  checkedSum (owners.map (fun recipient => if headroom then summary.sentHeadroom recipient else summary.sentRights recipient))\n", "  checkedSum (owners.map (fun recipient => summary.sentRights recipient))\n", "native_outgoing_refinement"),
    ]),
    ("StateResourceLocalBudget", (root / "lean-cbcl/LeanCbcl/StateResourceLocalBudget.lean").read_text(), [
        ("local-budget-credit-debit-reversed", "let raised ← checkedAdd initial (if headroom then own.debited else own.credited)", "let raised ← checkedAdd initial (if headroom then own.credited else own.debited)", "native_local_budget_refinement"),
    ]),
])
suites.extend([
    ("StateResourceMachine", (root / "lean-cbcl/LeanCbcl/StateResourceMachine.lean").read_text(), [
        ("recorded-node-own-tip-not-updated", "setOwn tips node else machine.tips address", "tips else machine.tips address", "recordResult_invariant"),
    ]),
])
suites.append(("StateResourceCounters", (root / "lean-cbcl/LeanCbcl/StateResourceCounters.lean").read_text(), [
    ("native-waiting-count-not-decremented", "if address = child then counts address - 1 else counts address", "counts address", "decrementAll_value"),
    ("native-parent-waiting-list-not-removed", "if address = parent then [] else state.waiters address", "state.waiters address", "pop_invariant"),
    ("native-ready-child-not-enqueued", "ready child || (children.contains child && decide (decrementAll counts children child = 0))", "ready child", "ready_pop_refinement"),
]))
suites.extend([
    ("StateResourceAuthorization", (root / "lean-cbcl/LeanCbcl/StateResourceAuthorization.lean").read_text(), [
        ("authorization-always-faults", "if nativeBudgetCheck c op node own machine.summaries (mergedTips machine.summaries machine.tips parents) then", "if false then", "checkedStep_budget_fault"),
    ]),
    ("StateResourceWorklist", (root / "lean-cbcl/LeanCbcl/StateResourceWorklist.lean").read_text(), [
        ("budget-worklist-skipped", "runFuel e e.known.length (initialWorklist e) StateResourceMachine.initial initialGhost", "runFuel e 0 (initialWorklist e) StateResourceMachine.initial initialGhost", "native_worklist_verified"),
    ]),
])
aggregate_tests = (root / "lean-cbcl/LeanCbcl/StateResourceAggregateTests.lean").read_text()
aggregate_tests = "\n".join(line for line in aggregate_tests.splitlines() if not line.startswith("import "))
finalize_source = "import LeanCbcl.StateResourceTests\n" + (root / "lean-cbcl/LeanCbcl/StateResourceFinalize.lean").read_text() + "\n" + aggregate_tests
suites.extend([
    ("StateResourceAggregate", (root / "lean-cbcl/LeanCbcl/StateResourceAggregate.lean").read_text(), [
        ("aggregate-transfer-credit-discarded", "addAccount owners debited recipient amount", "addAccount owners debited recipient 0", "transferAccounts_success"),
    ]),
    ("StateResourceFinalize", finalize_source, [
        ("aggregate-capacity-always-rejected", "if checkedAdd value totalSpace == some cap then", "if false then", "finishBalances_bounded"),
        ("aggregate-floor-discarded", "let value ← checkedAdd totalRights c.floor", "let value := totalRights", "finishBalances_unbounded"),
        ("aggregate-negative-guard-discarded", "if owners.any (fun owner => decide (rights owner < 0)) ||\n      headroom.any (fun space => owners.any (fun owner => decide (space owner < 0))) then none else do", "if false then none else do", "negative_final_budget_rejected"),
    ]),
])
installed_tests = (root / "lean-cbcl/LeanCbcl/StateInstalledCompilerTests.lean").read_text()
installed_tests = "\n".join(line for line in installed_tests.splitlines() if not line.startswith("import "))
suites.extend([
    ("StateResourcePreflight", (root / "lean-cbcl/LeanCbcl/StateResourcePreflight.lean").read_text(), [
        ("accepted-foreign-parent-ignored", "operationVerbCheck c parent.data.selected.verb", "true", "foreignCheck_iff"),
    ]),
    ("StateResourceVerifier", (root / "lean-cbcl/LeanCbcl/StateResourceVerifier.lean").read_text(), [
        ("native-preflight-fault-hidden", "| .fault _ => .fault", "| .fault _ => .pending", "native_verifier_certificate_iff"),
    ]),
    ("StateInstalledCompiler", (root / "lean-cbcl/LeanCbcl/StateInstalledCompiler.lean").read_text(), [
        ("installed-post-discarded", "return .map post (← earlier.lookup name)", "return .map id (← earlier.lookup name)", "compile_rule_refinement"),
    ]),
    ("StateInstalledClause", (root / "lean-cbcl/LeanCbcl/StateInstalledClause.lean").read_text() + "\n" + installed_tests, [
        ("installed-freeze-discarded", "return match field.freeze with | none => source | some spec => .freeze spec source", "return source", "compile_field_refinement"),
        ("late-freeze-declaration-ignored", "fields.map (fun (name,rule) => (name,⟨rule,freezes.lookup name⟩))", "fields.map (fun (name,rule) => (name,⟨rule,none⟩))", "late_freeze_attaches_before_dependencies"),
    ]),
])
lowering_tests = (root / "lean-cbcl/LeanCbcl/StateInstalledLoweringTests.lean").read_text()
lowering_tests = "\n".join(line for line in lowering_tests.splitlines() if not line.startswith("import "))
suites.extend([
    ("StateObservationPlan", (root / "lean-cbcl/LeanCbcl/StateObservationPlan.lean").read_text(), [
        ("reached-embedding-becomes-snapshot", "| .reached v => .reached (f v)", "| .reached v => .snapshot (f v)", "embed_preserves_reached"),
        ("context-embedding-becomes-snapshot", "| .value v => .context (embed v)", "| .value v => .snapshot (embed v)", "contextAs_value"),
    ]),
    ("StateInstalledLattice", (root / "lean-cbcl/LeanCbcl/StateInstalledLattice.lean").read_text(), [
        ("query-empty-alternatives-allowed", "!queries.isEmpty && decide queries.Nodup", "true && decide queries.Nodup", "alternativesCheck_iff"),
        ("query-duplicate-alternatives-allowed", "decide queries.Nodup", "true", "alternativesCheck_iff"),
        ("query-conflict-top-allowed", "queries.all (fun q => decide (q ≠ ⊤))", "true", "alternativesCheck_iff"),
        ("query-detached-from-source-carrier", "field.algebra,field.contribution,query.alternatives", "field.algebra,(fun _ => @BoundedJoinSemilattice.top field.Carrier field.algebra),query.alternatives", "query_source_coherence"),
    ]),
    ("StateInstalledLowering", (root / "lean-cbcl/LeanCbcl/StateInstalledLowering.lean").read_text() + "\n" + lowering_tests, [
        ("query-source-recognition-bypassed", "if policy.check elements then some (.threshold elements policy.test source)", "if true then some (.threshold elements policy.test source)", "lower_rule_refinement"),
        ("supersede-threshold-source-allowed", "match freezes.lookup source with | none => true | some spec => spec.policy", "true", "supersede_threshold_source_rejected"),
    ]),
])
finite_projection_tests = (root / "lean-cbcl/LeanCbcl/StateFiniteProjectionTests.lean").read_text()
finite_projection_tests = "\n".join(line for line in finite_projection_tests.splitlines() if not line.startswith("import "))
suites.extend([
    ("StateFiniteTable", (root / "lean-cbcl/LeanCbcl/StateFiniteTable.lean").read_text(), [
        ("finite-totality-check-bypassed", "completeCheck table && lawCheck table", "true && lawCheck table", "check_iff"),
        ("finite-duplicate-input-check-bypassed", "decide (table.rows.map Prod.fst).Nodup", "true", "check_iff"),
    ]),
    ("StateFiniteProjection", (root / "lean-cbcl/LeanCbcl/StateFiniteProjection.lean").read_text() + "\n" + finite_projection_tests, [
        ("finite-stable-order-check-bypassed", "if projection.stable then", "if false then", "check_iff"),
        ("finite-projection-totality-bypassed", "(indices table).all (fun i => (projection.rows.lookup i).isSome)", "true", "check_iff"),
        ("finite-projection-scalar-check-bypassed", "projection.rows.all (fun row => scalarCheck row.2)", "true", "check_iff"),
        ("finite-contribution-first-match-only", "rows.filter (fun row => act.get row.key == some row.literal)", "(rows.take 1).filter (fun row => act.get row.key == some row.literal)", "every_matching_row_contributes"),
    ]),
    ("StateInstalledFinite", (root / "lean-cbcl/LeanCbcl/StateInstalledFinite.lean").read_text(), [
        ("finite-source-fault-guard-discarded", "guards := [.certified (errorSpec field)]", "guards := []", "concrete_finite_read_refinement"),
        ("finite-native-domain-writers-discarded", "| some evidence => some (evidence ∪ writers field A)\n  | none => (topErrorSpec field).read A", "| some evidence => some evidence\n  | none => (topErrorSpec field).read A", "native_error_refinement"),
    ]),
])

finite_read_tests = (root / "lean-cbcl/LeanCbcl/StateFiniteReadTests.lean").read_text()
finite_read_tests = "\n".join(line for line in finite_read_tests.splitlines() if not line.startswith("import "))
suites.append(("StateFiniteRead", "import LeanCbcl.StateFiniteProjectionTests\n" +
    (root / "lean-cbcl/LeanCbcl/StateFiniteRead.lean").read_text() + "\n" + finite_read_tests, [
    ("finite-top-read-allowed", "current != field.table.table.top && reaches field query current", "reaches field query current", "test_top"),
    ("finite-common-upper-check-bypassed", "current == field.table.table.top || !(reaches field left current && reaches field right current)", "true", "pairCheck_iff"),
    ("finite-empty-read-accepted", "!queries.isEmpty && decide queries.Nodup", "true && decide queries.Nodup", "empty_query_rejected"),
    ("finite-raw-query-state-discarded", "test field element (state field (StateInstalledLegacy.history carrier))", "test field element field.table.table.bottom", "policy_actual_history"),
]))

authored_tests = (root / "lean-cbcl/LeanCbcl/StateAuthoredBindingsTests.lean").read_text()
authored_tests = "\n".join(line for line in authored_tests.splitlines() if not line.startswith("import "))
suites.extend([
    ("StateAuthoredBindings", (root / "lean-cbcl/LeanCbcl/StateAuthoredBindings.lean").read_text() + "\n" + authored_tests, [
        ("authored-freeze-contributors-use-empty-history", "contributes resolvedDomains history template.footprint", "contributes resolvedDomains [] template.footprint", "materialized_progress_contributor"),
        ("authored-progress-domain-filtered", "| .progress verb => .rawVerbs [verb]", "| .progress verb => .verbs [verb]", "progress_raw_contributor"),
        ("authored-duplicate-namespace-allowed", "decide names.Nodup", "true", "lattice_and_field_namespace_shared"),
        ("authored-domain-source-environment-discarded", "environment.schema (domainFields entries)", "environment.schema []", "domain_can_reference_later_initializer"),
        ("authored-freeze-sender-role-bypassed", "if senderRole.isEmpty || !environment.schema.verbs.contains verb then", "if false then", "freeze_without_sender_role_rejected"),
    ]),
    ("StateFreezeGrowth", (root / "lean-cbcl/LeanCbcl/StateFreezeGrowth.lean").read_text(), [
        ("growing-freeze-evidence-discarded", "⟨a,b,conflict_transfer closed growth contributors conflict,which⟩", "⟨a,a,conflict_transfer closed growth contributors conflict,which⟩", "evidence_grows"),
    ]),
    ("StateFreezeScopes", (root / "lean-cbcl/LeanCbcl/StateFreezeScopes.lean").read_text(), [
        ("cached-freeze-uses-entire-history", ".frozen freezer.addr (evaluate (causalCut world whole freezer))", ".frozen freezer.addr (evaluate whole)", "cached_freeze_refinement"),
        ("cached-freezer-applied-outside-scope", "some freezer => if freezer ∈ scope then", "some freezer => if True then", "cached_freeze_refinement"),
    ]),
    ("StateCompiledFreezeGrowth", (root / "lean-cbcl/LeanCbcl/StateCompiledFreezeGrowth.lean").read_text(), [
        ("compiled-pair-error-path-discarded", "| .pair _ left right => do return .join (← earlier.lookup left) (← earlier.lookup right)", "| .pair _ left _ => earlier.lookup left", "compile_rule_path"),
        ("compiled-global-freeze-path-discarded", "| some spec => .freeze spec.verb spec.contributes spec.policy source", "| some _ => source", "compile_field_path"),
    ]),
])

suites.append(("StateNativeReader", (root / "lean-cbcl/LeanCbcl/StateNativeReader.lean").read_text(), [
    ("native-reader-freeze-fault-dropped", "(freezeFault world spec.verb spec.contributes spec.policy none whole)", "none", "full_error_refinement"),
    ("native-reader-freeze-cut-ignored", "| _, .freeze spec source, scope => frozenData (cachedFreeze world spec (fun cut => value world whole source cut) whole scope)", "| _, .freeze spec source, scope => frozenData (cachedFreeze world spec (fun _ => value world whole source whole) whole scope)", "scoped_value_refinement"),
    ("native-reader-fault-header-hidden", "| some evidence => .fault evidence", "| some _ => .data (value world whole plan whole)", "native_reader_refinement"),
]))

# Preserve the full default gate while allowing a focused continuation check.
import argparse
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--module", action="append", help="Run only this module (repeatable)")
options = parser.parse_args()
if options.module:
    unknown = set(options.module) - {name for name, _, _ in suites}
    if unknown:
        parser.error("unknown modules: " + ", ".join(sorted(unknown)))
    suites = [suite for suite in suites if suite[0] in options.module]

for module, source, mutants in suites:
    with tempfile.TemporaryDirectory(prefix="cbcl-state-lvar-") as directory:
        path = Path(directory) / f"{module}.lean"
        def compile_copy(text):
            path.write_text(text)
            return subprocess.run(["lake", "env", "lean", str(path)], cwd=root / "lean-cbcl",
                                  text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)
        baseline = compile_copy(source)
        if baseline.returncode:
            print(baseline.stdout)
            raise SystemExit("FAIL: baseline does not compile")
        print("PASS: baseline compiles", flush=True)
        for name, original, replacement, theorem in mutants:
            if source.count(original) != 1:
                raise SystemExit(f"FAIL: {name} anchor missing or ambiguous")
            broken = source.replace(original, replacement)
            result = compile_copy(broken)
            start = broken.index(f"theorem {theorem}")
            next_decl = re.search(r"\n(?:theorem|def|noncomputable def|end) ", broken[start:])
            end = start + next_decl.start() if next_decl else len(broken)
            first, last = broken[:start].count("\n") + 1, broken[:end].count("\n") + 1
            errors = [line for line in result.stdout.splitlines() if "error:" in line and
                      any(f"{module}.lean:{n}:" in line for n in range(first, last))]
            if not result.returncode or not errors:
                print(result.stdout)
                raise SystemExit(f"FAIL: {name} did not fail {theorem}")
            print(f"PASS: {name} rejected by {theorem}", flush=True)
