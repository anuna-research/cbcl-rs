#!/usr/bin/env python3
"""SPEC-038 TEST-3800/3801/3803/3804: mutate isolated Rust copies only."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[1]
    domain_test = ("lattice_factorisation", "domain_lift_obeys_union_law_across_distinct_openers")
    sum_test = ("threshold_reads", "negative_credits_are_rejected_and_signed_balances_remain_snapshots")
    closure_test = ("threshold_reads", "initializer_conflict_faults_progress_and_its_reached_threshold")
    freeze_test = ("freeze_reads", "freeze_keeps_its_causal_past_and_records_late_and_concurrent_writes")
    freeze_fault_test = ("freeze_reads", "fault_policy_names_the_freezer_and_late_writer")
    freeze_pair_test = ("freeze_reads", "repeated_causal_freezes_keep_the_first_cut_but_concurrent_freezes_fault")
    freeze_initial_test = ("freeze_reads", "freeze_cannot_hide_a_later_initializer_conflict")
    mutations = [
        ("initializer-domain-support-omitted", "state.rs",
         'support.insert(act.address.clone());', 'let _ = &act.address;',
         ("freeze_reads", "admitted_domain_initializer_outside_freeze_cut_preserves_threshold_or_fault")),
        ("roster-domain-support-omitted", "state.rs",
         'support.insert(root.address.clone());', 'let _ = &root.address;',
         ("state_context", "domain_roster_root_outside_cut_is_retained_as_freeze_support")),
        ("quoted-pin-wire-path-rejected", "role.rs",
         'SExpr::Atom(Atom::Str(pin) | Atom::Symbol(pin)) => pin,',
         'SExpr::Atom(Atom::Symbol(pin)) => pin,',
         ("state_context", "quoted_dialect_pins_cross_the_strict_wire_boundary")),
        ("frozen-threshold-uses-full-history", "freeze.rs",
         'let ctx = crate::lattice::Ctx::new(clause, &reader.scopes[scope]);',
         'let ctx = crate::lattice::Ctx::new(clause, &reader.scopes[0]);',
         ("freeze_reads", "frozen_threshold_raw_state_keeps_domain_initialization_inside_its_cut")),
        ("unsupported-profile-gains-context", "escrow.rs",
         'if c.ownership == Ownership::Collective || c.certification.is_quorum() {',
         'if false {',
         ("bounded_counter", "unsupported_resource_profiles_keep_projection_fault_evidence")),
        ("initializer-fault-erases-finite-writers", "lattice.rs",
         'if initializer_fault && matches!(contribution, Contribute::Finite { .. }) {',
         'if false {',
         ("finite_lattices", "initializer_fork_preserves_an_existing_finite_fault_witness")),
        ("missing-dependency-hides-resource-fault", "escrow.rs",
         '    // Validate every dependency-closed component before reporting missing',
         '    if !missing.is_empty() { return Outcome::Pending(missing.into_iter().collect()); }\n    // Validate every dependency-closed component before reporting missing',
         ("bounded_counter", "missing_dependency_cannot_hide_an_independent_resource_fault")),
        ("context-pin-not-checked", "context.rs",
         '.is_some_and(|pin| *pin != self.address)', '.is_some_and(|_| false)',
         ("state_context", "cast_validation_and_pins_are_not_bypassed_by_context_reads")),
        ("context-fixed-data-marked-snapshot", "state.rs",
         'if crate::context::stable_path(path)', 'if false',
         ("state_context", "context_schema_marks_fixed_projections_and_current_observations")),
        ("context-observation-freeze-drops-acts", "freeze.rs",
         'return acts.iter().map(|a| a.address.clone()).collect();', 'return HashSet::new();',
         ("state_context", "context_observation_freezes_include_domain_excluded_accepted_acts")),
        ("resource-fault-context-discarded", "escrow.rs",
         'evidence.extend(all.keys().cloned());', 'let _ = all.keys();',
         ("bounded_counter", "resource_fault_evidence_keeps_prior_witnesses_when_another_fork_arrives")),
        ("finite-only-first-contribution", "lattice.rs",
         '.fold(table.bottom, |a, b| table.merge(a, b))', '.next().unwrap_or(table.bottom)',
         ("finite_lattices", "every_matching_contribution_row_is_joined")),
        ("domain-freeze-evidence-forgotten", "state.rs",
         'for act in acts.iter().filter(|a| a.verb == *opener) {',
         'for act in acts.iter().filter(|_| false) {',
         ("freeze_reads", "domain_fault_cannot_erase_the_freeze_witness_of_an_admitted_contributor")),
        ("concurrent-freeze-loses-writer", "freeze.rs",
         'evidence.extend(candidates.iter().filter(|a| !cut.contains(*a)).cloned());',
         'let _ = candidates.iter().filter(|a| !cut.contains(*a));',
         ("freeze_reads", "additional_concurrent_freezer_preserves_the_late_writer_witness")),
        ("normal-fault-replaces-freeze-evidence", "freeze.rs",
         'evidence.extend(fault.fault_evidence().unwrap_or_default());',
         'let _ = fault;',
         ("freeze_reads", "initializer_conflict_preserves_an_existing_freeze_fault_witness")),
        ("snapshot-marking-removed", "state.rs",
         'if matches!(ty, StateType::Threshold { .. }) {', 'if true {',
         ("finite_lattices", "schema_marks_projections_as_snapshots_and_keeps_mixed_types_honest")),
        ("finite-commutativity-unchecked", "finite.rs",
         'if t.merge(a, b) != t.merge(b, a) {', 'if false {',
         ("finite_lattices", "invalid_join_tables_are_rejected_with_law_and_witness")),
        ("finite-associativity-unchecked", "finite.rs",
         'if t.merge(t.merge(a, b), c) != t.merge(a, t.merge(b, c)) {', 'if false {',
         ("finite_lattices", "associativity_idempotence_and_boundary_laws_are_checked_independently")),
        ("finite-top-hidden", "lattice.rs", 'if *index == table.top {', 'if false {',
         ("finite_lattices", "top_is_an_attributable_terminal_fault")),
        ("finite-stability-unchecked", "finite.rs", 'if !ordered {', 'if false {',
         ("finite_lattices", "projection_stability_is_verified_and_snapshot_projection_stays_available")),
        ("domain-evidence-discarded", "lattice.rs", "if self.domain_governed(term) || matches!(term, Term::History(_)) {",
         "if matches!(term, Term::History(_)) {", domain_test),
        ("negative-credit-admitted", "shape.rs",
         "return matches!(sexpr, SExpr::Atom(Atom::Num(n)) if *n >= 0);",
         "return matches!(sexpr, SExpr::Atom(Atom::Num(_)));", sum_test),
        ("signed-events-threshold-admitted", "r7.rs", "if !monotone {", "if false {", sum_test),
        ("threshold-fault-suppressed", "state.rs", "n == field && v.fault_evidence().is_some()",
         "false && n == field && v.fault_evidence().is_some()", domain_test),
        ("derived-fault-suppressed", "lattice.rs",
         "earlier.filter(|v| v.fault_evidence().is_some())", "earlier.filter(|_| false)", domain_test),
        ("closure-fault-suppressed", "lattice.rs",
         '.filter(|(verb, _)| verbs.contains(verb))',
         '.filter(|_| false)', closure_test),
        ("freeze-cut-ignored", "freeze.rs", '.filter(|a| cut.contains(&a.address))',
         '.filter(|_| true)', freeze_test),
        ("freeze-fault-policy-ignored", "freeze.rs",
         'if p.policy == FreezePolicy::Fault && !p.late.is_empty() {',
         'if false {', freeze_fault_test),
        ("concurrent-freezers-hidden", "freeze.rs", 'if frontier.len() > 1 {',
         'if false {', freeze_pair_test),
        ("freeze-hides-initializer-fault", "freeze.rs",
         '(Some(_), None) => normal,',
         '(Some(_), None) => Value::Absent,', freeze_initial_test),
    ]
    with tempfile.TemporaryDirectory(prefix="cbcl-lvar-semantics-") as directory:
        isolated = Path(directory)
        (isolated / "crates").mkdir()
        for name in ["cbcl-core", "cbcl-parser"]:
            shutil.copytree(root / "crates" / name, isolated / "crates" / name)
        for name in ["dialects", "test-vectors"]:
            shutil.copytree(root / name, isolated / name)
        for name in ["Cargo.lock", "rust-toolchain.toml"]:
            if (root / name).exists():
                shutil.copy2(root / name, isolated / name)
        manifest, count = re.subn(
            r"members = \[.*?\]", 'members = ["crates/cbcl-core", "crates/cbcl-parser"]',
            (root / "Cargo.toml").read_text(), count=1, flags=re.S,
        )
        if count != 1:
            raise SystemExit("FAIL: workspace members anchor missing")
        (isolated / "Cargo.toml").write_text(manifest)
        env = dict(os.environ, CARGO_TARGET_DIR=str(isolated / "target"),
                   CARGO_PROFILE_TEST_DEBUG="0", CARGO_PROFILE_DEV_DEBUG="0", CARGO_INCREMENTAL="0")

        def run(test):
            return subprocess.run(
                ["cargo", "test", "--offline", "-p", "cbcl-parser", "--test", test[0],
                 test[1], "--", "--exact"], cwd=isolated, env=env,
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300,
            )

        for test in sorted({m[-1] for m in mutations}):
            baseline = run(test)
            if baseline.returncode != 0 or f"test {test[1]} ... ok" not in baseline.stdout:
                print(baseline.stdout)
                raise SystemExit(f"FAIL: baseline {test[1]}")
            print(f"PASS: baseline {test[1]}", flush=True)
        for name, filename, original, replacement, test in mutations:
            path = isolated / "crates/cbcl-core/src" / filename
            source = path.read_text()
            if source.count(original) != 1:
                raise SystemExit(f"FAIL: {name} anchor missing or ambiguous")
            try:
                path.write_text(source.replace(original, replacement))
                result = run(test)
            finally:
                path.write_text(source)
            if result.returncode == 0 or f"test {test[1]} ... FAILED" not in result.stdout:
                print(result.stdout)
                raise SystemExit(f"FAIL: {name} did not fail its executed semantic test")
            print(f"PASS: {name} rejected by {test[1]}", flush=True)


if __name__ == "__main__":
    main()
