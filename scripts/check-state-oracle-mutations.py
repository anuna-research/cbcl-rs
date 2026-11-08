#!/usr/bin/env python3
"""SPEC-038: test live Lean comparisons and native admission guards, in copies."""
from pathlib import Path
import argparse
import os
import re
import shutil
import subprocess
import tempfile

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--mutant", action="append", help="Run only this mutant (repeatable)")
options = parser.parse_args()

root = Path(__file__).resolve().parents[1]
oracle = root / "lean-cbcl/.lake/build/bin/cbcl-state-oracle"
if not oracle.is_file():
    raise SystemExit("Build first: cd lean-cbcl && lake build cbcl-state-oracle")
resource_context_test = "resource::cited_context_evidence_matches_lean"
resource_graph_test = "resource::funding_graph_matches_lean"
resource_test = "resource::decrement_verifier_matches_lean"
finite_test = "finite_kernel_matches_live_lean_oracle"
freeze_test = "freeze_kernel_matches_live_lean_oracle"
nested_test = "nested_kernel_matches_live_lean_oracle"
context_test = "context::context_kernel_matches_live_lean_oracle"
admission_test = "duplicate_amount_cannot_hide_a_negative_state_contribution"
keyword_test = "shape::keyword_extraction_matches_lean"
transport_test = "oracle_transport_failure_rejects_late_replies"
fault_test = "render::fault_evidence_bytes_match_lean"
render_test = "render::native_json_bytes_match_lean"
frozen_render_test = "render::frozen_wrapper_bytes_match_lean"
with tempfile.TemporaryDirectory(prefix="cbcl-live-oracle-") as directory:
    isolated = Path(directory)
    (isolated / "crates").mkdir()
    for name in ["cbcl-core", "cbcl-parser"]:
        shutil.copytree(root / "crates" / name, isolated / "crates" / name)
    shutil.copytree(root / "dialects", isolated / "dialects")
    for name in ["Cargo.lock", "rust-toolchain.toml"]:
        shutil.copy2(root / name, isolated / name)
    manifest, count = re.subn(r"members = \[.*?\]", 'members = ["crates/cbcl-core", "crates/cbcl-parser"]',
                             (root / "Cargo.toml").read_text(), count=1, flags=re.S)
    if count != 1:
        raise SystemExit("workspace membership anchor missing")
    (isolated / "Cargo.toml").write_text(manifest)
    env = dict(os.environ, CBCL_STATE_ORACLE=str(oracle), PROPTEST_CASES="32", PROPTEST_RNG_SEED="380038",
               CARGO_TARGET_DIR=str(isolated / "target"), CARGO_INCREMENTAL="0", CARGO_PROFILE_TEST_DEBUG="0")

    def run(test):
        binary = "threshold_reads" if test == admission_test else "state_kernel_oracle"
        flags = ["--exact"] if test in [admission_test, transport_test] else ["--ignored", "--exact"]
        return subprocess.run(["cargo", "test", "--offline", "-p", "cbcl-parser", "--test", binary,
                               test, "--", *flags], cwd=isolated, env=env,
                              text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300)

    mutants = [
        ("resource-cited-context-hidden", "escrow.rs", "evidence.extend(fact.predecessors.iter().filter(|id| present(id)).cloned());", "", resource_context_test),
        ("resource-absent-context-reported", "escrow.rs", "evidence.extend(fact.predecessors.iter().filter(|id| present(id)).cloned());", "evidence.extend(fact.predecessors.iter().cloned());", resource_context_test),
        ("resource-evidence-json-spacing", "state.rs", "Value::List(items) => {\n                out.push('[');", "Value::List(items) => {\n                out.push_str(\"[ \");", resource_graph_test),
        ("resource-evidence-json-order-reversed", "escrow.rs", "Value::List(evidence.iter().map(|s| text(s)).collect())", "Value::List(evidence.iter().rev().map(|s| text(s)).collect())", resource_graph_test),
        ("resource-contextual-facts-hidden", "escrow.rs", "evidence.extend(all.keys().cloned());", "", resource_graph_test),
        ("resource-witness-dedup-skipped", "escrow.rs", "evidence.dedup();", "", resource_graph_test),
        ("resource-owner-fork-hidden", "escrow.rs", "if let Some(other) = children.insert((a.signer.clone(), prev.into()), a.address.clone()) {", "if let Some(other) = None::<String> {", resource_graph_test),
        ("resource-dependency-credit-hidden", "escrow.rs", "for dep in &n.deps {", "for dep in core::iter::empty::<&String>() {", resource_graph_test),
        ("resource-zero-decrement-accepted", "escrow.rs", "number(amount).filter(|n| *n > 0)", "number(amount).filter(|n| *n >= 0)", resource_test),
        ("resource-exact-budget-rejected", "escrow.rs", "budget.is_some_and(|b| b < n.amount)", "budget.is_some_and(|b| b <= n.amount)", resource_test),
        ("resource-decrement-credits-rights", "escrow.rs", "Kind::Decrement => {\n            add(rights, owner, -amount)?;", "Kind::Decrement => {\n            add(rights, owner, amount)?;", resource_test),
        ("frozen-wrapper-root-altered", "freeze.rs", '(Value::Str("frozen".into()), Value::Str(root))', '(Value::Str("frozen".into()), Value::Str(root + "x"))', frozen_render_test),
        ("frozen-wrapper-exclusion-order-reversed", "freeze.rs", "state::sort_addresses(&mut excluded);", "state::sort_addresses(&mut excluded); excluded.reverse();", frozen_render_test),
        ("frozen-wrapper-payload-discarded", "freeze.rs", '(Value::Str("value".into()), value)', '(Value::Str("value".into()), Value::Int(0))', frozen_render_test),
        ("radix-outer-digit-order-forward", "state.rs", "for digit in (0..width).rev() {", "for digit in 0..width {", fault_test),
        ("radix-outer-leading-digit-skipped", "state.rs", "for digit in (0..width).rev() {", "for digit in (1..width).rev() {", fault_test),
        ("radix-prefix-control-order-reversed", "state.rs", "for k in 1..257 {", "for k in (1..257).rev() {", fault_test),
        ("radix-prefix-control-count-index-shifted", "state.rs", "next[k - 1] + counts[k - 1]", "next[k - 1] + counts[k]", fault_test),
        ("fault-source-pool-order-reversed", "state.rs", "addresses.extend(order.into_iter().map(|i| values[i].take().unwrap()));", "addresses.extend(order.into_iter().rev().map(|i| values[i].take().unwrap()));", fault_test),
        ("fault-source-pool-address-altered", "state.rs", "values[i].take().unwrap()", 'values[i].take().unwrap() + "x"', fault_test),
        ("oracle-transport-failure-not-poisoned", "state_kernel_oracle.rs", "self.healthy = false;", "self.healthy = true;", transport_test),
        ("oracle-poison-guard-bypassed", "state_kernel_oracle.rs", "assert!(self.healthy,", "assert!(true,", transport_test),
        ("radix-scatter-equal-bucket-order-reversed", "state.rs", "for &i in &order {\n            let k = key(i);", "for &i in order.iter().rev() {\n            let k = key(i);", fault_test),
        ("fault-zero-byte-sentinel-lost", "state.rs", ".map(|b| *b as usize + 1)", ".map(|b| *b as usize)", fault_test),
        ("fault-evidence-duplicates-retained", "state.rs", "evidence.dedup();", "// evidence duplicates retained", fault_test),
        ("json-control-hex-uppercase", "state.rs", "{:04x}", "{:04X}", render_test),
        ("json-state-clause-order-reversed", "state.rs", "for (i, (name, value)) in state.iter().enumerate() {", "for (i, (name, value)) in state.iter().rev().enumerate() {", render_test),
        ("keyword-extraction-value-changed", "state.rs", "out.insert(k.clone(), params[i + 1].clone());", "out.insert(k.clone(), match &params[i + 1] { crate::sexpr::SExpr::Atom(crate::sexpr::Atom::Num(n)) => crate::sexpr::SExpr::Atom(crate::sexpr::Atom::Num(*n + 1)), value => value.clone() });", keyword_test),
        ("keyword-extraction-duplicate-gate-bypassed", "r7.rs", "&& !seen_fields.insert(k)", "&& (!seen_fields.insert(k) && false)", keyword_test),
        ("duplicate-state-keyword-accepted", "r7.rs", "&& !seen_fields.insert(k)", "&& (!seen_fields.insert(k) && false)", admission_test),
        ("context-sealed-cast-traversal-stops-at-wrapper", "context.rs", "crate::message::Message::Wrapped { content, .. } => message = content,", 'crate::message::Message::Wrapped { .. } => return Err("lost enclosed cast".into()),', context_test),
        ("context-pin-grammar-bypassed", "role.rs", "if hex.len() != PIN_HEX_LEN || !hex.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f')) {", "if false {", context_test),
        ("context-quoted-account-accepted", "role.rs", "let SExpr::Atom(Atom::Symbol(k)) = key else {", "let SExpr::Atom(Atom::Symbol(k) | Atom::Str(k)) = key else {", context_test),
        ("state-bound-default-gate-bypassed", "r7.rs", "|| b.max_list > defaults.max_list", "|| false", finite_test),
        ("finite-read-cache-wrong-right-index", "r7.rs", "match (reads[i], reads[j])", "match (reads[i], reads[0])", finite_test),
        ("finite-symbol-string-confused", "lattice.rs", "act.fields.get(&row.key) == Some(&row.value)", "act.fields.get(&row.key).map(|value| match value { SExpr::Atom(Atom::Symbol(name)) => SExpr::Atom(Atom::Str(name.clone())), other => other.clone() }).as_ref() == Some(&row.value)", finite_test),
        ("reader-scope-cache-key-erased", "freeze.rs", "let key = (scope, name.to_string());", "let key = (0, name.to_string());", nested_test),
        ("reader-field-cache-key-erased", "freeze.rs", "let key = (scope, name.to_string());", "let key = (scope, String::new());", nested_test),
        ("reader-dependency-uses-whole-history", "freeze.rs", "let v = self.field(scope, &source);", "let v = self.field(0, &source);", nested_test),
        ("reader-frozen-dependency-not-unwrapped", "freeze.rs", "done.push((source, v.unfrozen().clone()));", "done.push((source, v.clone()));", nested_test),
        ("derived-source-fault-hidden", "lattice.rs", "earlier.filter(|v| v.fault_evidence().is_some())", "earlier.filter(|_| false)", nested_test),
        ("only-first-finite-contribution", "lattice.rs", ".fold(table.bottom, |a, b| table.merge(a, b))", ".next().unwrap_or(table.bottom)", finite_test),
        ("threshold-source-fault-hidden", "state.rs", "n == field && v.fault_evidence().is_some()", "false && n == field && v.fault_evidence().is_some()", finite_test),
        ("freeze-cut-ignored", "freeze.rs", ".filter(|a| cut.contains(&a.address))", ".filter(|_| true)", freeze_test),
        ("freeze-fault-policy-hidden", "freeze.rs", "if p.policy == FreezePolicy::Fault && !p.late.is_empty() {", "if false {", freeze_test),
        ("concurrent-freezers-hidden", "freeze.rs", "if frontier.len() > 1 {", "if false {", freeze_test),
        ("raw-fault-hides-freeze-evidence", "freeze.rs", "evidence.extend(fault.fault_evidence().unwrap_or_default());", "let _ = fault;", freeze_test),
        ("context-duplicate-roster-accepted", "role.rs", "if !key_set.insert(AgentKey(k.clone())) {", "if !key_set.insert(AgentKey(k.clone())) && false {", context_test),
        ("context-dialect-marked-snapshot", "context.rs", 'Some("dialect") => true,', 'Some("dialect") => false,', context_test),
        ("context-pin-check-hidden", "context.rs", ".is_some_and(|pin| *pin != self.address)", ".is_some_and(|_| false)", context_test),
        ("context-mixed-witness-hidden", "context.rs", "evidence.extend(acts.iter().map(|a| a.address.clone()));", "let _ = acts;", context_test),
        ("context-opener-witness-hidden", "context.rs", "evidence.extend(openers.into_iter().map(String::from));", "let _ = openers;", context_test),
        ("context-count-includes-delivery-duplicates", "context.rs", "acts.iter()\n                            .map(|a| &a.address)\n                            .collect::<BTreeSet<_>>()\n                            .len()", "acts.len()", context_test),
        ("context-frontier-hidden", "context.rs", "crate::state::frontier(acts)", "Vec::<String>::new()", context_test),
    ]
    if options.mutant:
        unknown = set(options.mutant) - {item[0] for item in mutants}
        if unknown:
            parser.error("unknown mutants: " + ", ".join(sorted(unknown)))
        mutants = [item for item in mutants if item[0] in options.mutant]
    for test in dict.fromkeys(item[4] for item in mutants):
        baseline = run(test)
        if baseline.returncode or f"test {test} ... ok" not in baseline.stdout:
            print(baseline.stdout)
            raise SystemExit(f"FAIL: regression baseline {test}")
        kind = "native-admission" if test == admission_test else "transport-regression" if test == transport_test else "live-oracle"
        print(f"PASS: {kind} baseline {test}", flush=True)
    for name, filename, before, after, test in mutants:
        path = (isolated / "crates/cbcl-parser/tests" / filename) if filename == "state_kernel_oracle.rs" else (isolated / "crates/cbcl-core/src" / filename)
        source = path.read_text()
        if source.count(before) != 1:
            raise SystemExit(f"FAIL: {name} anchor missing or ambiguous")
        try:
            path.write_text(source.replace(before, after))
            result = run(test)
        finally:
            path.write_text(source)
        # Rust assert! with a custom message omits the word "assertion".
        # Recognize only the named guard, after requiring this test to execute.
        assertion = ("assertion" in result.stdout
                     or (test == admission_test and "ambiguous amount admitted:" in result.stdout)
                     or (test == fault_test and "native fault fold panicked; case=" in result.stdout)
                     or (test in [resource_test,resource_graph_test] and "duplicate native resource witness" in result.stdout)
                     or (test == resource_context_test and "resource evidence names an absent act" in result.stdout))
        if result.returncode == 0 or f"test {test} ... FAILED" not in result.stdout or not assertion:
            print(result.stdout)
            raise SystemExit(f"FAIL: {name} not rejected by executed regression assertion")
        evidence = "native admission regression" if test == admission_test else "transport regression" if test == transport_test else "live Lean comparison"
        print(f"PASS: {name} rejected by {evidence}", flush=True)
