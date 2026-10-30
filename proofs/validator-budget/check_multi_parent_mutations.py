#!/usr/bin/env python3
"""SPEC-029: isolated executable guard mutations, leaving real Lean sources intact.

Run from any directory. Each mutant must trigger an actual kernel `decide`
counterexample in the executable audit, rather than a missing import/type error.
"""
import json
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / 'lean-cbcl'
SOURCE = (LEAN / 'LeanCbcl/ConsensusFree/MultiParent.lean').read_text()
AUDIT = (LEAN / 'MultiParentAudit.lean').read_text()

perform = SOURCE[SOURCE.index('def perform ('):SOURCE.index('\ntheorem perform_sound')]
perform = perform.replace('def perform (', 'def performMutant (')
execute = SOURCE[SOURCE.index('def execute ('):SOURCE.index('\ntheorem execute_sound')]
execute = re.sub(r'\bexecute\b', 'executeMutant', execute)
execute = re.sub(r'\bperform\b', 'performMutant', execute)
# The mutation harness exercises executable assertions only. The actual source's
# perform_sound/run/refinement theorems are checked independently, unchanged.
audit = AUDIT[:AUDIT.index('-- Run/refinement theorem')]
audit += '\nend CBCL.ConsensusFree.MultiParent.Audit\n'
audit = re.sub(r'\bexecute\b', 'executeMutant', audit)

static = SOURCE[SOURCE.index('def Static ('):SOURCE.index('\nstructure State')]
static = static[:static.index('\ninstance')]
books = static.index('    (∀ d, (allowance')
weak_static = static[:books] + '    True)\n'
weak_static = re.sub(r'\bStatic\b', 'WeakStatic', weak_static)
weak_static += 'instance : Decidable (WeakStatic c v) := inferInstanceAs (Decidable (_ ∨ _))\n'
live = SOURCE[SOURCE.index('def Live ('):SOURCE.index('\ndef signed (')]
weak_live = re.sub(r'\bLive\b', 'WeakLive', live)
weak_live = re.sub(r'\bStatic\b', 'WeakStatic', weak_live)

adopt = 'if AdoptAllowed c s v w'
mutations = {
    'control': ('', perform),
    'omit-historical-signatures': ('', perform.replace(adopt,
        'if s.known v = true ∧ (w ∈ c.committee.core → s.active w ∈ c.graph.parents v)')),
    'omit-exact-books': (weak_static + weak_live, perform.replace('if Live c s v', 'if WeakLive c s v')),
    'allow-sibling-adoption': ('', perform.replace(adopt,
        'if s.known v = true ∧ (w ∈ c.committee.core → Fits c s v w)')),
    'release-without-certificate': ('', perform.replace(
        'if cancelCert c s tx then some (released s tx w) else none', 'some (released s tx w)')),
    'omit-scaled-budget': ('', perform.replace('if SignAllowed c s tx w',
        'if w ∈ c.committee.core → c.authorized tx = true ∧ s.active w = c.opVersion tx ∧ s.released tx w = false')),
}

results = []
with tempfile.TemporaryDirectory(prefix='cbcl-multiparent-mutations-') as tmp:
    for name, (extra, body) in mutations.items():
        # Extra definitions and local executors reside in the audit namespace.
        insertion = 'set_option maxHeartbeats 0\n'
        text = audit.replace(insertion, insertion + '\n' + extra + body + execute + '\n', 1)
        file = Path(tmp) / f'{name}.lean'
        file.write_text(text)
        run = subprocess.run(['lake', 'env', 'lean', str(file)], cwd=LEAN,
                             capture_output=True, text=True, timeout=120)
        output = run.stdout + run.stderr
        false_tests = output.count('Tactic `decide` proved that the proposition')
        expected = run.returncode == 0 if name == 'control' else run.returncode != 0 and false_tests > 0
        results.append({'mutation': name, 'exit_code': run.returncode,
                        'false_executable_assertions': false_tests, 'expected_result': expected,
                        'output': output})
report = {'source': 'LeanCbcl/ConsensusFree/MultiParent.lean', 'results': results,
          'passed': all(r['expected_result'] for r in results)}
print(json.dumps(report, indent=2))
raise SystemExit(0 if report['passed'] else 1)
