#!/usr/bin/env python3
"""Targeted circuit mutations; restores sources even when a test fails."""
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / 'crates/cbcl-state-proof/src/circuit.rs'
EVIDENCE = ROOT / 'experiments/state-proof/evidence'
MUTANTS = [
    ('unbound-after-state',
     'layouter.constrain_instance(cell.cell(), config.public, i)?;',
     'if i != 8 { layouter.constrain_instance(cell.cell(), config.public, i)?; }',
     'every_public_limb_is_constrained_without_the_host_precheck'),
    ('unconstrained-admission-transition',
     'config.transition.enable(&mut region, i)?;',
     '// MUTATION: omit the transition recurrence constraint.',
     'previous_context_relation_is_enforced_independently_of_snapshot_and_growth_checks'),
]

def main():
    EVIDENCE.mkdir(exist_ok=True)
    original = SOURCE.read_text()
    results = []
    try:
        for name, old, new, test in MUTANTS:
            if original.count(old) != 1:
                raise RuntimeError(f'{name}: expected one mutation target')
            SOURCE.write_text(original.replace(old, new))
            command = ['cargo', 'test', '-p', 'cbcl-state-proof', '--lib', test, '--', '--test-threads=1']
            run = subprocess.run(command, cwd=ROOT, env={**os.environ, 'RAYON_NUM_THREADS':'2'}, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=120)
            (EVIDENCE / f'{name}.log').write_text(run.stdout.rstrip()+'\n')
            # Compilation failure is not a killed mutant: a named test must run
            # and fail on its assertion, with no successful test result.
            killed = run.returncode != 0 and f'test tests::{test} ... FAILED' in run.stdout and 'panicked at' in run.stdout
            results.append({'mutant':name, 'test':test, 'exit_code':run.returncode, 'killed':killed, 'command':command})
            print(json.dumps(results[-1]), flush=True)
    finally:
        SOURCE.write_text(original)
    (EVIDENCE / 'mutations.json').write_text(json.dumps(results, indent=2)+'\n')
    return 0 if len(results)==len(MUTANTS) and all(r['killed'] for r in results) else 1

if __name__ == '__main__':
    sys.exit(main())
