#!/usr/bin/env python3
"""Targeted mutations of cbcl-state-proof; restores sources even when a test fails."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
CRATE = ROOT / 'crates/cbcl-state-proof/src'
DEFAULT_OUTPUT = ROOT / 'outputs/state-proof-mutations'
# (name, file, old, new, test module, test name)
MUTANTS = [
    ('unbound-after-state', 'circuit.rs',
     'layouter.constrain_instance(cell.cell(), config.public, i)?;',
     'if i != 8 { layouter.constrain_instance(cell.cell(), config.public, i)?; }',
     'tests', 'every_public_limb_is_constrained_without_the_host_precheck'),
    ('unconstrained-admission-transition', 'circuit.rs',
     'config.transition.enable(&mut region, i)?;',
     '// MUTATION: omit the transition recurrence constraint.',
     'tests', 'previous_context_relation_is_enforced_independently_of_snapshot_and_growth_checks'),
    ('unconstrained-transition-total', 'circuit.rs',
     'region.constrain_constant(last.cell(), Fp::ONE)',
     '{ let _ = last; Ok(()) } // MUTATION: final total unconstrained.',
     'tests', 'transition_total_must_equal_one_without_a_forged_sum'),
    ('chain-continuity-unchecked', 'chain.rs',
     'if statement.before != current {',
     'if false && statement.before != current { // MUTATION: no continuity check.',
     'chain_tests', 'gap_between_links_is_rejected'),
]

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=DEFAULT_OUTPUT,
                        help='Directory for generated reports and logs (default: gitignored outputs).')
    args = parser.parse_args()
    evidence = args.output_dir
    evidence.mkdir(parents=True, exist_ok=True)
    originals = {f: (CRATE / f).read_text() for _, f, *_ in MUTANTS}
    results = []
    try:
        for name, file, old, new, module, test in MUTANTS:
            original = originals[file]
            if original.count(old) != 1:
                raise RuntimeError(f'{name}: expected one mutation target')
            (CRATE / file).write_text(original.replace(old, new))
            try:
                command = ['cargo', 'test', '-p', 'cbcl-state-proof', '--lib', f'{module}::{test}', '--', '--test-threads=1']
                run = subprocess.run(command, cwd=ROOT, env={**os.environ, 'RAYON_NUM_THREADS':'2'}, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300)
            finally:
                (CRATE / file).write_text(original)
            (evidence / f'{name}.log').write_text(run.stdout.rstrip()+'\n')
            # Compilation failure is not a killed mutant: a named test must run
            # and fail on its assertion, with no successful test result.
            killed = run.returncode != 0 and f'test {module}::{test} ... FAILED' in run.stdout and 'panicked at' in run.stdout
            results.append({'mutant':name, 'file':file, 'test':f'{module}::{test}', 'exit_code':run.returncode, 'killed':killed, 'command':command})
            print(json.dumps(results[-1]), flush=True)
    finally:
        for f, text in originals.items():
            (CRATE / f).write_text(text)
    (evidence / 'mutations.json').write_text(json.dumps(results, indent=2)+'\n')
    return 0 if len(results)==len(MUTANTS) and all(r['killed'] for r in results) else 1

if __name__ == '__main__':
    sys.exit(main())
