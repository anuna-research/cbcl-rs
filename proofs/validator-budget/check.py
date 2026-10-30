#!/usr/bin/env python3
"""Reproduce SPEC-021 behavioral and proof mutation evidence.

Run from any directory. Output is JSON; logs go to --output if supplied.
The Lean mutation operates only on an isolated temporary copy.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path)
    parser.add_argument('--lean-mutation', action='store_true')
    args = parser.parse_args()
    if args.output:
        args.output.mkdir(parents=True, exist_ok=True)
    report = {'scope': 'reference tests, mutations and a known safety refutation',
              'async_safety': 'refuted by SPEC-021 BUG-2100'}
    clean = dict(os.environ)
    clean.pop('CBCL_BUDGET_MODEL_MUTATION', None)
    p = subprocess.run([sys.executable, str(HERE/'test_model.py')], env=clean,
                       capture_output=True, text=True)
    if args.output:
        (args.output/'lifecycle.log').write_text(p.stderr.rstrip()+'\n')
        (args.output/'lifecycle.json').write_text(p.stdout)
    assert p.returncode == 0, p.stderr
    report['lifecycle'] = json.loads(p.stdout)
    targets = {
        'forget-omitted': 'test_version_omitted_signatures_remain_charged',
        'charge-replay': 'test_signing_replay_and_restart',
        'early-finality': 'test_finality_is_not_certification_or_local_execution',
        'ignore-fence': 'test_no_commit_recovery_and_late_certificate',
    }
    killed = {}
    for mutation, test in targets.items():
        env = dict(clean, CBCL_BUDGET_MODEL_MUTATION=mutation)
        p = subprocess.run([sys.executable, '-m', 'unittest', '-v', 'test_model.ModelTests.'+test],
                           cwd=HERE, env=env, capture_output=True, text=True)
        assert p.returncode != 0 and 'AssertionError' in p.stderr, (mutation, p.stderr)
        assert 'Ran 1 test' in p.stderr, p.stderr
        killed[mutation] = {'test': test, 'exit_code': p.returncode, 'behavioral_assertion_failed': True}
        if args.output:
            (args.output/(mutation+'.log')).write_text(p.stderr.rstrip()+'\n')
    report['behavioral_mutations_killed'] = killed
    if args.lean_mutation:
        source = (ROOT/'lean-cbcl/LeanCbcl/ValidatorBudget.lean').read_text()
        needle = '≤ (f + 1) * initial)'
        assert source.count(needle) == 1
        with tempfile.TemporaryDirectory(prefix='cbcl-budget-proof-') as temp:
            path = Path(temp)/'UnsafeBudget.lean'
            path.write_text(source.replace(needle, '≤ (2 * f + 1) * initial)'))
            p = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT/'lean-cbcl',
                               capture_output=True, text=True)
        assert p.returncode != 0 and 'error:' in p.stdout, p.stdout+p.stderr
        assert 'witness_capacity' in p.stdout, p.stdout
        report['lean_mutation'] = {'change': 'allow each honest witness the full resource budget',
                                   'exit_code': p.returncode, 'proof_rejected': True}
        if args.output:
            # Temp directory names are not meaningful evidence identity.
            log = p.stdout.replace(str(path), 'UnsafeBudget.lean') + p.stderr
            (args.output/'lean-bound-mutation.log').write_text(log.rstrip()+'\n')
    p = subprocess.run([sys.executable, str(HERE/'async_counterexample.py')],
                       env=clean, capture_output=True, text=True)
    assert p.returncode == 0, p.stderr
    refutation = json.loads(p.stdout)
    assert refutation['result'] == 'asynchronous safety refuted'
    report['known_refutation'] = {'reproduced': True, 'initial_rights': 30,
                                 'finalized_payments': 33, 'final_rights': -3}
    if args.output:
        (args.output/'known-async-refutation.json').write_text(p.stdout)
    rendered = json.dumps(report, indent=2, sort_keys=True)+'\n'
    if args.output:
        (args.output/'checks.json').write_text(rendered)
    print(rendered, end='')


if __name__ == '__main__':
    main()
