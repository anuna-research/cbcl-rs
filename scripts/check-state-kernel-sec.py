#!/usr/bin/env python3
"""SPEC-037 falsification of accepted-set interpretation and execution semantics.

Compile baseline first, then change only executable definitions/transition effects
in isolated files. A kill needs proof/type failure; import/parser failures do not count.
"""
import argparse
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean-cbcl'


def run(path):
    result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=LEAN,
                            text=True, capture_output=True)
    return result.returncode, result.stdout + result.stderr


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    results = []
    mutations = [
        ('drop-first-accepted-act', 'StateKernelSEC',
         '⟨A, c.opener, c.clock, c.rank,', '⟨A.drop 1, c.opener, c.clock, c.rank,'),
        ('merge-discards-current-history', 'StateKernelSEC',
         'incoming.foldr insertAct current', 'incoming.foldr insertAct []'),
        ('accept-forgets-previous-acts', 'StateRefinement',
         'accepted := insertAct a s.accepted', 'accepted := [a]'),
        ('accept-label-does-not-insert', 'StateRefinement',
         'accepted := insertAct a s.accepted', 'accepted := s.accepted'),
    ]
    with tempfile.TemporaryDirectory(prefix='cbcl-sec-mutants-') as temporary:
        for name, module, before, after in mutations:
            original_path = LEAN / 'LeanCbcl' / (module + '.lean')
            original = original_path.read_text()
            code, output = run(original_path)
            if code:
                raise SystemExit(f'Baseline {module} failed:\n{output}')
            if original.count(before) != 1:
                raise SystemExit(f'{name}: target count {original.count(before)}')
            mutant = Path(temporary) / (module + '.lean')
            mutant.write_text(original.replace(before, after))
            code, output = run(mutant)
            semantic_failure = any(x in output.lower() for x in
                                   ('unsolved goals', 'type mismatch', 'tactic'))
            if not code or not semantic_failure or any(x in output.lower() for x in
                    ('unknown module', 'unexpected token', 'file not found')):
                raise SystemExit(f'{name}: survived or invalid infrastructure failure:\n{output}')
            results.append({'mutation': name, 'killed': True, 'evidence': output})
    report = {'baseline': 'passed', 'mutations': results,
              'scope': 'proof falsification; typed model, not Rust runtime mutation'}
    if args.output:
        args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'baseline': 'passed', 'mutations':
                      [{'mutation': x['mutation'], 'killed': x['killed']} for x in results]}, indent=2))


if __name__ == '__main__':
    main()
