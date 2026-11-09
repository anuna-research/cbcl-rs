#!/usr/bin/env python3
"""SPEC-036 coverage inventory and isolated proof falsification.

Checks names, not Rust/Lean semantic equivalence. Every mutation must fail a
formerly passing Lean proof, without missing imports, identifiers or syntax errors.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean-cbcl'
MODULES = LEAN / 'LeanCbcl'


def run(path):
    result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=LEAN,
                            text=True, capture_output=True)
    return result.returncode, result.stdout + result.stderr


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    rust = (ROOT / 'crates/cbcl-core/src/state.rs').read_text()
    block = rust.split('pub fn head(&self)', 1)[1].split('///', 1)[0]
    runtime = set(re.findall(r'=> "([a-z-]+)"', block))
    source = (MODULES / 'StateKernelClause.lean').read_text()
    heads = set(re.findall(r'=> "([a-z-]+)"', source.split('def Rule.head', 1)[1].split('/--', 1)[0]))
    # SPEC-038 extensions have separate StateLift/StateContext proofs and Rust
    # correspondence tests; the legacy typed AST below still covers its 16 heads.
    extensions = {'lift', 'context'}
    if len(heads) != 16 or runtime != heads | extensions:
        raise SystemExit(f'Coverage mismatch: Rust={runtime}, Lean={heads}')
    parser_source = (ROOT / 'crates/cbcl-parser/src/state_parser.rs').read_text()
    for alias in ('multi-value-register', 'multi-value-map'):
        if alias not in parser_source or alias not in source:
            raise SystemExit(f'Missing alias coverage: {alias}')
    mutations = [
        ('initializer-arbitrates-ambiguity', 'StateKernelSemantics',
         'if rest.all (fun b => b == a) then some a else none',
         'if rest.all (fun b => b == a) then some a else some a'),
        ('drop-own-supersession', 'StateKernelSemantics',
         '| .own v => currentOwn v A', '| .own v => acts v A'),
        ('cardinality-always-zero', 'StateKernel',
         '| .count source => .integer (Int.ofNat (size (select (admitted domains input.acts) source)))',
         '| .count _ => .integer 0'),
        ('ignore-domains', 'StateKernelSemantics',
         'A.filter (fun a => ds.all', 'A.filter (fun a => ([] : List Domain).all'),
        ('numeric-payload-zero', 'StateKernelAggregates',
         '| .value (.int n) | .event _ (.int n) => n',
         '| .value (.int _) | .event _ (.int _) => 0'),
        ('histogram-counts-all-keys', 'StateKernelAggregates',
         '(m.keys.filter (fun key => cellScalar (m.read key) == some v)).length',
         'm.keys.length'),
        ('map-sum-zero', 'StateKernelAggregates',
         'm.keys.foldl (fun acc key => acc + cellNumber (m.read key)) 0', '0'),
        ('wrong-surface-dispatch', 'StateKernelClause',
         '| .count v => some (.count (.verb v))', '| .count v => some (.existsRule (.verb v))'),
        ('omit-clause-fields', 'StateKernelClause',
         'fields.map (fun (name, expression) => (name, evaluate input domains expression))', '[]'),
        ('progress-always-zero', 'StateKernel',
         '| .progress verb => .integer (Int.ofNat (protocolProgress input.causal input.thread verb (input.limit verb) input.acts))',
         '| .progress _ => .integer 0'),
        ('pending-exposes-ready', 'StateKernelExtensions',
         '| .pending missing => .pending missing', '| .pending _ => .ready 0 [] none'),
    ]
    results = []
    with tempfile.TemporaryDirectory(prefix='cbcl-state-kernel-mutants-') as temporary:
        for name, module, before, after in mutations:
            path = MODULES / (module + '.lean')
            original = path.read_text()
            code, output = run(path)
            if code:
                raise SystemExit(f'{module} baseline failed:\n{output}')
            if original.count(before) != 1:
                raise SystemExit(f'{name}: expected one target, got {original.count(before)}')
            mutant = Path(temporary) / (module + '.lean')
            mutant.write_text(original.replace(before, after))
            code, output = run(mutant)
            rejected = ('unknown module', 'unexpected token', 'file not found')
            proof_failure = any(x in output.lower() for x in ('unsolved goals', 'type mismatch', 'application type mismatch', 'tactic'))
            if not code or not proof_failure or any(x in output.lower() for x in rejected):
                raise SystemExit(f'{name}: survived or infrastructure failure:\n{output}')
            results.append({'mutation': name, 'killed': True, 'evidence': output})
    report = {'runtime_heads': sorted(runtime), 'coverage': '16 legacy heads and 2 aliases; names only',
              'separately_verified_extensions': sorted(extensions),
              'baseline': 'passed', 'mutations': results}
    if args.output:
        args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({**report, 'mutations': [{'mutation': x['mutation'], 'killed': x['killed']}
                                             for x in results]}, indent=2))


if __name__ == '__main__':
    main()
