#!/usr/bin/env python3
"""SPEC-035 TEST-3504: falsify covered HLC behavior in an isolated source copy.

Uses a private Cargo target directory for every mutation run. Never
modifies the caller's source or production build cache. Rust kills require an executed FAILED test, not a
compiler/import error. The Lean kill must invalidate the independent pick proof.
"""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def run(command, cwd):
    result = subprocess.run(command, cwd=cwd, text=True, capture_output=True)
    return result.returncode, result.stdout + result.stderr


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    results = []
    rust_cmd = ['cargo', 'test', '-p', 'cbcl-parser', '--test', 'hlc_registers', '--locked']
    code, output = run(rust_cmd, ROOT)
    if code:
        raise SystemExit('Baseline Rust tests must pass:\n' + output)
    with tempfile.TemporaryDirectory(prefix='cbcl-hlc-mutants-') as folder:
        isolated = Path(folder)
        os.environ['CARGO_TARGET_DIR'] = str(isolated / 'target')
        os.environ['CARGO_INCREMENTAL'] = '0'
        # Only files tracked in HEAD or explicitly changed/new in this worktree.
        tracked = subprocess.check_output(['git', 'ls-files', '-z'], cwd=ROOT).decode().split('\0')
        added = subprocess.check_output(['git', 'ls-files', '--others', '--exclude-standard', '-z'], cwd=ROOT).decode().split('\0')
        for name in set(tracked + added):
            if not name or not (ROOT / name).is_file():
                continue
            destination = isolated / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / name, destination)
        mutations = [
            ('initializer-arbitrates-ambiguity', 'crates/cbcl-core/src/state.rs',
             'match table {\n            [act] => self.field(act, key).unwrap_or(Value::Absent),\n            _ => Value::Absent,\n        }',
             'table.iter().max_by(|a, b| a.address.cmp(&b.address)).and_then(|a| self.field(a, key)).unwrap_or(Value::Absent)',
             ['cargo', 'test', '-p', 'cbcl-parser', '--test', 'register_simplification', '--locked']),
            ('reverse-clock-order', 'crates/cbcl-core/src/state.rs',
             '.max_by(|(x, _), (y, _)| x.cmp(y))', '.min_by(|(x, _), (y, _)| x.cmp(y))', rust_cmd),
            ('ignore-own-supersession', 'crates/cbcl-core/src/state.rs',
             'Rule::LwwPerSigner { verb, key, clock } => Value::Map(\n                self.group_by_signer(&self.current_by_signer(verb))',
             'Rule::LwwPerSigner { verb, key, clock } => Value::Map(\n                self.group_by_signer(&self.acts(verb))', rust_cmd),
            ('accept-malformed-clock', 'crates/cbcl-core/src/r7.rs',
             'if !valid {\n                    return Err(violation(\n                        "hlc",',
             'if false {\n                    return Err(violation(\n                        "hlc",', rust_cmd),
            ('logical-overflow-wrap', 'crates/cbcl-core/src/hlc.rs',
             'self.logical.checked_add(1)?', 'self.logical.wrapping_add(1)',
             ['cargo', 'test', '-p', 'cbcl-core', '--lib', 'hlc::tests', '--locked']),
        ]
        for name, relative, before, after, command in mutations:
            path = isolated / relative
            original = path.read_text()
            if original.count(before) != 1:
                raise SystemExit(f'{name}: mutation target must occur exactly once')
            path.write_text(original.replace(before, after))
            try:
                code, output = run(command, isolated)
                killed = code != 0 and 'test result: FAILED.' in output
                if not killed:
                    raise SystemExit(f'{name}: mutant survived or did not execute assertions:\n{output}')
                results.append({'mutation': name, 'killed': True,
                                'evidence': output[output.find('failures:'):][-6000:]})
            finally:
                path.write_text(original)
        source = ROOT / 'lean-cbcl/LeanCbcl/HlcRegister.lean'
        code, output = run(['lake', 'env', 'lean', str(source)], ROOT / 'lean-cbcl')
        if code:
            raise SystemExit('Baseline Lean module must pass:\n' + output)
        original = source.read_text()
        before = 'if LE a.key b.key then b else a'
        if original.count(before) != 1:
            raise SystemExit('Lean mutation target must occur exactly once')
        mutant = isolated / 'HlcRegisterMutant.lean'
        mutant.write_text(original.replace(before, 'if LE a.key b.key then a else b'))
        code, output = run(['lake', 'env', 'lean', str(mutant)], ROOT / 'lean-cbcl')
        if not code or ': error:' not in output or 'unknown module' in output or 'unknown identifier' in output.lower():
            raise SystemExit('Lean mutant survived or failed for infrastructure reasons:\n' + output)
        results.append({'mutation': 'reverse-model-arbitration', 'killed': True, 'evidence': output})
    report = {'baseline': 'passed', 'mutations': results}
    if args.output:
        args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'baseline': 'passed', 'mutations': [{'mutation': r['mutation'], 'killed': r['killed']} for r in results]}, indent=2))


if __name__ == '__main__':
    main()
