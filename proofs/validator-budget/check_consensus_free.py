"""SPEC-025 consensus-free executable/proof audit with isolated module mutations.

No second protocol model: audits execute the canonical Lean transition function.
Mutants are recompiled through their dependent proofs in private module trees.
"""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import json
import os
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / 'lean-cbcl'
MODULES = ['Core', 'Journals', 'Archive', 'Evidence', 'Capacity', 'Observation',
           'Coverage', 'Execution', 'Currency', 'Tests']
MUTANTS = {
    'ignore-local-budget': ('Core',
        '(∀ d, charge c (signed s tx w) (c.opEpoch tx) w d ≤ (f+1) * allowance c (c.opEpoch tx) d)',
        'True'),
    'sign-after-seal': ('Core', 's.sealed (c.opEpoch tx) w = false ∧ s.released tx w = false',
                        'True ∧ s.released tx w = false'),
    'release-without-cancellation': ('Core', '(certificate : cancelCert c s tx = true) : Step c s none (release s tx w)',
                                    '(certificate : True) : Step c s none (release s tx w)'),
    'overwrite-checkpoint-choice': ('Core',
        '(s.choices (c.checkpoints p).parent w = none ∨ s.choices (c.checkpoints p).parent w = some p)',
        'True'),
    'forget-parent-obligations': ('Core', '(∀ tx, held c m.parent tx = true → m.held tx = true)', 'True'),
    'speculative-funding-credit': ('Core',
        '(∀ tx, (c.checkpoints p).credited tx = true → finalCert c s tx = true)',
        '(∀ tx, (c.checkpoints p).credited tx = true → True)'),
    'double-manifest-refund': ('Core',
        'isum (List.finRange T) (fun tx => if m.refunded tx then (c.cost tx d : Int) else 0))',
        '2 * isum (List.finRange T) (fun tx => if m.refunded tx then (c.cost tx d : Int) else 0))'),
    'record-without-certificate': ('Execution',
        'Member c w ∧ checkpointCert c s p = true ∧ ManifestLive c s p',
        'Member c w ∧ True ∧ ManifestLive c s p'),
    'effects-after-fence': ('Core',
        'w ∈ c.committee.core → s.seenOperation tx w = true ∧ s.fences tx w = false',
        'w ∈ c.committee.core → s.seenOperation tx w = true ∧ True'),
}


def checked(args):
    outcome = subprocess.run(args, cwd=LEAN, capture_output=True, text=True)
    if outcome.returncode:
        raise RuntimeError(outcome.stdout + outcome.stderr)
    return outcome.stdout + outcome.stderr


def no_oracle_checks():
    core = (LEAN / 'LeanCbcl/ConsensusFree/Core.lean').read_text()
    signing = core.split('def SignAllowed', 1)[1].split('instance', 1)[0]
    recording = core.split('def record ', 1)[1].split('def install ', 1)[0]
    assert all(word not in signing for word in ('balance', 'frontier', 'archive', 'Known', 'consensus', 'available'))
    assert 'if ' not in recording and 'quorum' not in recording
    execution = (LEAN / 'LeanCbcl/ConsensusFree/Execution.lean').read_text()
    commands = execution.split('inductive Command', 1)[1].split('def perform', 1)[0]
    assert all(word not in commands for word in ('reserve', 'grant', 'decide', 'consensus'))
    imports = '\n'.join(p.read_text() for p in (LEAN / 'LeanCbcl/ConsensusFree').glob('*.lean'))
    assert 'import LeanCbcl.AbortableHandoff' not in imports
    assert 'import LeanCbcl.AsyncReservation' not in imports
    return {'signing_uses_local_inputs': True, 'registration_has_no_selection_guard': True,
            'no_reservation_or_decision_command': True,
            'boundary': 'structural checks supplement independent review; not a general program-analysis proof'}


def compile_tree(binary, lean_path, sources, mutation=None):
    with tempfile.TemporaryDirectory(prefix='cbcl-cf-proof-') as directory:
        sandbox = Path(directory)
        # Lean resolves a module-root directory as a unit, so populate the
        # unchanged LeanCbcl imports explicitly rather than rely on path fallback.
        library = sandbox / 'LeanCbcl'
        library.mkdir()
        for entry in (LEAN / '.lake/build/lib/lean/LeanCbcl').iterdir():
            if entry.name != 'ConsensusFree':
                (library / entry.name).symlink_to(entry, target_is_directory=entry.is_dir())
        environment = dict(os.environ, LEAN_PATH=str(sandbox) + os.pathsep + lean_path)
        compiled = []
        for module in MODULES:
            relative = Path('LeanCbcl/ConsensusFree') / (module + '.lean')
            path = sandbox / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            source = sources[module]
            if mutation and module == mutation[0]:
                _, before, after = mutation
                assert before in source, (module, before)
                source = source.replace(before, after)
            path.write_text(source)
            outcome = subprocess.run([binary, '--root=' + str(sandbox), '-o', str(path.with_suffix('.olean')), str(path)],
                                     cwd=sandbox, env=environment, capture_output=True, text=True)
            evidence = outcome.stdout + outcome.stderr
            if outcome.returncode:
                return {'failed_module': module, 'compiled_dependencies': compiled, 'evidence': evidence}
            compiled.append(module)
        return {'compiled_modules': compiled}


def main():
    build = checked(['lake', 'build', 'LeanCbcl.ConsensusFree', 'LeanCbcl.ConsensusFree.Tests'])
    audit = json.loads(checked(['lake', 'env', 'lean', '--run', 'ConsensusFreeAudit.lean']))
    independent = checked(['lake', 'env', 'lean', '--run', '../proofs/validator-budget/consensus-free-independent-review.lean'])
    binary = checked(['lake', 'env', 'which', 'lean']).strip()
    lean_path = checked(['lake', 'env', 'printenv', 'LEAN_PATH']).strip()
    sources = {module: (LEAN / 'LeanCbcl/ConsensusFree' / (module + '.lean')).read_text() for module in MODULES}
    baseline = compile_tree(binary, lean_path, sources)
    assert 'failed_module' not in baseline, baseline
    print('isolated dependency-tree baseline passed', file=sys.stderr, flush=True)

    def inspect(item):
        name, mutation = item
        result = compile_tree(binary, lean_path, sources, mutation)
        assert 'failed_module' in result and result['failed_module'] != 'Core', (name, result)
        evidence = result['evidence']
        assert 'error:' in evidence and 'unexpected token' not in evidence and 'unknown module' not in evidence, (name, result)
        print(name + ': rejected by ' + result['failed_module'], file=sys.stderr, flush=True)
        return name, {'caught': True, **result}

    with ThreadPoolExecutor(max_workers=3) as pool:
        results = dict(pool.map(inspect, MUTANTS.items()))
    return {'build': build, 'executable_regressions': audit, 'independent_checks': independent,
            'no_oracle_checks': no_oracle_checks(), 'isolated_baseline': baseline, 'mutations': results,
            'scope': 'consensus-free independent budgets, sealed checkpoints, cancellation and typed currency; '
                     'full declared protocol-model safety refinement; no cryptographic/Rust/storage correspondence'}


if __name__ == '__main__':
    print(json.dumps(main(), indent=2))
