"""SPEC-023 TEST-2300 reproducible baseline and isolated behavioral mutants."""
from pathlib import Path
import argparse
import json
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
MUTANTS = {
    'omit-prepare-evidence': ('evidence = self.known_prepared.get(key)', 'evidence = None',
                              'test_hidden_activation_certificate_preserved'),
    'activate-after-abort': ("require(key not in self.stopped, 'checkpoint activation stopped')",
                             "require(True, 'checkpoint activation stopped')",
                             'test_abort_stops_activation_prepare_and_operation'),
    'ignore-pinned-successor': ("require(cp.id == pinned, 'recovery must preserve prepared checkpoint')",
                                "require(True, 'recovery must preserve prepared checkpoint')",
                                'test_hidden_activation_certificate_preserved'),
    'reset-replayed-journal': ('return cp.id  # never reset a used journal',
                               'node.rights = self.k*cp.rights\n            return cp.id',
                               'test_recovery_replay_after_spending'),
    'install-prepare-only': ('self._quorum(activation_voters, self.activations.get(cp.id, set()))',
                            'pass  # mutant accepts preparation without activation',
                            'test_one_phase_install_is_disabled'),
}


def run():
    baseline = subprocess.run([sys.executable, '-m', 'unittest', 'test_handoff_model'],
                              cwd=ROOT, text=True, capture_output=True)
    assert baseline.returncode == 0, baseline.stdout + baseline.stderr
    results = {}
    for name, (before, after, test) in MUTANTS.items():
        with tempfile.TemporaryDirectory(prefix='cbcl-handoff-mutant-') as directory:
            dest = Path(directory)
            for filename in ('model.py', 'sealed_model.py', 'handoff_model.py', 'test_handoff_model.py'):
                source = (ROOT / filename).read_text()
                if filename == 'handoff_model.py':
                    assert before in source
                    source = source.replace(before, after)
                (dest / filename).write_text(source)
            outcome = subprocess.run([sys.executable, '-m', 'unittest',
                'test_handoff_model.HandoffTests.' + test], cwd=dest, capture_output=True, text=True)
            evidence = outcome.stdout + outcome.stderr
            assert outcome.returncode and 'Ran 1 test' in evidence and 'FAIL:' in evidence, evidence
            results[name] = {'caught': True, 'evidence': evidence}
    return {'baseline': baseline.stderr, 'mutants': results,
            'boundary': 'recovery agreement is a trusted abstract oracle, not implemented BFT'}


def lean_mutation():
    lean_dir = ROOT.parents[1] / 'lean-cbcl'
    source = (lean_dir / 'LeanCbcl/AbortableHandoff.lean').read_text()
    before = '| activate (s : Node) (cp : Nat) (openPhase : s.stopped = false)'
    assert before in source
    mutant = source.replace(before, '| activate (s : Node) (cp : Nat) (openPhase : True)')
    with tempfile.TemporaryDirectory(prefix='cbcl-handoff-lean-') as directory:
        path = Path(directory) / 'AbortableHandoff.lean'
        path.write_text(mutant)
        result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=lean_dir,
                                capture_output=True, text=True)
        evidence = result.stdout + result.stderr
        assert result.returncode and 'unsolved goals' in evidence and 'unknown module' not in evidence, evidence
        return {'mutation': 'allow fresh activation after abort', 'caught': True, 'evidence': evidence}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean-mutation', action='store_true')
    args = parser.parse_args()
    result = run()
    if args.lean_mutation:
        result['lean_mutation'] = lean_mutation()
    print(json.dumps(result, indent=2))
