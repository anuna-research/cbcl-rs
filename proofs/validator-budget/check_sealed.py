"""Run repaired profile tests and isolated behavioral mutants (TEST-2200)."""
from pathlib import Path
import subprocess
import sys
import tempfile
import json

ROOT = Path(__file__).resolve().parent
MUTANTS = {
    'accept-incorrect-cut': ("require(rebuilt == cp,", "require(True,", 'test_omitted_report_and_invalid_endorsements'),
    'sign-after-seal': ('require(not any(r.witness', 'require(True or not any(r.witness', 'test_seal_blocks_fresh_votes_but_allows_retry'),
    'vote-two-successors': ('require(key not in self.choices or', 'require(True or key not in self.choices or', 'test_vote_once_and_own_report_required'),
    'double-credit': ('for t in credited)', 'for t in tuple(credited)*2)', 'test_credit_once_mint_burn_and_recipient'),
}


def run():
    baseline = subprocess.run([sys.executable, '-m', 'unittest', 'test_sealed_model'], cwd=ROOT,
                              capture_output=True, text=True)
    if baseline.returncode:
        raise RuntimeError(baseline.stdout + baseline.stderr)
    results = {}
    for name, (before, after, test) in MUTANTS.items():
        with tempfile.TemporaryDirectory(prefix='cbcl-sealed-mutant-') as directory:
            dest = Path(directory)
            for filename in ('model.py', 'sealed_model.py', 'test_sealed_model.py'):
                text = (ROOT / filename).read_text()
                if filename == 'sealed_model.py':
                    assert before in text
                    text = text.replace(before, after)
                (dest / filename).write_text(text)
            outcome = subprocess.run([sys.executable, '-m', 'unittest',
                                      'test_sealed_model.SealedTests.' + test], cwd=dest,
                                     capture_output=True, text=True)
            evidence = outcome.stdout + outcome.stderr
            assert outcome.returncode and 'Ran 1 test' in evidence and 'FAIL:' in evidence, evidence
            results[name] = {'caught': True, 'evidence': evidence}
    return {'baseline': baseline.stderr, 'mutations': results,
            'scope': 'finite symbolic tests; full asynchronous refinement remains open'}


if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
