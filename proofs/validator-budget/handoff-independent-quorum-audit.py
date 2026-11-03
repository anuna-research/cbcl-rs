"""Independent finite audit for SPEC-023; not full lifecycle model checking.

Run: python3 proofs/validator-budget/handoff-independent-quorum-audit.py
Enumerates all activation-prefix subsets and exact abort quorums for f=0,1,2,
then attempts every remaining activation. Also checks distinct prepare choices
and late fast delivery to an already-aborted witness.
"""
from itertools import combinations, product
from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from handoff_model import HandoffModel
from model import Operation, Rejected


def subsets(values):
    values = list(values)
    for size in range(len(values) + 1):
        yield from combinations(values, size)


activation_cases = 0
for f in (0, 1, 2):
    n, q = 3*f + 1, 2*f + 1
    for before in subsets(range(n)):
        for stopped in combinations(range(n), q):
            m = HandoffModel(rights=(30, 0), headroom=(0, 0), f=f)
            parent = m.initial_versions[0]
            seals = [m.seal(v, 0, parent) for v in range(n)]
            cp = m.propose_checkpoint(0, parent, seals)
            for v in range(n):
                m.vote_checkpoint(v, cp)
            for v in before:
                m.activate_checkpoint(v, cp)
            handoff = [m.abort(v, 0, parent) for v in stopped]
            _, pinned = m.validate_handoff(handoff)
            for v in range(n):
                try:
                    m.activate_checkpoint(v, cp)
                except Rejected:
                    pass
            if len(m.activations.get(cp[0].id, set())) >= q:
                assert pinned == cp[0].id, (f, before, stopped)
            activation_cases += 1

prepare_cases = 0
for votes in product((0, 1, 2), repeat=3):
    for byz in ((), (0,), (1,), (0, 1)):
        m = HandoffModel(rights=(30, 0), headroom=(0, 0))
        parent = m.initial_versions[0]
        tx = m.propose(Operation(m.genesis, 0, parent, 'pay', 1, 1), 0)
        seals = [m.seal(v, 0, parent) for v in range(4)]
        proposals = [m.propose_checkpoint(0, parent, seals),
                     m.propose_checkpoint(0, parent, seals, (tx,))]
        for v, choice in enumerate(votes):
            if choice:
                m.vote_checkpoint(v, proposals[choice - 1])
        for choice in byz:
            m.vote_checkpoint(3, proposals[choice])
        assert sum(len(m.endorsements.get(p[0].id, ())) >= m.q
                   for p in proposals) <= 1
        prepare_cases += 1

m = HandoffModel(rights=(30, 0), headroom=(0, 0))
parent = m.initial_versions[0]
seals = [m.seal(v, 0, parent) for v in range(4)]
cp = m.propose_checkpoint(0, parent, seals)
for v in (0, 1, 3):
    m.vote_checkpoint(v, cp)
old_report = m.abort(2, 0, parent)
assert old_report.prepared is None
for v in (0, 1, 3):
    m.activate_checkpoint(v, cp)
m.install_checkpoint(2, cp)
assert m.known_prepared[2, 0, parent] == cp[0].id
assert m.abort(2, 0, parent) == old_report
late_delivery_quorums = 0
for others in combinations((0, 1, 3), 2):
    reports = [old_report] + [m.abort(v, 0, parent) for v in others]
    assert m.validate_handoff(reports)[1] == cp[0].id
    late_delivery_quorums += 1

print(json.dumps({'activation_abort_schedules': activation_cases,
                  'distinct_prepare_schedules': prepare_cases,
                  'late_delivery_quorums': late_delivery_quorums,
                  'result': 'pass',
                  'boundary': 'finite schedule audit; consensus oracle and Python/Lean refinement unproved'},
                 indent=2))
