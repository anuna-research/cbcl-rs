#!/usr/bin/env python3
"""SPEC-021 BUG-2100: reproduce the unmutated asynchronous safety refutation.

Exit success means the counterexample reproduced, NOT that the model is safe.
The final diagnostic assertion is deliberately caught and reported as a failure
of the model's claimed resource invariant, not as an input/protocol rejection.
"""
import os
import json
from model import Model, Operation


def reproduce(update_zero=True):
    assert not os.getenv('CBCL_BUDGET_MODEL_MUTATION'), 'refutation requires unmutated model'
    m = Model(rights=(30, 0), headroom=(0, 0), mutation='')
    events = []

    def log(action, **details):
        events.append(dict(action=action, honest_budgets=[m.local[v][0].rights for v in range(3)],
                           balances=m.snapshot(), **details))

    def propose(nonce, amount, version=None):
        op = Operation(m.genesis, 0, version or m.initial_versions[0], 'pay', amount, 1, nonce)
        return m.propose(op, 0)

    def certify(name, tx, voters):
        for v in voters:
            m.sign(v, tx)
        assert m.certificate(tx, voters) == tuple(voters)
        log('certify', payment=name, amount=m.ops[tx].amount, signers=list(voters))

    def finalize(name, tx):
        for v in (0, 1, 2):
            m.receive(v, tx)
        assert tx in m.final
        log('finalize', payment=name, effects=sorted(m.effects[tx]))

    a, b, c = [propose(i, 10) for i in range(3)]
    for name, tx, voters in [('A', a, (0, 1, 3)), ('B', b, (0, 2, 3)), ('C', c, (1, 2, 3))]:
        certify(name, tx, voters)
    finalize('C', c)
    version = m.make_version(0, (m.initial_versions[0],), (c,), signer=0)
    for v in range(4) if update_zero else (1, 2, 3):
        m.apply_version(v, version)
    log('partial-version-update', covered=['C'], updated_zero=update_zero)
    d = propose(3, 3, version)
    certify('D', d, (1, 2, 3))
    finalize('D', d)
    finalize('A', a)
    # All protocol guards succeed. The diagnostic check fails after effects quorum
    # records B as final. Treat that as a refutation, never as a successful safe run.
    caught = None
    try:
        finalize('B', b)
    except AssertionError as e:
        caught = str(e)
    assert caught == 'negative finalized rights', caught
    assert m.snapshot() == [(-3, 0), (33, 0)]
    assert all(t in m.final and len(m.votes[t]) >= 3 and len(m.effects[t]) >= 3 for t in (a, b, c, d))
    # Audit the local accounting identities independently without assuming safety.
    for v in range(3):
        local = m.local[v][0]
        recognized, _ = m.recognized_balance(local.covered, 0)
        reserved = local.signed - local.covered - local.released
        assert local.rights == m.k*recognized - m.scale*sum(m.cost(m.ops[t])[0] for t in reserved)
    log('final-invariant-failure', payment='B', reason=caught)
    if not update_zero:
        assert all(all(x >= 0 for x in event['honest_budgets']) for event in events)
    return {'mutation': m.mutation, 'all_protocol_guards_passed': True,
            'diagnostic_failure': caught, 'finalized_payment_total': 33,
            'initial_rights': 30, 'trace': events}


if __name__ == '__main__':
    print(json.dumps({'result': 'asynchronous safety refuted',
                      'scope': 'current executable model, not a claim about an external paper',
                      'all_update': reproduce(),
                      'only_nonnegative_quorum_updates': reproduce(False)}, indent=2, sort_keys=True))
