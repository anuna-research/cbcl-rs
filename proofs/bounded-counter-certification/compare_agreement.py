#!/usr/bin/env python3
"""Finite design counterexamples for SPEC-020 ADR-2001.

No BGLA/CryptoConcurrency implementation, signatures, recovery or liveness proof.
Candidate IDs stand for distinct authenticated operations. Arithmetic examples
assume one pinned checkpoint and no unseen/uncertified incoming credits.
"""
from itertools import combinations, product
import json


def powerset(items):
    return [frozenset(xs) for n in range(len(items) + 1)
            for xs in combinations(items, n)]


def subset_certificate_attack():
    # f=1, n=4, q=3. Each honest replica endorses at most 2 of 3 unit debits.
    votes = {'A': {0, 1, 3}, 'B': {0, 2, 3}, 'C': {1, 2, 3}}
    assert all(len(v) == 3 for v in votes.values())
    assert all(sum(r in v for v in votes.values()) <= 2 for r in range(3))
    assert len(votes) > 2
    return {'capacity': 2, 'quorum': 3, 'byzantine': [3],
            'certificates': {k: sorted(v) for k, v in votes.items()}}


def comparable_whole_sets():
    # Enumerate all monotonic two-signature histories of 3 honest acceptors.
    # Each pair is that acceptor's first/second signed complete debit set.
    states = powerset(('A', 'B', 'C'))
    valid = [s for s in states if len(s) <= 2]
    histories = [(a, b) for a in valid for b in valid if a <= b]
    checked = 0
    for choices in product(histories, repeat=3):
        certified = [s for s in valid if sum(any(s == x for x in h) for h in choices) >= 2]
        # One Byzantine witness may sign all values, so 2 honest + 1 faulty suffices.
        for a, b in combinations(certified, 2):
            assert a <= b or b <= a
            assert len(a | b) <= 2
            checked += 1
    return {'honest_histories_examined': len(histories) ** 3,
            'certified_pairs_examined': checked,
            'scope': 'two signatures per honest witness, fixed known capacity only'}


def main():
    report = {'scope': 'finite design checks, not a protocol or proof of asynchronous liveness'}
    for name in ('rights', 'headroom'):
        a, b, capacity = {'A': 80}, {'B': 80}, 100
        assert sum(a.values()) <= capacity and sum(b.values()) <= capacity
        union = dict(a, **b)
        assert sum(union.values()) > capacity
        report[name + '_non_join_closed'] = {'capacity': capacity, 'a': a, 'b': b,
                                             'union_consumption': sum(union.values())}
    # Pairwise compatibility does not establish safety of a whole batch.
    assert all(len(s) <= 2 for s in combinations(('A', 'B', 'C'), 2))
    assert len({'A', 'B', 'C'}) > 2
    report['pairwise_compatible_triple_overspends'] = True
    report['per_operation_quorum_attack'] = subset_certificate_attack()
    report['whole_set_monotonic_signature_check'] = comparable_whole_sets()

    # A chain in the evidence powerset may include an invalid larger state.
    evidence = [frozenset(), frozenset({'A'}), frozenset({'A', 'B'})]
    assert all(a <= b for a, b in zip(evidence, evidence[1:]))
    assert 80 * len(evidence[-1]) > 100
    report['comparable_evidence_can_overspend'] = True

    # A deterministic hash-ordered greedy selector converges but retracts a receipt.
    def select(ids):
        return frozenset(sorted(ids)[:1])  # two 80-unit payments, 100 funds
    before, after = select({'z'}), select({'a', 'z'})
    assert not before <= after
    report['hash_filter_retracts_receipt'] = {'before': sorted(before), 'after': sorted(after)}

    # Two checkpoints net to zero, but no first operation can execute. At floor==ceiling,
    # neither a unit mint nor unit burn has the required starting budget.
    rights = headroom = 0
    mint_delta, burn_delta = (1, -1), (-1, 1)
    assert rights + mint_delta[0] + burn_delta[0] == 0
    assert headroom + mint_delta[1] + burn_delta[1] == 0
    assert headroom < 1 and rights < 1
    report['net_only_dual_budget_check_allows_unfunded_cycle'] = True

    # Joint certificate protects both dimensions; independent dimension checks are insufficient.
    def valid(r, h, rights_debits, headroom_debits):
        return sum(rights_debits) <= r and sum(headroom_debits) <= h
    assert not valid(2, 1, (1,), (1, 1))
    assert not valid(1, 2, (1, 1), (1,))
    assert valid(2, 2, (1, 1), (1, 1))
    report['both_budget_dimensions_required'] = True
    report['decision'] = 'keep escrow kernel; model invariant-aware per-account sets before certification runtime'
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
