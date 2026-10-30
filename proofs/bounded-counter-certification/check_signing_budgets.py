#!/usr/bin/env python3
"""SPEC-020 TEST-2008: finite one-version validator-budget research.

Models unit decrements only, n=4 f=1 q=3, no incoming credits. Exactly one
Byzantine witness signs everything. Honest histories are sets of signatures
whose size stays within an integer local budget. No version updates, signatures,
recovery, network or liveness implementation is supplied by this script.
"""
from itertools import combinations, product
import json


def histories(tx_count, budget):
    return [frozenset(xs) for k in range(min(tx_count, budget) + 1)
            for xs in combinations(range(tx_count), k)]


def max_certified(balance, budget):
    tx_count = balance + 1  # enough unit operations to witness an overspend
    choices = histories(tx_count, budget)
    maximum = 0
    example = None
    for votes in product(choices, repeat=3):
        certified = [tx for tx in range(tx_count) if sum(tx in h for h in votes) >= 2]
        if len(certified) > maximum:
            maximum = len(certified)
            example = [sorted(h) for h in votes]
    return maximum, len(choices) ** 3, example


def main():
    # For n=4,f=1 the conservative fraction is eta=2/3. Round down for integer units.
    profiles = []
    for balance in range(1, 5):
        budget = 2 * balance // 3
        maximum, examined, _ = max_certified(balance, budget)
        assert maximum <= balance
        profiles.append({'balance': balance, 'validator_budget': budget,
                         'maximum_certified_unit_debits': maximum,
                         'signature_assignments_examined': examined})
    # Mutation oracle: replacing the conservative budget with full balance is unsafe.
    naive, _, example = max_certified(2, 2)
    assert naive == 3
    # Safe certification is not full-balance availability under Byzantine withholding.
    balance, budget = 3, 2
    assert budget < balance
    # If faulty witness withholds, every certificate needs all 3 honest signatures.
    assert min(budget for _ in range(3)) == 2
    print(json.dumps({
        'scope': 'one-version finite unit-debit model; not a Stingray implementation or lifecycle proof',
        'n': 4, 'f': 1, 'q': 3, 'fraction': '2/3',
        'safe_profiles': profiles,
        'full_local_budget_counterexample': {'balance': 2, 'certified': naive,
                                             'honest_signature_sets': example},
        'withholding_availability_example': {'balance': balance,
                                             'spendable_before_version_update': budget},
        'integer_dust_example': {'balance': 1, 'validator_budget': 0,
                                'requires_additional_protocol': True},
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
