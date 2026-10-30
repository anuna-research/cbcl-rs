#!/usr/bin/env python3
"""Finite certification checks supporting SPEC-019 ADR-1915.

Research harness, NOT a network/certificate implementation or a cryptographic
proof. Signer labels below stand for already verified, distinct witness keys.
The checks cover static quorum intersection and constructive negative examples;
they do not establish reliable broadcast, liveness or CBCL integration.
Run: python3 proofs/bounded-counter-certification/check_quorums.py
"""
from dataclasses import dataclass, replace
from itertools import combinations, combinations_with_replacement
import json


def quorums(n, q):
    return [frozenset(xs) for xs in combinations(range(n), q)]


def intersection_check(n, f):
    assert n == 3 * f + 1
    q = 2 * f + 1
    compared = 0
    for a, b in combinations_with_replacement(quorums(n, q), 2):
        for bad in map(frozenset, combinations(range(n), f)):
            assert (a & b) - bad, (n, f, a, b, bad)
            compared += 1
    return {"n": n, "f": f, "q": q, "quorum_pair_fault_cases": compared}


@dataclass(frozen=True)
class Statement:
    domain: str = "cbcl-account-certification-research-v1"
    genesis: str = "genesis-and-roster-hash"
    dialect: str = "dialect-body-hash"
    root_cast: str = "authenticated-root-context-hash"
    thread: str = "coin-thread"
    field: str = "coins"
    owner: str = "alice-key"
    sequence: int = 1
    previous: str = "opener-hash"
    act: str = "pay-bob-hash"

    def slot(self):
        # Configuration/asset identity is fixed, NOT chosen per candidate.
        return self.genesis, self.thread, self.field, self.owner, self.sequence


class Witness:
    def __init__(self):
        self.persisted = {}

    def acknowledge(self, statement):
        key = statement.slot()
        if key in self.persisted and self.persisted[key] != statement:
            return False
        self.persisted[key] = statement
        return True


def check_certificate(expected, statement, signers, n=4, q=3):
    """Structural finite model; real verification must authenticate every key."""
    return (
        statement == expected
        and len(signers) == len(set(signers))
        and set(signers) <= set(range(n))
        and len(signers) >= q
    )


def main():
    report = {"scope": "finite research checks; no network or cryptographic proof"}
    report["safe_static_profiles"] = [intersection_check(4, 1), intersection_check(7, 2)]

    # Wrong threshold: a faulty intersection member can endorse both values.
    a, b, bad = frozenset([0, 1]), frozenset([0, 2]), frozenset([0])
    assert not ((a & b) - bad)
    report["insufficient_quorum_counterexample"] = {
        "n": 4, "f": 1, "q": 2, "a": sorted(a), "b": sorted(b), "faulty": sorted(bad)
    }

    first = Statement()
    fork = replace(first, act="pay-carol-hash")
    witness = Witness()
    assert witness.acknowledge(first)
    assert witness.acknowledge(first)  # retransmission is idempotent
    assert not witness.acknowledge(fork)
    report["same_slot_conflict_rejected"] = True

    # A persisted choice must survive reboot. Resetting it allows two QCs:
    # A={0,1,3}, B={0,2,3}; witness 3 is faulty, witness 0 forgot its vote.
    restarted_without_persistence = Witness()
    assert restarted_without_persistence.acknowledge(fork)
    assert check_certificate(first, first, [0, 1, 3])
    assert check_certificate(fork, fork, [0, 2, 3])
    report["forgotten_lock_counterexample"] = True

    # Locking by message hash instead of account slot also signs both forks.
    broken_locks = {}
    for proposal in (first, fork):
        broken_locks.setdefault(proposal.act, proposal)
    assert len(broken_locks) == 2
    report["per_hash_lock_counterexample"] = True

    # Honest witnesses may split on a faulty owner's conflicting proposals.
    # Witness 3 is unavailable/faulty and withholds its vote. No QC need form.
    honest_choices = {0: "A", 1: "A", 2: "B"}
    assert max(list(honest_choices.values()).count(x) for x in ("A", "B")) < 3
    report["equivocating_owner_can_stall"] = True

    assert check_certificate(first, first, [0, 1, 2])
    assert not check_certificate(first, first, [0, 0, 1])
    assert not check_certificate(first, first, [0, 1, 99])
    assert not check_certificate(first, first, [0, 1])
    changes = {
        "domain": "another-protocol", "genesis": "sender-chosen-roster",
        "dialect": "another-dialect", "root_cast": "another-cast",
        "thread": "another-thread", "field": "another-counter", "owner": "bob-key",
        "sequence": 2, "previous": "another-parent", "act": "another-act",
    }
    for key, value in changes.items():
        assert not check_certificate(first, replace(first, **{key: value}), [0, 1, 2])
    report["context_and_distinct_witness_checks"] = "pass"

    # Changing membership invalidates the original quorum-intersection argument.
    old, new = frozenset([0, 1, 2]), frozenset([4, 5, 6])
    assert not old & new
    report["uncoordinated_roster_change_counterexample"] = True
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
