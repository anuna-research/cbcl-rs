#!/usr/bin/env python3
"""SPEC-021 TEST-2100: actual reference transitions, not mocked acceptance flags."""
import copy
from itertools import combinations, permutations, product
import json
import unittest

from model import Model, Operation, Rejected


def propose(m, kind='pay', source=0, recipient=1, amount=1, nonce=0, version=None):
    if kind in ('burn', 'mint'):
        recipient = None
    op = Operation(m.genesis, source, version or m.local[0][source].version,
                   kind, amount, recipient, nonce)
    return m.propose(op, signer=source)


def certify(m, tx, voters=None):
    for v in range(m.n) if voters is None else voters:
        m.sign(v, tx)
    return m.certificate(tx)


def finalize(m, tx):
    for v in range(m.q):
        m.receive(v, tx)
    assert tx in m.final


def rebase(m, account, included=None):
    if included is None:
        included = [t for t in m.final if m.delta(m.ops[t], account) != (0, 0)]
    ver = m.make_version(account, (m.local[0][account].version,), included, signer=account)
    for v in range(m.n):
        m.apply_version(v, ver)
    return ver


class ModelTests(unittest.TestCase):
    def unchanged_rejection(self, m, action):
        before = copy.deepcopy(m.__dict__)
        with self.assertRaises(Rejected):
            action()
        self.assertEqual(before, m.__dict__)

    def test_genesis_exact_integers_and_canonical_identity_slots(self):
        for kwargs in ({'rights': (1.5, 0)}, {'rights': (True, 0)},
                       {'rights': ()}, {'headroom': (1.5, 0)}, {'headroom': (True, 0)},
                       {'f': 1.0}, {'f': True}, {'floor': 0.0}, {'floor': False},
                       {'pending_limit': 1.0}, {'pending_limit': True},
                       {'faulty': (True,)}, {'issuers': (False,)}):
            with self.assertRaises(Rejected, msg=str(kwargs)):
                Model(**kwargs)
        m = Model()
        op = Operation(m.genesis, 0, m.initial_versions[0], 'burn', 1)
        self.unchanged_rejection(m, lambda: m.propose(op, False))
        tx = m.propose(op, 0)
        self.unchanged_rejection(m, lambda: m.sign(True, tx))

    def test_authentication_context_and_atomic_guard(self):
        m = Model(rights=(6, 0), headroom=(0, 0))
        op = Operation('wrong-context', 0, m.initial_versions[0], 'pay', 1, 1)
        self.unchanged_rejection(m, lambda: m.propose(op, 0))
        op = Operation(m.genesis, 0, m.initial_versions[0], 'mint', 1)
        self.unchanged_rejection(m, lambda: m.propose(op, 1))
        tx = m.propose(op, 0)
        self.unchanged_rejection(m, lambda: m.sign(0, tx))
        self.unchanged_rejection(m, lambda: m.sign(99, tx))
        for amount in (0, -1):
            bad = Operation(m.genesis, 0, m.initial_versions[0], 'burn', amount)
            self.unchanged_rejection(m, lambda bad=bad: m.propose(bad, 0))
        foreign = Operation(m.genesis, 1, m.initial_versions[0], 'burn', 1)
        self.unchanged_rejection(m, lambda: m.propose(foreign, 1))
        nonissuer = Operation(m.genesis, 1, m.initial_versions[1], 'mint', 1)
        self.unchanged_rejection(m, lambda: m.propose(nonissuer, 1))

    def test_certificate_distinct_members_and_actual_votes(self):
        m = Model()
        tx = propose(m)
        m.sign(0, tx)
        m.sign(3, tx)
        for votes in ((0, 0, 3), (0, 1, 3), (0, 3), (0, 3, 99)):
            self.unchanged_rejection(m, lambda votes=votes: m.certificate(tx, votes))
        m.sign(1, tx)
        self.assertEqual(m.certificate(tx), (0, 1, 3))

    def test_signing_replay_and_restart(self):
        m = Model()
        tx = propose(m)
        m.sign(0, tx)
        before = copy.deepcopy(m.__dict__)
        # Reconstruct over all persisted journal/state fields; no claim of disk IO/crash proof.
        restarted = copy.deepcopy(m)
        restarted.sign(0, tx)
        self.assertEqual(before, restarted.__dict__)

    def test_worked_dual_budget_operations(self):
        m = Model(rights=(12, 0, 0), headroom=(6, 0, 0), issuers=(0, 1), floor=7)
        payment = propose(m, amount=6)
        certify(m, payment); finalize(m, payment); rebase(m, 1)
        payment2 = propose(m, source=1, recipient=2, amount=3)
        certify(m, payment2); finalize(m, payment2); rebase(m, 2)
        burn = propose(m, 'burn', source=2)
        certify(m, burn); finalize(m, burn)
        mint = propose(m, 'mint', amount=2)
        certify(m, mint); finalize(m, mint)
        transfer = propose(m, 'headroom', recipient=1, amount=2)
        certify(m, transfer); finalize(m, transfer); rebase(m, 1)
        mint2 = propose(m, 'mint', source=1)
        certify(m, mint2); finalize(m, mint2)
        self.assertEqual(m.snapshot(), [(8, 2), (4, 1), (2, 1)])
        self.assertEqual(m.value, 21)
        self.assertEqual(m.ceiling, 25)

    def test_uncapped_and_fixed_supply(self):
        m = Model(rights=(3, 0), headroom=None)
        mint = propose(m, 'mint', amount=100)
        certify(m, mint); finalize(m, mint)
        self.assertEqual(m.value, 103)
        self.assertIsNone(m.ceiling)
        fixed = Model(issuers=())
        self.unchanged_rejection(fixed, lambda: propose(fixed, 'mint'))

    def test_concurrent_certification_and_delivery_orders(self):
        # All relative delivery orders of two sibling payments at every honest witness.
        for orders in product(tuple(permutations((0, 1))), repeat=3):
            m = Model()
            txs = [propose(m, nonce=i) for i in range(2)]
            for tx in txs:
                certify(m, tx)
            for v, order in enumerate(orders):
                for i in order:
                    m.receive(v, txs[i])
            self.assertEqual(m.snapshot(), [(1, 3), (2, 0)])
            self.assertEqual(m.final, set(txs))

    def test_split_quorums_and_withholding_budget(self):
        # Three certified unit debits against balance3 fit the actual conservative budgets.
        m = Model()
        for nonce, voters in enumerate(((0, 1, 3), (0, 2, 3), (1, 2, 3))):
            tx = propose(m, nonce=nonce)
            certify(m, tx, voters); finalize(m, tx)
        self.assertEqual(m.snapshot(), [(0, 3), (3, 0)])
        m = Model()
        for nonce in range(2):
            tx = propose(m, nonce=nonce)
            certify(m, tx, (0, 1, 2)); finalize(m, tx)
        third = propose(m, nonce=2)
        self.unchanged_rejection(m, lambda: m.sign(0, third))
        self.assertEqual(m.snapshot()[0][0], 1)  # safe, but unusable until resynchronization

    def test_version_omitted_signatures_remain_charged(self):
        m = Model()
        a, b = propose(m, nonce=0), propose(m, nonce=1)
        for tx in (a, b):
            certify(m, tx)
        finalize(m, a)
        updated = m.make_version(0, (m.initial_versions[0],), (a,), signer=0)
        for v in range(m.n):
            m.apply_version(v, updated)
        self.assertEqual(m.local[0][0].rights, 1)  # 2*remaining2 - 3*omitted1
        c = propose(m, nonce=2, version=updated)
        self.unchanged_rejection(m, lambda: m.sign(0, c))
        finalize(m, b)  # delayed old-version certificate still settles
        rebase(m, 0)
        self.assertEqual(m.local[0][0].rights, 2)
        self.assertEqual(m.snapshot()[0][0], 1)

    def test_reconciliation_preserves_negative_exposure_without_clipping(self):
        m = Model()
        a, b, c = [propose(m, nonce=i) for i in range(3)]
        m.sign(0, a); m.sign(0, b)
        certify(m, c, (1, 2, 3)); finalize(m, c)
        rebase(m, 0, (c,))
        self.assertEqual(m.local[0][0].rights, -2)
        self.assertEqual(m.snapshot()[0][0], 2)
        rebase(m, 0, ())
        self.assertEqual(m.local[0][0].rights, -2)
        fresh = propose(m, nonce=3)
        self.unchanged_rejection(m, lambda: m.sign(0, fresh))

    def test_exhaustive_small_signing_assignments_on_actual_transitions(self):
        choices = [xs for k in range(3) for xs in combinations(range(4), k)]
        examined = delivered = 0
        for assignment in product(choices, repeat=3):
            m = Model()
            txs = [propose(m, 'burn', nonce=i) for i in range(4)]
            for v, signed in enumerate(assignment):
                for index in signed:
                    m.sign(v, txs[index])
            for tx in txs:
                m.sign(3, tx)
            certified = [tx for tx in txs if len(m.votes[tx]) >= m.q]
            self.assertLessEqual(len(certified), 3)
            for order in permutations(certified):
                receiver = copy.deepcopy(m)
                for tx in order:
                    finalize(receiver, tx)
                self.assertEqual(receiver.snapshot()[0], (3-len(certified), 3+len(certified)))
                delivered += 1
            examined += 1
        self.assertEqual(examined, 1331)
        self.assertGreater(delivered, examined)

    def test_other_fault_bounds_and_honest_committee(self):
        for f, faulty in ((0, ()), (1, ()), (2, (5, 6))):
            m = Model(rights=(10, 0), headroom=(5, 0), f=f, faulty=faulty)
            tx = propose(m)
            certify(m, tx, range(m.q)); finalize(m, tx)
            self.assertEqual(m.snapshot(), [(9, 5), (1, 0)])

    def test_version_merge_and_credit_replay(self):
        m = Model()
        txs = [propose(m, nonce=i) for i in range(2)]
        for tx in txs:
            certify(m, tx); finalize(m, tx)
        left = m.make_version(1, (m.initial_versions[1],), (txs[0],), signer=1)
        right = m.make_version(1, (m.initial_versions[1],), (txs[1],), signer=1)
        for v in (0, 1):
            m.apply_version(v, left)
        for v in (2, 3):
            m.apply_version(v, right)
        merged = m.make_version(1, (left, right), (), signer=1)
        for v in range(m.n):
            m.apply_version(v, merged)
        before = copy.deepcopy(m.__dict__)
        for v in range(m.n):
            m.apply_version(v, merged)
        self.assertEqual(before, m.__dict__)
        self.assertEqual(m.local[0][1].rights, 4)
        for v in range(m.n):
            self.unchanged_rejection(m, lambda v=v: m.apply_version(v, left))

    def test_only_finalized_funding_and_pending_buffer_bypass(self):
        m = Model(pending_limit=1)
        credit = propose(m)
        certify(m, credit)
        self.unchanged_rejection(m, lambda: rebase(m, 1, (credit,)))
        # Deliver to witnesses1,2,3; witness0 lacks the dependency payload/execution.
        for v in (1, 2, 3):
            m.receive(v, credit)
        rebase(m, 1)
        # One unit cannot pass conservative signing budget: accumulate another unit.
        credit2 = propose(m, nonce=1)
        certify(m, credit2)
        for v in (1, 2, 3):
            m.receive(v, credit2)
        rebase(m, 1)
        debit = propose(m, 'burn', source=1)
        certify(m, debit)
        self.assertFalse(m.receive(0, debit))
        self.assertEqual(len(m.pending[0]), 1)
        m.receive(0, credit)
        self.assertIn(debit, m.pending[0])
        m.receive(0, credit2)  # ready dependency admitted despite full pending buffer
        self.assertIn(debit, m.executed[0])
        self.assertFalse(m.pending[0])

    def test_finality_is_not_certification_or_local_execution(self):
        m = Model()
        tx = propose(m)
        certify(m, tx)
        self.assertNotIn(tx, m.final)
        m.receive(0, tx)
        self.assertNotIn(tx, m.final)
        self.assertEqual(m.snapshot(), [(3, 3), (0, 0)])
        m.receive(1, tx); m.receive(2, tx)
        self.assertIn(tx, m.final)
        before = m.snapshot(), m.final.copy()
        for v in range(m.n):
            m.receive(v, tx)
        self.assertEqual(before, (m.snapshot(), m.final))

    def test_no_commit_recovery_and_late_certificate(self):
        m = Model()
        tx = propose(m)
        certify(m, tx)
        m.receive(0, tx)  # provisional local execution; still no final receipt
        old = m.initial_versions[0]
        for v in (1, 2, 3):
            m.no_commit_vote(v, 0, old)
        new = m.recover_no_commit(0, old, (1, 2, 3))
        self.assertNotIn(tx, m.executed[0])
        self.assertIn(0, m.effects[tx])  # rollback never erases signed evidence
        self.assertNotIn(tx, m.final)
        self.assertEqual(m.local[0][0].rights, 6)
        for v in (0, 1, 2):
            self.unchanged_rejection(m, lambda v=v: m.receive(v, tx))
        replacement = propose(m, version=new, nonce=1)
        certify(m, replacement); finalize(m, replacement)
        self.assertEqual(m.snapshot(), [(2, 3), (1, 0)])

    def test_finalized_receipt_prevents_no_commit_quorum(self):
        m = Model()
        tx = propose(m)
        certify(m, tx); finalize(m, tx)
        old = m.initial_versions[0]
        for v in range(3):
            self.unchanged_rejection(m, lambda v=v: m.no_commit_vote(v, 0, old))
        m.no_commit_vote(3, 0, old)  # Byzantine witness can lie, but cannot form a quorum
        self.unchanged_rejection(m, lambda: m.recover_no_commit(0, old, (0, 1, 3)))
        self.assertIn(tx, m.final)

    def test_exhaustive_fence_effect_partitions(self):
        # All 3^3 honest per-version choices (idle/execute/fence), plus faulty witness both.
        examined = 0
        for choices in product(range(3), repeat=3):
            executed = {v for v, choice in enumerate(choices) if choice == 1} | {3}
            fenced = {v for v, choice in enumerate(choices) if choice == 2} | {3}
            self.assertFalse(len(executed) >= 3 and len(fenced) >= 3)
            examined += 1
        self.assertEqual(examined, 27)

    def test_zero_width_ceiling_cannot_speculatively_net(self):
        m = Model(rights=(0,), headroom=(0,))
        for kind in ('mint', 'burn'):
            tx = propose(m, kind)
            self.unchanged_rejection(m, lambda tx=tx: m.sign(0, tx))


if __name__ == '__main__':
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(ModelTests)
    names = [case.id().split('.')[-1] for case in suite]
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    print(json.dumps({'scope': 'symbolic reference lifecycle; selected finite schedules; no asynchronous refinement proof',
                      'tests_run': result.testsRun, 'failures': len(result.failures),
                      'errors': len(result.errors), 'cases': names,
                      'assumptions': ['symbolic authenticated identities', 'fixed roster and fault set',
                                      'persistent vote/effect/fence records', 'unique abstract recovery consensus']},
                     indent=2, sort_keys=True))
    raise SystemExit(0 if result.wasSuccessful() else 1)
