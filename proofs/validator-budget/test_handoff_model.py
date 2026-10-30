"""SPEC-023 TEST-2300: explicit abstract-consensus handoff schedules."""
import unittest
from dataclasses import replace
from copy import deepcopy
from model import Operation, Rejected
from handoff_model import HandoffModel, RecoveryDecision


class HandoffTests(unittest.TestCase):
    def model(self, **kwargs):
        return HandoffModel(rights=kwargs.pop('rights', (30, 0)),
                            headroom=kwargs.pop('headroom', (0, 0)), **kwargs)

    def op(self, m, amount=5, voters=(), source=0, kind='pay', recipient=1, nonce=0):
        t = m.propose(Operation(m.genesis, source, m.local[0][source].version,
                                kind, amount, recipient, nonce), source)
        for v in voters:
            m.sign(v, t)
        return t

    def proposals(self, m, candidates=(), receipts=(), account=0):
        parent = m.local[0][account].version
        reports = [m.seal(v, account, parent) for v in range(3)]
        return m.propose_checkpoint(account, parent, reports, candidates, receipts)

    def prepare(self, m, proposal):
        for v in (0, 1, 3):
            m.vote_checkpoint(v, proposal)

    def activate(self, m, proposal):
        self.prepare(m, proposal)
        for v in (0, 1, 3):
            m.activate_checkpoint(v, proposal)

    def handoff(self, m, account=0, parent=None, witnesses=(0, 1, 2)):
        parent = parent or m.initial_versions[account]
        return [m.abort(v, account, parent) for v in witnesses]

    def recover(self, m, reports, proposal=None, witnesses=(0, 1, 2, 3)):
        proposal = proposal or m.recovery_proposal(reports)
        decision = m.decide_recovery(reports, proposal)
        for v in witnesses:
            m.install_recovery(v, decision, proposal)
        return decision, proposal

    def finalize(self, m, tx):
        for v in range(3):
            m.receive(v, tx)

    def split(self, m):
        # Uncertified extra operation distinguishes two valid semantic proposals.
        t = self.op(m)
        a = self.proposals(m)
        b = self.proposals(m, candidates=(t,))
        m.vote_checkpoint(0, a)
        m.vote_checkpoint(1, b)
        m.vote_checkpoint(2, b)
        return a, b

    def test_split_prepare_votes_recover(self):
        m = self.model()
        a, b = self.split(m)
        with self.assertRaises(Rejected):
            m.vote_checkpoint(0, b)
        with self.assertRaises(Rejected):
            m.install_checkpoint(0, b)
        reports = self.handoff(m)
        decision, proposal = self.recover(m, reports, a)
        self.assertEqual(m.local[0][0].version, a[0].id)
        self.assertEqual(m.decide_recovery(reports, proposal), decision)
        self.op(m, voters=(0, 1, 3), nonce=1)

    def test_hidden_activation_certificate_preserved(self):
        m = self.model()
        a, b = self.split(m)
        # b has 1/2 votes; Byzantine 3 completes preparation. Activation is hidden.
        m.vote_checkpoint(3, b)
        for v in (1, 2, 3):
            m.activate_checkpoint(v, b)
        reports = self.handoff(m, witnesses=(0, 1, 3))
        self.assertTrue(any(r.prepared == b[0].id for r in reports))
        with self.assertRaises(Rejected):
            m.decide_recovery(reports, a)
        decision, chosen = self.recover(m, reports)
        self.assertEqual(chosen[0], b[0])
        # Late fast certificate and recovery install are semantic replays.
        self.op(m, voters=(0, 1, 3), nonce=2)
        spent = m.local[0][0].rights
        m.install_checkpoint(0, b)
        m.install_recovery(0, decision, chosen)
        self.assertEqual(m.local[0][0].rights, spent)

    def test_single_activation_discloses_prepare(self):
        m = self.model()
        a = self.proposals(m)
        self.prepare(m, a)
        m.activate_checkpoint(0, a)
        reports = self.handoff(m)
        chosen = m.recovery_proposal(reports)
        self.assertEqual(chosen[0], a[0])
        self.recover(m, reports)
        with self.assertRaises(Rejected):
            m.activate_checkpoint(1, a)

    def test_abort_stops_activation_prepare_and_operation(self):
        m = self.model()
        a = self.proposals(m)
        self.prepare(m, a)
        # witness 2 has not voted to prepare or activate.
        report = m.abort(2, 0, a[0].parent)
        self.assertEqual(report, m.abort(2, 0, a[0].parent))
        with self.assertRaises(Rejected):
            m.activate_checkpoint(2, a)
        with self.assertRaises(Rejected):
            m.vote_checkpoint(2, a)
        t = self.op(m)
        with self.assertRaises(Rejected):
            m.sign(2, t)
        m.vote_checkpoint(0, a)  # cached prepare retry remains valid

    def test_one_phase_install_is_disabled(self):
        m = self.model()
        a = self.proposals(m)
        self.prepare(m, a)
        with self.assertRaises(Rejected):
            m.install_checkpoint(0, a)
        self.activate(m, a)
        m.install_checkpoint(0, a)
        self.assertEqual(m.local[0][0].version, a[0].id)

    def test_late_operation_certificate_across_recovery(self):
        m = self.model()
        t = self.op(m, voters=(0, 3))
        reports = self.handoff(m, witnesses=(0, 1, 3))
        _, chosen = self.recover(m, reports, witnesses=(0, 1, 3))
        self.assertIn(t, chosen[0].charged)
        m.sign(2, t)  # unsealed lagging witness completes old operation certificate
        self.finalize(m, t)
        self.assertEqual(m.snapshot()[0][0], 25)

    def test_triangle_late_effects_and_no_new_capacity(self):
        m = self.model()
        a = self.op(m, 10, (0, 1, 3), nonce=1)
        b = self.op(m, 10, (0, 2, 3), nonce=2)
        c = self.op(m, 10, (1, 2, 3), nonce=3)
        self.finalize(m, c)
        before = set(m.final), deepcopy(m.effects)
        _, chosen = self.recover(m, self.handoff(m))
        self.assertEqual(chosen[0].rights, 0)
        self.assertEqual((m.final, m.effects), before)
        t = self.op(m, 3, nonce=4)
        for v in range(3):
            with self.assertRaises(Rejected):
                m.sign(v, t)
        self.finalize(m, a)
        self.finalize(m, b)
        self.assertEqual(m.snapshot(), [(0, 0), (30, 0)])

    def test_recovery_replay_after_spending(self):
        m = self.model()
        decision, proposal = self.recover(m, self.handoff(m))
        self.op(m, voters=(0, 1, 3))
        before = m.local[0][0].rights
        m.install_recovery(0, decision, proposal)
        self.assertEqual(m.local[0][0].rights, before)

    def test_forged_reports_decisions_and_context(self):
        m = self.model()
        reports = self.handoff(m)
        proposal = m.recovery_proposal(reports)
        for bad in (reports[:2], [reports[0], reports[0], reports[1]],
                    [replace(reports[0], witness=4), *reports[1:]],
                    [replace(reports[0], witness=False), *reports[1:]],
                    [replace(reports[0], genesis='other'), *reports[1:]],
                    [replace(reports[0], prepared='forged'), *reports[1:]]):
            with self.assertRaises(Rejected):
                m.recovery_proposal(bad)
        forged = RecoveryDecision(m.genesis, 0, proposal[0].parent, proposal[0].id)
        with self.assertRaises(Rejected):
            m.install_recovery(0, forged, proposal)
        decision = m.decide_recovery(reports, proposal)
        for bad in (replace(decision, genesis='other'), replace(decision, account=False),
                    replace(decision, instance='other')):
            with self.assertRaises(Rejected):
                m.install_recovery(0, bad, proposal)

    def test_bad_prepare_and_activation_quorums(self):
        m = self.model()
        proposal = self.proposals(m)
        self.activate(m, proposal)
        for bad in ((0, 0, 1), (0, 1, 4), (0, 1, 2), (0, 1, True)):
            with self.assertRaises(Rejected):
                m.activate_checkpoint(2, proposal, bad)
            with self.assertRaises(Rejected):
                m.install_checkpoint(2, proposal, activation_voters=bad)

    def test_abstract_oracle_agreement_is_explicit(self):
        m = self.model()
        a, b = self.split(m)
        reports = self.handoff(m)
        m.decide_recovery(reports, a)
        with self.assertRaisesRegex(Rejected, 'abstract consensus already decided'):
            m.decide_recovery(reports, b)
        # This verifies the oracle contract, not a consensus algorithm.

    def test_overloaded_manifest_keeps_capacity_locked(self):
        m = self.model()
        self.op(m, 20, (0,))
        self.op(m, 20, (1,), nonce=1)
        with self.assertRaisesRegex(Rejected, 'overloaded checkpoint'):
            m.recovery_proposal(self.handoff(m))
        self.assertEqual(m.snapshot()[0][0], 30)

    def test_capped_mint_burn_and_uncapped_recovery(self):
        m = self.model(rights=(10, 0), headroom=(10, 0))
        t = self.op(m, 3, (0, 1, 3), kind='mint', recipient=None)
        self.finalize(m, t)
        reports = self.handoff(m)
        proposal = m.recovery_proposal(reports, receipts=(t,))
        self.recover(m, reports, proposal)
        self.assertEqual((proposal[0].rights, proposal[0].headroom), (13, 7))
        burn = self.op(m, 2, (0, 1, 3), kind='burn', recipient=None)
        # Dependencies must execute locally; already executed mint at all honest v.
        self.finalize(m, burn)
        reports2 = self.handoff(m, parent=proposal[0].id)
        next_proposal = m.recovery_proposal(reports2, receipts=(burn,))
        self.recover(m, reports2, next_proposal)
        self.assertEqual((next_proposal[0].rights, next_proposal[0].headroom), (11, 9))
        uncapped = self.model(headroom=None)
        self.assertIsNone(self.recover(uncapped, self.handoff(uncapped))[1][0].headroom)

    def test_sequential_catchup_and_restart(self):
        m = self.model()
        d1, p1 = self.recover(m, self.handoff(m, witnesses=(0, 1, 3)), witnesses=(0, 1, 3))
        reports = self.handoff(m, parent=p1[0].id, witnesses=(0, 1, 3))
        d2, p2 = self.recover(m, reports, witnesses=(0, 1, 3))
        m = deepcopy(m)  # symbolic durable restart, not a storage adapter
        with self.assertRaises(Rejected):
            m.install_recovery(2, d2, p2)
        m.install_recovery(2, d1, p1)
        m.install_recovery(2, d2, p2)
        self.assertEqual(m.local[2][0].version, p2[0].id)
        with self.assertRaises(Rejected):
            m.install_recovery(2, d1, p1)

    def test_installed_fast_successor_is_carried_on_abort(self):
        m = self.model()
        p = self.proposals(m)
        self.activate(m, p)
        m.install_checkpoint(2, p)  # recipient did not emit its own activation
        report = m.abort(2, 0, p[0].parent)
        self.assertEqual(report.prepared, p[0].id)

    def test_cancellation_and_bare_renewal_disabled(self):
        m = self.model()
        for method in (m.make_version, m.apply_version, m.no_commit_vote, m.recover_no_commit):
            with self.assertRaises(Rejected):
                method()


if __name__ == '__main__':
    unittest.main()
