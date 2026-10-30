"""SPEC-022 TEST-2200: seals, delayed certificates, cumulative books."""
import unittest
from dataclasses import replace
from model import Operation, Rejected
from sealed_model import SealedModel


class SealedTests(unittest.TestCase):
    def model(self, rights=(30, 0), headroom=(0, 0)):
        return SealedModel(rights=rights, headroom=headroom)

    def op(self, m, amount, voters, kind='pay', source=0, recipient=1, nonce=0):
        t = m.propose(Operation(m.genesis, source, m.local[0][source].version,
                                kind, amount, recipient, nonce), source)
        for v in voters:
            m.sign(v, t)
        return t

    def close(self, m, account=0, receipts=(), candidates=(), witnesses=(0, 1, 2)):
        parent = m.local[0][account].version
        reports = [m.seal(v, account, parent) for v in witnesses]
        proposal = m.propose_checkpoint(account, parent, reports, candidates, receipts)
        for v in witnesses:
            m.vote_checkpoint(v, proposal)
        for v in range(m.n):
            m.install_checkpoint(v, proposal)
        return proposal

    def finalize(self, m, t):
        for v in (0, 1, 2):
            m.receive(v, t)

    def test_delayed_triangle_carries_all_costs(self):
        m = self.model()
        a = self.op(m, 10, (0, 1, 3), nonce=1)
        b = self.op(m, 10, (0, 2, 3), nonce=2)
        c = self.op(m, 10, (1, 2, 3), nonce=3)
        self.finalize(m, c)
        cp, _ = self.close(m)
        self.assertEqual(cp.charged, {a, b, c})
        self.assertEqual(cp.rights, 0)
        d = self.op(m, 3, (3,), nonce=4)
        for v in range(3):
            with self.assertRaises(Rejected):
                m.sign(v, d)
        self.finalize(m, a)
        self.finalize(m, b)
        self.assertEqual(m.snapshot(), [(0, 0), (30, 0)])

    def test_future_old_certificate_is_carried(self):
        m = self.model()
        t = self.op(m, 5, (0, 3))
        parent = m.initial_versions[0]
        reports = [m.seal(v, 0, parent) for v in (0, 1, 3)]
        proposal = m.propose_checkpoint(0, parent, reports)
        for v in (0, 1, 3):
            m.vote_checkpoint(v, proposal)
        for v in (0, 1, 3):
            m.install_checkpoint(v, proposal)
        m.sign(2, t)  # unsealed, lagging witness completes the old certificate
        self.finalize(m, t)
        self.assertIn(t, proposal[0].charged)
        self.assertEqual(m.snapshot()[0][0], 25)

    def test_seal_blocks_fresh_votes_but_allows_retry(self):
        m = self.model()
        t = self.op(m, 5, (0,))
        m.seal(0, 0, m.initial_versions[0])
        m.sign(0, t)
        other = self.op(m, 5, (), nonce=1)
        with self.assertRaises(Rejected):
            m.sign(0, other)

    def test_checkpoint_replay_does_not_reset_spending(self):
        m = self.model()
        proposal = self.close(m)
        t = self.op(m, 5, (0, 1, 3))
        before = m.local[0][0].rights
        m.install_checkpoint(0, proposal)
        self.assertEqual(m.local[0][0].rights, before)
        self.assertIn(t, m.local[0][0].signed)

    def test_forged_books_and_reports_rejected(self):
        m = self.model()
        reports = [m.seal(v, 0, m.initial_versions[0]) for v in range(3)]
        cp, sidecar = m.propose_checkpoint(0, m.initial_versions[0], reports)
        for fields in ({'rights': 31}, {'rights': 30.0}, {'headroom': False}, {'account': False}):
            with self.assertRaises(Rejected):
                m.vote_checkpoint(0, (replace(cp, **fields), sidecar))
        with self.assertRaises(Rejected):
            m.propose_checkpoint(0, cp.parent, [replace(reports[0], witness=3), *reports[1:]])
        with self.assertRaises(Rejected):
            m.propose_checkpoint(0, cp.parent, [reports[0], replace(reports[1], witness=True), reports[2]])

    def test_vote_once_and_own_report_required(self):
        m = self.model()
        t = self.op(m, 5, (0,))
        parent = m.initial_versions[0]
        reports = [m.seal(v, 0, parent) for v in (1, 2, 3)]
        empty = m.propose_checkpoint(0, parent, reports)
        m.seal(0, 0, parent)
        with self.assertRaises(Rejected):
            m.vote_checkpoint(0, empty)
        full = m.propose_checkpoint(0, parent, reports, (t,))
        m.vote_checkpoint(1, empty)
        with self.assertRaises(Rejected):
            m.vote_checkpoint(1, full)

    def test_credit_once_mint_burn_and_recipient(self):
        m = self.model(rights=(10, 0), headroom=(10, 0))
        mint = self.op(m, 3, (0, 1, 3), 'mint', recipient=None)
        self.finalize(m, mint)
        cp, _ = self.close(m, receipts=(mint,))
        self.assertEqual((cp.rights, cp.headroom), (13, 7))
        cp2, _ = self.close(m, receipts=(mint,))
        self.assertEqual((cp2.rights, cp2.headroom), (13, 7))
        burn = self.op(m, 2, (0, 1, 3), 'burn', recipient=None)
        self.finalize(m, burn)
        cp3, _ = self.close(m, receipts=(burn,))
        self.assertEqual((cp3.rights, cp3.headroom), (11, 9))
        pay = self.op(m, 4, (0, 1, 3))
        self.finalize(m, pay)
        recipient, _ = self.close(m, account=1, receipts=(pay,))
        self.assertEqual(recipient.rights, 4)

    def test_overloaded_candidates_and_speculative_credit(self):
        m = self.model()
        a = self.op(m, 20, (0,))
        b = self.op(m, 20, (1,), nonce=1)
        reports = [m.seal(v, 0, m.initial_versions[0]) for v in range(3)]
        with self.assertRaises(Rejected):
            m.propose_checkpoint(0, m.initial_versions[0], reports)
        with self.assertRaises(Rejected):
            m.propose_checkpoint(1, m.initial_versions[1],
                [m.seal(v, 1, m.initial_versions[1]) for v in range(3)], receipts=(a,))

    def test_omitted_report_and_invalid_endorsements(self):
        m = self.model()
        t = self.op(m, 5, (0, 1, 3))
        reports = [m.seal(v, 0, m.initial_versions[0]) for v in range(3)]
        cp, sidecar = m.propose_checkpoint(0, m.initial_versions[0], reports)
        with self.assertRaises(Rejected):
            m.vote_checkpoint(2, (replace(cp, charged=frozenset(), rights=30), sidecar))
        for v in range(3):
            m.vote_checkpoint(v, (cp, sidecar))
        for voters in ((0, 0, 1), (0, 1, 4), (0, 1, 3)):
            with self.assertRaises(Rejected):
                m.install_checkpoint(0, (cp, sidecar), voters)

    def test_headroom_transfer_and_uncapped(self):
        m = self.model(rights=(0, 0), headroom=(12, 0))
        t = self.op(m, 4, (0, 1, 3), 'headroom')
        self.finalize(m, t)
        source, _ = self.close(m)
        target, _ = self.close(m, account=1, receipts=(t,))
        self.assertEqual((source.headroom, target.headroom), (8, 4))
        uncapped = self.model(headroom=None)
        self.assertIsNone(self.close(uncapped)[0].headroom)

    def test_sequential_lagging_installation(self):
        m = self.model()
        parent = m.initial_versions[0]
        proposals = []
        for _ in range(2):
            reports = [m.seal(v, 0, parent) for v in (0, 1, 3)]
            proposal = m.propose_checkpoint(0, parent, reports)
            for v in (0, 1, 3):
                m.vote_checkpoint(v, proposal)
            for v in (0, 1, 3):
                m.install_checkpoint(v, proposal)
            proposals.append(proposal)
            parent = proposal[0].id
        with self.assertRaises(Rejected):
            m.install_checkpoint(2, proposals[1])
        m.install_checkpoint(2, proposals[0])
        m.install_checkpoint(2, proposals[1])
        self.assertEqual(m.local[2][0].version, parent)

    def test_unsafe_paths_disabled(self):
        m = self.model()
        for method in (m.make_version, m.apply_version, m.no_commit_vote, m.recover_no_commit):
            with self.assertRaises(Rejected):
                method()


if __name__ == '__main__':
    unittest.main()
