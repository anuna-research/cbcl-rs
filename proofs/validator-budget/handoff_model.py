"""SPEC-023 abortable handoff experiment; consensus is an explicit trusted oracle.

Historical research only: not selected for the consensus-free design (SPEC-025).
This is a separate profile, not an implementation of Abstract or network BFT.
No cancellation: old operation certificates remain valid after switching.
"""
from __future__ import annotations
from dataclasses import dataclass
from model import Local, Version, require, digest
from sealed_model import SealedModel, Report


@dataclass(frozen=True)
class AbortReport:
    genesis: str
    account: int
    parent: str
    witness: int
    signed: frozenset[str]
    prepared: str | None


@dataclass(frozen=True)
class RecoveryDecision:
    genesis: str
    account: int
    parent: str
    checkpoint: str
    instance: str = 'recovery-1'


class HandoffModel(SealedModel):
    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        self.genesis = digest(('abortable-handoff-v1', self.genesis))
        self.stopped = set()
        self.known_prepared = {}
        self.prepared_proofs = {}
        self.activations = {}
        self.abort_reports = set()
        self.decisions = {}

    def _quorum(self, supplied, actual):
        voters = tuple(actual) if supplied is None else tuple(supplied)
        for v in voters:
            self._member(v)
        require(len(set(voters)) == len(voters) and len(voters) >= self.q, 'bad quorum')
        require(set(voters) <= actual, 'forged quorum signature')
        return voters

    def _prepare_certificate(self, proposal, voters=None):
        cp = self.validate_checkpoint(proposal)
        self._quorum(voters, self.endorsements.get(cp.id, set()))
        return cp

    def _remember_prepared(self, v, proposal):
        cp = self._prepare_certificate(proposal)
        self.prepared_proofs[cp.id] = proposal
        key = (v, cp.account, cp.parent)
        if v not in self.faulty:
            require(key not in self.known_prepared or self.known_prepared[key] == cp.id,
                    'conflicting prepare evidence')
        self.known_prepared[key] = cp.id
        return cp

    def vote_checkpoint(self, v, proposal):
        self._member(v)
        cp = self.validate_checkpoint(proposal)
        key = (v, cp.account, cp.parent)
        if v not in self.faulty:
            # Cached old signatures remain relayable after stopping.
            if v in self.endorsements.get(cp.id, set()):
                return
            require(key not in self.stopped, 'checkpoint preparation stopped')
        super().vote_checkpoint(v, proposal)

    def activate_checkpoint(self, v, proposal, prepare_voters=None):
        self._member(v)
        cp = self._prepare_certificate(proposal, prepare_voters)
        key = (v, cp.account, cp.parent)
        if v in self.activations.get(cp.id, set()):
            return
        if v not in self.faulty:
            require(key not in self.stopped, 'checkpoint activation stopped')
            self.seal(v, cp.account, cp.parent)
        self._remember_prepared(v, proposal)  # evidence before activation signature
        self.activations.setdefault(cp.id, set()).add(v)

    def _install(self, v, cp):
        node = self.local[v][cp.account]
        if node.version == cp.id:
            return cp.id  # never reset a used journal
        require(node.version == cp.parent, 'checkpoint does not extend active epoch')
        self.checkpoints[cp.id] = cp
        self.books[cp.id] = (cp.charged, cp.credited, cp.rights, cp.headroom)
        self.versions[cp.id] = Version(cp.account, (cp.parent,), cp.credited, 'sealed')
        fresh = Local(cp.id, self.k*cp.rights,
                      None if cp.headroom is None else self.k*cp.headroom,
                      covered=set(cp.credited))
        self.local[v][cp.account] = fresh
        self.journals[v, cp.account, cp.id] = fresh
        self.check()
        return cp.id

    def install_checkpoint(self, v, proposal, voters=None, activation_voters=None):
        self._member(v)
        cp = self._prepare_certificate(proposal, voters)
        self._quorum(activation_voters, self.activations.get(cp.id, set()))
        # Delivery alone is sufficient evidence to preserve this successor on abort.
        self._remember_prepared(v, proposal)
        return self._install(v, cp)

    def abort(self, v, account, parent, candidates=None, prepared=None):
        self._member(v)
        self._account(account)
        require(type(parent) is str and parent in self.books
                and self.versions[parent].account == account, 'bad abort parent')
        existing = [r for r in self.abort_reports if
                    (r.witness, r.account, r.parent) == (v, account, parent)]
        if v not in self.faulty and existing:
            return existing[0]
        key = (v, account, parent)
        if v not in self.faulty:
            require(key in self.journals, 'uninstalled epoch')
            signed = frozenset(self.journals[key].signed)
            require(candidates is None or frozenset(candidates) == signed, 'incomplete abort journal')
            evidence = self.known_prepared.get(key)
            require(prepared is None or prepared == evidence, 'incorrect abort prepare evidence')
            self.stopped.add(key)
            # Also seal a historic epoch when this witness installed before aborting.
            self.reports.add(Report(self.genesis, account, parent, v, signed))
        else:
            signed = frozenset(candidates or ())
            evidence = prepared
            require(evidence is None or (evidence in self.prepared_proofs
                    and self.prepared_proofs[evidence][0].account == account
                    and self.prepared_proofs[evidence][0].parent == parent), 'forged prepare evidence')
            require(all(t in self.ops and self.ops[t].source == account
                        and self.ops[t].version == parent for t in signed), 'foreign candidate')
            self.reports.add(Report(self.genesis, account, parent, v, signed))
        report = AbortReport(self.genesis, account, parent, v, signed, evidence)
        self.abort_reports.add(report)
        return report

    def validate_handoff(self, reports):
        reports = tuple(reports)
        require(all(type(r) is AbortReport and type(r.genesis) is str
                    and type(r.account) is int and type(r.parent) is str
                    and type(r.witness) is int and type(r.signed) is frozenset
                    and all(type(t) is str for t in r.signed)
                    and (r.prepared is None or type(r.prepared) is str)
                    for r in reports), 'untyped abort report')
        require(len(reports) >= self.q and len({r.witness for r in reports}) == len(reports),
                'bad abort quorum')
        first = reports[0]
        for r in reports:
            self._member(r.witness)
            require(r in self.abort_reports and (r.genesis, r.account, r.parent) ==
                    (self.genesis, first.account, first.parent), 'unauthenticated abort report')
        pinned = {r.prepared for r in reports if r.prepared is not None}
        require(len(pinned) <= 1, 'conflicting prepare certificates')
        if pinned:
            proposal = self.prepared_proofs[next(iter(pinned))]
            cp = self._prepare_certificate(proposal)
            require((cp.account, cp.parent) == (first.account, first.parent), 'foreign prepare evidence')
        return reports, next(iter(pinned)) if pinned else None

    def recovery_proposal(self, reports, candidates=(), receipts=()):
        reports, pinned = self.validate_handoff(reports)
        if pinned is not None:
            return self.prepared_proofs[pinned]
        r = reports[0]
        seals = [Report(a.genesis, a.account, a.parent, a.witness, a.signed) for a in reports]
        return self.propose_checkpoint(r.account, r.parent, seals, candidates, receipts)

    def decide_recovery(self, reports, proposal):
        """SIMPLIFY SPEC-023 CON-2300: trusted one-shot consensus, not BFT code.

        Agreement is assumed here; all proposal-validity checks below are real.
        No timeout or validator can manufacture the resulting authenticated token.
        """
        reports, pinned = self.validate_handoff(reports)
        cp = self.validate_checkpoint(proposal)
        first = reports[0]
        require((cp.account, cp.parent) == (first.account, first.parent), 'wrong recovery context')
        if pinned is not None:
            require(cp.id == pinned, 'recovery must preserve prepared checkpoint')
        else:
            held = frozenset().union(*(r.signed for r in reports))
            require(held <= cp.charged, 'handoff obligations omitted')
        key = (cp.account, cp.parent)
        decision = RecoveryDecision(self.genesis, cp.account, cp.parent, cp.id)
        require(key not in self.decisions or self.decisions[key] == decision,
                'abstract consensus already decided')
        self.decisions[key] = decision
        return decision

    def install_recovery(self, v, decision, proposal):
        self._member(v)
        require(type(decision) is RecoveryDecision and type(decision.genesis) is str
                and type(decision.account) is int and type(decision.parent) is str
                and type(decision.checkpoint) is str and decision.instance == 'recovery-1',
                'untyped decision')
        cp = self.validate_checkpoint(proposal)
        require(decision.genesis == self.genesis and
                (decision.account, decision.parent, decision.checkpoint) ==
                (cp.account, cp.parent, cp.id) and
                self.decisions.get((cp.account, cp.parent)) == decision, 'unauthenticated decision')
        return self._install(v, cp)
