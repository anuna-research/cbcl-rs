"""SPEC-022 symbolic prototype. No cancellation, cryptography or durable adapter."""
from __future__ import annotations
from dataclasses import dataclass
from model import Model, Local, Version, Rejected, require, digest


@dataclass(frozen=True)
class Report:
    genesis: str
    account: int
    parent: str
    witness: int
    signed: frozenset[str]


@dataclass(frozen=True)
class Checkpoint:
    genesis: str
    account: int
    parent: str
    charged: frozenset[str]
    credited: frozenset[str]
    rights: int
    headroom: int | None

    @property
    def id(self):
        return digest((self.genesis, self.account, self.parent, sorted(self.charged),
                       sorted(self.credited), self.rights, self.headroom))


class SealedModel(Model):
    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        require(not self.mutation, 'mutations unsupported in repaired profile')
        self.genesis = digest(('sealed-budget-v1', self.genesis))
        self.books = {p: (frozenset(), frozenset(), self.r0[a],
                         None if self.h0 is None else self.h0[a])
                      for a, p in enumerate(self.initial_versions)}
        self.journals = {(v, a, node.version): node for v, row in enumerate(self.local)
                         for a, node in enumerate(row)}
        self.reports, self.choices, self.endorsements = set(), {}, {}
        self.checkpoints = {}

    def sign(self, v, tx):
        self._member(v)
        require(tx in self.ops, 'missing payload')
        op = self.ops[tx]
        if v not in self.faulty and v not in self.votes[tx]:
            require(not any(r.witness == v and r.account == op.source and r.parent == op.version
                            for r in self.reports), 'epoch sealed')
        super().sign(v, tx)

    def seal(self, v, account, parent, candidates=None):
        self._member(v)
        self._account(account)
        require(parent in self.books and self.versions[parent].account == account, 'bad parent')
        existing = [r for r in self.reports if (r.witness, r.account, r.parent) == (v, account, parent)]
        if v not in self.faulty:
            if existing:
                return existing[0]
            require(self.local[v][account].version == parent, 'seal inactive epoch')
            signed = frozenset(self.local[v][account].signed)
            require(candidates is None or frozenset(candidates) == signed, 'incomplete honest report')
        else:
            signed = frozenset(candidates or ())
        require(all(t in self.ops and self.ops[t].source == account and self.ops[t].version == parent
                    for t in signed), 'foreign candidate')
        report = Report(self.genesis, account, parent, v, signed)
        self.reports.add(report)  # symbolic authenticated, durable seal precedes publication
        return report

    def propose_checkpoint(self, account, parent, reports, candidates=(), receipts=()):
        require(parent in self.books and self.versions[parent].account == account, 'bad parent')
        reports = tuple(reports)
        require(all(type(r) is Report and type(r.witness) is int and type(r.account) is int
                    and type(r.genesis) is str and type(r.parent) is str
                    and type(r.signed) is frozenset and all(type(t) is str for t in r.signed)
                    for r in reports), 'untyped report')
        require(len({r.witness for r in reports}) == len(reports) and len(reports) >= self.q,
                'bad report quorum')
        require(all(r in self.reports and (r.genesis, r.account, r.parent) ==
                    (self.genesis, account, parent) for r in reports), 'unauthenticated report')
        held = frozenset(candidates).union(*(r.signed for r in reports))
        require(all(t in self.ops and self.ops[t].source == account and self.ops[t].version == parent
                    for t in held), 'foreign candidate')
        charged, credited, _, _ = self.books[parent]
        receipts = frozenset(receipts)
        require(all(t in self.final and any(x > 0 for x in self.delta(self.ops[t], account))
                    for t in receipts), 'unfinalized or unrelated credit')
        charged, credited = charged | held, credited | receipts
        rights = self.r0[account] + sum(max(0, self.delta(self.ops[t], account)[0]) for t in credited)
        rights -= sum(self.cost(self.ops[t])[0] for t in charged)
        headroom = None
        if self.h0 is not None:
            headroom = self.h0[account] + sum(max(0, self.delta(self.ops[t], account)[1]) for t in credited)
            headroom -= sum(self.cost(self.ops[t])[1] for t in charged)
        require(rights >= 0 and (headroom is None or headroom >= 0), 'overloaded checkpoint')
        return Checkpoint(self.genesis, account, parent, charged, credited, rights, headroom), reports

    def validate_checkpoint(self, proposal):
        cp, reports = proposal
        require(type(cp) is Checkpoint and type(cp.account) is int
                and type(cp.rights) is int and (cp.headroom is None or type(cp.headroom) is int)
                and type(cp.genesis) is str and type(cp.parent) is str
                and type(cp.charged) is frozenset and type(cp.credited) is frozenset
                and all(type(t) is str for t in cp.charged | cp.credited), 'untyped checkpoint')
        self._account(cp.account)
        require(cp.genesis == self.genesis and cp.parent in self.books, 'foreign checkpoint')
        old_charged, old_credited, _, _ = self.books[cp.parent]
        require(old_charged <= cp.charged and old_credited <= cp.credited, 'history retraction')
        rebuilt, _ = self.propose_checkpoint(cp.account, cp.parent, reports,
                                             cp.charged - old_charged, cp.credited - old_credited)
        require(rebuilt == cp, 'incorrect checkpoint accounting')
        return cp

    def vote_checkpoint(self, v, proposal):
        self._member(v)
        cp = self.validate_checkpoint(proposal)
        key = (v, cp.account, cp.parent)
        if v not in self.faulty:
            own = [r for r in self.reports if (r.witness, r.account, r.parent) == key]
            require(own and own[0].signed <= cp.charged, 'own seal missing')
            require(key not in self.choices or self.choices[key] == cp.id, 'successor already chosen')
            self.choices[key] = cp.id
        self.endorsements.setdefault(cp.id, set()).add(v)

    def install_checkpoint(self, v, proposal, voters=None):
        self._member(v)
        cp = self.validate_checkpoint(proposal)
        voters = tuple(self.endorsements.get(cp.id, ())) if voters is None else tuple(voters)
        require(len(set(voters)) == len(voters) and len(voters) >= self.q, 'bad checkpoint quorum')
        for witness in voters:
            self._member(witness)
        require(set(voters) <= self.endorsements.get(cp.id, set()), 'forged checkpoint vote')
        node = self.local[v][cp.account]
        if node.version == cp.id:
            return cp.id
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

    def make_version(self, *args, **kwargs):
        raise Rejected('use sealed checkpoints')

    apply_version = make_version
    no_commit_vote = make_version
    recover_no_commit = make_version

    def check(self):
        if not hasattr(self, 'books'):
            return Model.check(self)
        # Diagnostics only; admission never reads global finalized balances.
        for r, h in self.snapshot():
            assert r >= 0 and (h is None or h >= 0), 'negative finalized balance'
        for tx in self.final:
            assert len(self.votes[tx]) >= self.q and len(self.effects[tx]) >= self.q
            assert self.versions[self.ops[tx].version].covered <= self.final
        for (v, account, epoch), node in self.journals.items():
            if v in self.faulty:
                continue
            _, _, r, h = self.books[epoch]
            assert node.rights == self.k*r - self.scale*sum(self.cost(self.ops[t])[0] for t in node.signed)
            assert node.rights >= 0
            if h is not None:
                assert node.headroom == self.k*h - self.scale*sum(self.cost(self.ops[t])[1] for t in node.signed)
                assert node.headroom >= 0
            for report in self.reports:
                if (report.witness, report.account, report.parent) == (v, account, epoch):
                    assert report.signed == node.signed, 'signing after seal'
        for cp in self.checkpoints.values():
            for t, op in self.ops.items():
                if op.source == cp.account and op.version == cp.parent and len(self.votes[t]) >= self.q:
                    assert t in cp.charged, 'late certificate omitted'
