"""SPEC-021 reference model, not a network service or certificate wire format.

KNOWN UNSAFE: BUG-2100 refutes asynchronous safety of partial version renewal.
See async_counterexample.py. This implementation is retained as the regression
subject; its diagnostic check catches a reachable negative finalized balance.

Symbolic authenticated identities, fixed roster, exact scaled integer budgets.
Signatures and persistence are represented by monotonic records. Recovery models
only a no-commit fence + an abstract unique consensus outcome, not consensus.
"""
from __future__ import annotations

from dataclasses import dataclass, field
import hashlib
import json
import os


class Rejected(ValueError):
    pass


def require(condition, reason):
    if not condition:
        raise Rejected(reason)


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


@dataclass(frozen=True)
class Operation:
    genesis: str
    source: int
    version: str
    kind: str
    amount: int
    recipient: int | None = None
    nonce: int = 0

    @property
    def id(self):
        return digest(self.__dict__)


@dataclass(frozen=True)
class Version:
    account: int
    parents: tuple[str, ...]
    covered: frozenset[str]
    mode: str = 'update'

    @property
    def id(self):
        return digest((self.account, self.parents, sorted(self.covered), self.mode))


@dataclass
class Local:
    version: str
    rights: int
    headroom: int | None
    signed: set[str] = field(default_factory=set)
    covered: set[str] = field(default_factory=set)
    released: set[str] = field(default_factory=set)


class Model:
    def __init__(self, rights=(3, 0), headroom=(3, 0), issuers=(0,), f=1,
                 faulty=None, pending_limit=4, mutation=None, floor=0):
        require(type(f) is int and f >= 0 and type(floor) is int and bool(rights)
                and all(type(x) is int and x >= 0 for x in rights), 'bad genesis')
        require(headroom is None or (len(headroom) == len(rights)
                                    and all(type(x) is int and x >= 0 for x in headroom)), 'bad headroom')
        self.floor = floor
        self.f, self.n, self.q = f, 3*f+1, 2*f+1
        self.scale, self.k = self.q, f+1
        self.faulty = set(range(self.n-f, self.n)) if faulty is None else set(faulty)
        require(all(type(v) is int for v in self.faulty) and len(self.faulty) <= f
                and self.faulty <= set(range(self.n)), 'bad faults')
        self.r0, self.h0 = tuple(rights), None if headroom is None else tuple(headroom)
        self.issuers = frozenset(issuers)
        require(all(type(a) is int for a in self.issuers)
                and self.issuers <= set(range(len(rights))), 'bad issuers')
        require(type(pending_limit) is int and pending_limit >= 0, 'bad pending limit')
        self.genesis = digest((rights, headroom, sorted(self.issuers), f, floor))
        self.versions, self.ops, self.votes, self.effects = {}, {}, {}, {}
        self.final, self.cancelled = set(), set()
        self.executed = [set() for _ in range(self.n)]
        self.pending = [set() for _ in range(self.n)]
        self.fences = [set() for _ in range(self.n)]
        self.fence_votes = [set() for _ in range(self.n)]
        self.recovery = {}
        self.limit = pending_limit
        self.mutation = mutation or os.getenv('CBCL_BUDGET_MODEL_MUTATION', '')
        self.initial_versions = []
        for account in range(len(rights)):
            version = Version(account, (), frozenset(), 'genesis')
            self.versions[version.id] = version
            self.initial_versions.append(version.id)
        self.local = [[Local(self.initial_versions[a], self.k * rights[a],
                            None if headroom is None else self.k * headroom[a])
                       for a in range(len(rights))] for _ in range(self.n)]
        self.check()

    def _member(self, v):
        require(type(v) is int and 0 <= v < self.n, 'nonmember witness')

    def _account(self, a):
        require(type(a) is int and 0 <= a < len(self.r0), 'unknown account')

    def propose(self, op, signer):
        require(op.genesis == self.genesis, 'wrong genesis')
        self._account(op.source)
        require(type(signer) is int and signer == op.source, 'wrong owner')
        require(op.version in self.versions and self.versions[op.version].account == op.source,
                'wrong version context')
        require(type(op.amount) is int and op.amount > 0, 'nonpositive amount')
        require(type(op.nonce) is int and op.nonce >= 0, 'invalid nonce')
        require(op.kind in ('mint', 'burn', 'pay', 'headroom'), 'unknown operation')
        if op.kind == 'mint':
            require(op.source in self.issuers, 'not issuer')
        if op.kind in ('pay', 'headroom'):
            self._account(op.recipient)
            require(op.recipient != op.source, 'self transfer')
        else:
            require(op.recipient is None, 'unexpected recipient')
        require(op.kind != 'headroom' or self.h0 is not None, 'no headroom')
        self.ops.setdefault(op.id, op)
        self.votes.setdefault(op.id, set())
        self.effects.setdefault(op.id, set())
        return op.id

    def cost(self, op):
        return (op.amount if op.kind in ('burn', 'pay') else 0,
                op.amount if self.h0 is not None and op.kind in ('mint', 'headroom') else 0)

    def delta(self, op, account):
        r = h = 0
        if account == op.source:
            if op.kind == 'mint':
                r, h = op.amount, -op.amount if self.h0 is not None else 0
            elif op.kind == 'burn':
                r, h = -op.amount, op.amount if self.h0 is not None else 0
            elif op.kind == 'pay':
                r = -op.amount
            else:
                h = -op.amount
        if account == op.recipient:
            if op.kind == 'pay':
                r = op.amount
            elif op.kind == 'headroom':
                h = op.amount
        return r, h

    def sign(self, v, tx):
        self._member(v)
        require(tx in self.ops, 'missing payload')
        op = self.ops[tx]
        local = self.local[v][op.source]
        if v in self.votes[tx]:
            if self.mutation == 'charge-replay' and v not in self.faulty:
                r, h = self.cost(op)
                local.rights -= self.scale*r
                if local.headroom is not None:
                    local.headroom -= self.scale*h
            self.check()
            return
        if v not in self.faulty:
            require(local.version == op.version, 'stale version')
            r, h = self.cost(op)
            require(local.rights >= self.scale*r, 'rights exhausted')
            require(local.headroom is None or local.headroom >= self.scale*h, 'headroom exhausted')
            # Both guards precede either reservation: one operation, one vote.
            local.rights -= self.scale*r
            if local.headroom is not None:
                local.headroom -= self.scale*h
            local.signed.add(tx)
        self.votes[tx].add(v)
        self.check()

    def certificate(self, tx, voters=None):
        require(tx in self.ops, 'missing payload')
        voters = tuple(sorted(self.votes[tx])) if voters is None else tuple(voters)
        require(len(voters) == len(set(voters)), 'duplicate witness')
        for v in voters:
            self._member(v)
        require(len(voters) >= self.q, 'insufficient signatures')
        require(set(voters) <= self.votes[tx], 'forged witness signature')
        return voters

    def _ready(self, v, tx):
        return self.versions[self.ops[tx].version].covered <= self.executed[v]

    def _execute(self, v, tx):
        if tx in self.executed[v]:
            return
        op = self.ops[tx]
        if v not in self.faulty and self.mutation != 'ignore-fence':
            require((op.source, op.version) not in self.fences[v], 'execution fenced')
        self.executed[v].add(tx)
        self.effects[tx].add(v)  # irreversible signed evidence, even after local rollback
        threshold = 1 if self.mutation == 'early-finality' else self.q
        if len(self.effects[tx]) >= threshold:
            assert tx not in self.cancelled, 'cancelled transaction obtained final effects'
            self.final.add(tx)

    def receive(self, v, tx, voters=None):
        self._member(v)
        self.certificate(tx, voters)
        if not self._ready(v, tx):
            require(tx in self.pending[v] or len(self.pending[v]) < self.limit, 'pending backpressure')
            self.pending[v].add(tx)
            return False
        # A ready dependency bypasses pending-buffer capacity.
        self._execute(v, tx)
        progress = True
        while progress:
            progress = False
            for child in sorted(self.pending[v]):
                if self._ready(v, child):
                    op = self.ops[child]
                    if v not in self.faulty and (op.source, op.version) in self.fences[v]:
                        continue
                    self._execute(v, child)
                    self.pending[v].remove(child)
                    progress = True
        self.check()
        return True

    def make_version(self, account, parents, included=(), signer=None):
        self._account(account)
        require(type(signer) is int and signer == account, 'wrong version owner')
        parents = tuple(sorted(parents))
        require(parents and len(parents) == len(set(parents)), 'invalid parents')
        require(all(p in self.versions and self.versions[p].account == account for p in parents),
                'foreign version parent')
        covered = set().union(*(self.versions[p].covered for p in parents))
        for tx in included:
            require(tx in self.final, 'unfinalized funding')
            require(self.delta(self.ops[tx], account) != (0, 0), 'unrelated receipt')
            covered.add(tx)
        version = Version(account, parents, frozenset(covered))
        self.versions.setdefault(version.id, version)
        return version.id

    def apply_version(self, v, version_id):
        self._member(v)
        require(version_id in self.versions, 'unknown version')
        version = self.versions[version_id]
        local = self.local[v][version.account]
        if local.version == version_id:
            return
        require(local.version in version.parents, 'version does not extend current state')
        require(local.covered <= version.covered, 'history retraction')
        new = version.covered - local.covered
        for tx in new:
            dr, dh = self.delta(self.ops[tx], version.account)
            r, h = self.cost(self.ops[tx]) if tx in local.signed - local.released else (0, 0)
            local.rights += self.k*dr + self.scale*r
            if local.headroom is not None:
                local.headroom += self.k*dh + self.scale*h
        local.covered.update(new)
        local.version = version_id
        if self.mutation == 'forget-omitted':
            r, h = self.recognized_balance(local.covered, version.account)
            local.rights = self.k*r
            if local.headroom is not None:
                local.headroom = self.k*h
        self.check()

    def recognized_balance(self, covered, account):
        r = self.r0[account]
        h = None if self.h0 is None else self.h0[account]
        for tx in covered:
            dr, dh = self.delta(self.ops[tx], account)
            r += dr
            if h is not None:
                h += dh
        return r, h

    def no_commit_vote(self, v, account, version_id):
        self._member(v)
        self._account(account)
        require(version_id in self.versions and self.versions[version_id].account == account,
                'wrong fence context')
        if v not in self.faulty:
            require(not any(v in self.effects[t] and self.ops[t].source == account
                            and self.ops[t].version == version_id for t in self.ops),
                    'already emitted effects')
        self.fences[v].add((account, version_id))
        self.fence_votes[v].add((account, version_id))
        self.check()

    def recover_no_commit(self, account, version_id, voters):
        # Abstract unique consensus result, NOT an implementation of consensus.
        self._account(account)
        voters = tuple(voters)
        require(len(voters) == len(set(voters)) and len(voters) >= self.q, 'bad fence quorum')
        for v in voters:
            self._member(v)
            require((account, version_id) in self.fence_votes[v], 'forged fence vote')
        if version_id in self.recovery:
            return self.recovery[version_id]
        old = self.versions[version_id]
        require(old.account == account, 'wrong recovery account')
        doomed = {t for t, op in self.ops.items() if op.source == account and op.version == version_id}
        assert not doomed & self.final, 'no-commit quorum conflicts with a finalized receipt'
        self.cancelled.update(doomed)
        version = Version(account, (version_id,), old.covered, 'recovery')
        self.versions.setdefault(version.id, version)
        self.recovery[version_id] = version.id
        # Deliver the abstract consensus result to all witnesses in this reference action.
        for v in range(self.n):
            self.fences[v].add((account, version_id))
            self.executed[v].difference_update(doomed)  # effects signatures are NOT erased
            self.pending[v].difference_update(doomed)
            local = self.local[v][account]
            if local.version != version_id:
                continue
            release = (local.signed & doomed) - local.covered - local.released
            for tx in release:
                r, h = self.cost(self.ops[tx])
                local.rights += self.scale*r
                if local.headroom is not None:
                    local.headroom += self.scale*h
            local.released.update(release)
            local.version = version.id
        self.check()
        return version.id

    def snapshot(self):
        return [self.recognized_balance(self.final, a) for a in range(len(self.r0))]

    @property
    def value(self):
        return self.floor + sum(r for r, _ in self.snapshot())

    @property
    def ceiling(self):
        return None if self.h0 is None else self.floor + sum(self.r0) + sum(self.h0)

    def check(self):
        # Independent diagnostic assertions; these do not gate signing by global balances.
        for tx in self.final:
            assert len(self.votes[tx]) >= self.q and len(self.effects[tx]) >= self.q
            assert tx not in self.cancelled
            assert self.versions[self.ops[tx].version].covered <= self.final
        for r, h in self.snapshot():
            assert r >= 0, 'negative finalized rights'
            assert h is None or h >= 0, 'negative finalized headroom'
        if self.h0 is not None:
            assert sum(r+h for r, h in self.snapshot()) == sum(self.r0)+sum(self.h0)
        for v in range(self.n):
            if v in self.faulty:
                continue
            for account, version in self.fence_votes[v]:
                assert not any(v in self.effects[t] and self.ops[t].source == account
                               and self.ops[t].version == version for t in self.ops), 'effects after no-commit vote'
            for a, local in enumerate(self.local[v]):
                assert local.covered == set(self.versions[local.version].covered)
                r, h = self.recognized_balance(local.covered, a)
                pending = local.signed - local.covered - local.released
                assert local.rights == self.k*r - self.scale*sum(self.cost(self.ops[t])[0] for t in pending)
                if h is not None:
                    assert local.headroom == self.k*h - self.scale*sum(self.cost(self.ops[t])[1] for t in pending)
                for tx in local.released:
                    assert tx in self.cancelled and tx not in self.final
