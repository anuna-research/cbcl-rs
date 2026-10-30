//! SPEC-030: real runtime vs Lean reference, plus wire/durability boundaries.
use super::*;
use serde_json::{json, Value as Json};

fn dag() -> Net {
    dag_source(&TICKETS.replace("(floor 0)", "(floor 0) (ceiling 200)"))
}
fn dag_source(source: &str) -> Net {
    dag_supply(source, 100)
}
fn dag_supply(source: &str, supply: i64) -> Net {
    let mut n = collective_source(source);
    n.base[1]=act(&format!("(signed @treasury (lang {} (open (@alice @bob @treasury) :available {supply} :from @treasury :thread \"coin-1\" :caused-by {})))",n.d.name,n.base[0].address),"@treasury");
    n.auth
        .acts
        .insert((n.base[1].address.clone(), n.base[1].signer.clone()));
    let inst = Instance::new(&n.d, ThreadId("coin-1".into()), &n.base).unwrap();
    n.ctx = Context::from_instance_multi_parent(&inst, "tickets", None, &n.auth).unwrap();
    n.j = Memory::default();
    n.rs = (0..4)
        .map(|w| {
            Replica::initialize(
                n.ctx.clone(),
                &format!("@v{w}"),
                Limits::default(),
                &mut n.j,
            )
            .unwrap()
        })
        .collect();
    n
}
fn indices(v: &Json) -> Vec<usize> {
    v.as_array()
        .unwrap()
        .iter()
        .map(|x| x.as_u64().unwrap() as usize)
        .collect()
}
fn set(xs: impl IntoIterator<Item = String>) -> BTreeSet<String> {
    xs.into_iter().collect()
}

struct OracleNet {
    n: Net,
    ids: Vec<String>,
    versions: Vec<Option<DagVersion>>,
    acts: Vec<Option<Act>>,
    votes: BTreeMap<(VoteKind, usize, usize), Vote>,
}
impl OracleNet {
    fn new(c: &Json) -> Self {
        let n = dag();
        let mut x = Self {
            ids: vec![n.ctx.root_epoch(COLLECTIVE_POOL).unwrap()],
            versions: vec![None],
            acts: vec![None; c["amount"].as_array().unwrap().len()],
            votes: BTreeMap::new(),
            n,
        };
        x.make_acts(c, 0);
        for v in c["versions"].as_array().unwrap() {
            let id = v["id"].as_u64().unwrap() as usize;
            assert_eq!(id, x.ids.len());
            let txs = |name: &str| {
                set(indices(&v[name])
                    .iter()
                    .map(|i| x.acts[*i].as_ref().unwrap().address.clone()))
            };
            let m = VersionManifest {
                account: COLLECTIVE_POOL.into(),
                parents: set(indices(&v["parents"]).iter().map(|i| x.ids[*i].clone())),
                rank: v["rank"].as_u64().unwrap(),
                held: txs("held"),
                refunded: txs("refunded"),
                credited: txs("credited"),
                allocation: Resources {
                    rights: v["allocation"][0].as_i64().unwrap().into(),
                    headroom: v["allocation"][1].as_i64().unwrap().into(),
                },
            };
            let authorization = sign(x.n.ctx.version_request(&m, "@alice").unwrap());
            x.ids.push(m.id(x.n.ctx.id()));
            x.versions.push(Some(DagVersion {
                manifest: m,
                authorization,
            }));
            x.make_acts(c, id);
        }
        x
    }
    fn make_acts(&mut self, c: &Json, v: usize) {
        for (tx, epoch) in indices(&c["opVersion"]).iter().enumerate() {
            if *epoch != v {
                continue;
            }
            let mint = c["mint"][tx].as_bool().unwrap();
            let actor = if mint { "@treasury" } else { "@alice" };
            let verb = if mint { "restock" } else { "sell" };
            let buyer = if mint { "" } else { " :buyer @customer" };
            let credits = self.versions[v]
                .as_ref()
                .map(|m| {
                    m.manifest
                        .credited
                        .iter()
                        .cloned()
                        .collect::<Vec<_>>()
                        .join(" ")
                })
                .unwrap_or_default();
            let a = act(&format!("(signed {actor} (lang {} ({verb} (@alice @bob @treasury) (){buyer} :amount {} :escrow-prev {} :escrow-deps ({credits}) :escrow-nonce \"oracle-{tx}\" :from {actor} :thread \"coin-1\" :caused-by {})))",
                self.n.d.name, c["amount"][tx], self.ids[v], self.n.base[1].address), actor);
            self.n.auth.acts.insert((a.address.clone(), actor.into()));
            self.acts[tx] = Some(a);
        }
    }
    fn register_tx(&mut self, tx: usize) {
        let a = self.acts[tx].as_ref().unwrap();
        for r in &mut self.n.rs {
            // Candidate registration is abstract stuttering; absent source metadata
            // remains absent and the following core command must then reject.
            if r.operation_act(&a.address).is_none() {
                let _ = r.register(a.clone(), &mut self.n.j, &self.n.auth);
            }
        }
    }
    fn vote(&mut self, kind: VoteKind, tx: usize, w: usize, vote: Vote) {
        self.votes.insert((kind, tx, w), vote);
        let votes: Vec<_> = self
            .votes
            .iter()
            .filter(|((k, t, _), _)| *k == kind && *t == tx)
            .map(|(_, v)| v.clone())
            .collect();
        let id = &self.acts[tx].as_ref().unwrap().address;
        if votes.len() >= 3 {
            let c = Certificate {
                kind,
                payload: id.clone(),
                votes,
            };
            for r in &mut self.n.rs {
                r.receive(c.clone(), &mut self.n.j, &self.n.auth).unwrap();
            }
        }
    }
    fn command(&mut self, cmd: &Json) -> bool {
        let op = cmd[0].as_str().unwrap();
        let id = cmd[1].as_u64().unwrap() as usize;
        let w = cmd[2].as_u64().unwrap() as usize;
        if op == "record" {
            let v = self.versions[id].as_ref().unwrap().clone();
            let wanted: Vec<_> = self
                .acts
                .iter()
                .enumerate()
                .filter(|(_, a)| {
                    a.as_ref().is_some_and(|a| {
                        v.manifest.held.contains(&a.address)
                            || v.manifest.credited.contains(&a.address)
                    })
                })
                .map(|(i, _)| i)
                .collect();
            for tx in wanted {
                self.register_tx(tx);
            }
            let before: Vec<_> = self.n.rs.iter().map(Replica::journal_sequence).collect();
            let outcomes: Vec<_> = self
                .n
                .rs
                .iter_mut()
                .map(|r| {
                    r.receive_version(v.clone(), &mut self.n.j, &self.n.auth)
                        .is_ok()
                })
                .collect();
            assert!(outcomes.iter().all(|o| *o == outcomes[0]));
            if !outcomes[0] {
                assert_eq!(
                    before,
                    self.n
                        .rs
                        .iter()
                        .map(Replica::journal_sequence)
                        .collect::<Vec<_>>()
                );
            }
            return outcomes[0];
        }
        if op == "adopt" {
            let before = self.n.rs[w].journal_sequence();
            let result = self.n.rs[w]
                .adopt_version(&self.ids[id], &mut self.n.j, &self.n.auth)
                .is_ok();
            if !result {
                assert_eq!(before, self.n.rs[w].journal_sequence());
            }
            return result;
        }
        if op == "replay" {
            return true;
        }
        self.register_tx(id);
        let tx = &self.acts[id].as_ref().unwrap().address;
        let kind = match op {
            "sign" => VoteKind::Operation,
            "effect" => VoteKind::Effects,
            "fence" => VoteKind::Cancel,
            "release" => {
                let before = self.n.rs[w].journal_sequence();
                let result = self.n.rs[w]
                    .release(tx, &mut self.n.j, &self.n.auth)
                    .is_ok();
                if !result {
                    assert_eq!(before, self.n.rs[w].journal_sequence());
                }
                return result;
            }
            _ => panic!("unknown command {op}"),
        };
        // Validator3 is the modeled Byzantine participant. Its external signer
        // can emit arbitrary votes; no honest Replica API is weakened for it.
        if w == 3 {
            let mut vote = Vote {
                context: self.n.ctx.id().into(),
                kind,
                payload: tx.clone(),
                signer: "@v3".into(),
                signature: vec![],
            };
            vote.signature = signature(&vote.signer, &vote.preimage());
            self.vote(kind, id, w, vote);
            return true;
        }
        let before = self.n.rs[w].journal_sequence();
        let result = match kind {
            VoteKind::Operation => self.n.rs[w].prepare_operation(tx, &mut self.n.j, &self.n.auth),
            VoteKind::Effects => self.n.rs[w].prepare_effects(tx, &mut self.n.j, &self.n.auth),
            VoteKind::Cancel => {
                let request = sign(
                    self.n
                        .ctx
                        .cancellation_request(&self.acts[id].as_ref().unwrap().signer, tx)
                        .unwrap(),
                );
                self.n.rs[w].prepare_cancel(request, &mut self.n.j, &self.n.auth)
            }
            _ => unreachable!(),
        };
        match result {
            Ok(request) => {
                self.vote(kind, id, w, sign(request));
                true
            }
            Err(_) => {
                assert_eq!(before, self.n.rs[w].journal_sequence());
                false
            }
        }
    }
    fn project(&self, xs: &BTreeSet<String>, table: &[String]) -> Vec<usize> {
        let mut ids: Vec<_> = xs
            .iter()
            .map(|id| table.iter().position(|x| x == id).unwrap())
            .collect();
        ids.sort();
        ids
    }
    fn snapshot(&self) -> Json {
        let txs: Vec<_> = self
            .acts
            .iter()
            .map(|a| a.as_ref().unwrap().address.clone())
            .collect();
        let nodes: Vec<_> = self.n.rs.iter().take(3).map(|r| {
            let s = r.version_snapshot().unwrap();
            json!({"active":self.ids.iter().position(|x|x==&s.active).unwrap(),
                "visited":self.project(&s.visited,&self.ids),"known":self.project(&s.known,&self.ids),
                "signed":self.project(&s.signed,&txs),"released":self.project(&s.released,&txs),
                "effects":self.project(&s.effects,&txs),"fences":self.project(&s.fences,&txs)})
        }).collect();
        let certified = |kind| {
            (0..txs.len())
                .filter(|i| self.n.rs[0].certificate(kind, &txs[*i]).is_some())
                .collect::<Vec<_>>()
        };
        let view = self.n.rs[0].finalized_view().unwrap();
        json!({"nodes":nodes,"operation":certified(VoteKind::Operation),"final":certified(VoteKind::Effects),
            "cancel":certified(VoteKind::Cancel),"balance":[view.rights[COLLECTIVE_POOL],view.headroom.unwrap()[COLLECTIVE_POOL]]})
    }
}

#[test]
fn lean_shared_transition_traces() {
    let reference: Json = serde_json::from_str(include_str!(
        "../../../../test-vectors/quorum/multi-parent-lean.json"
    ))
    .unwrap();
    for trace in reference["traces"].as_array().unwrap() {
        let mut runtime = OracleNet::new(&reference["catalogue"]);
        for (index, step) in trace["steps"].as_array().unwrap().iter().enumerate() {
            let accepted = runtime.command(&step["command"]);
            assert_eq!(
                accepted,
                step["accepted"].as_bool().unwrap(),
                "trace {} step {index}: {}",
                trace["name"],
                step["command"]
            );
            assert_eq!(
                runtime.snapshot(),
                step["state"],
                "trace {} step {index}: {}",
                trace["name"],
                step["command"]
            );
            // Recovery is the same executable machine after every accepted/rejected command.
            for w in 0..3 {
                let recovered = Replica::recover(
                    runtime.n.ctx.clone(),
                    &format!("@v{w}"),
                    Limits::default(),
                    &runtime.n.j,
                    &runtime.n.auth,
                )
                .unwrap();
                assert_eq!(
                    recovered.version_snapshot().unwrap(),
                    runtime.n.rs[w].version_snapshot().unwrap()
                );
                assert_eq!(
                    recovered.finalized_view().unwrap(),
                    runtime.n.rs[w].finalized_view().unwrap()
                );
            }
        }
    }
}

fn oracle() -> OracleNet {
    let reference: Json = serde_json::from_str(include_str!(
        "../../../../test-vectors/quorum/multi-parent-lean.json"
    ))
    .unwrap();
    OracleNet::new(&reference["catalogue"])
}
fn authorized(n: &Net, m: VersionManifest) -> DagVersion {
    let authorization = sign(n.ctx.version_request(&m, "@alice").unwrap());
    DagVersion {
        manifest: m,
        authorization,
    }
}
#[test]
fn protocol_domains_and_legacy_entry_points_are_isolated() {
    let mut n = dag();
    let inst = Instance::new(&n.d, ThreadId("coin-1".into()), &n.base).unwrap();
    let legacy = Context::from_instance(&inst, "tickets", None, &n.auth).unwrap();
    assert_ne!(legacy.id(), n.ctx.id());
    assert_ne!(
        legacy.root_epoch("@alice").unwrap(),
        n.ctx.root_epoch("@alice").unwrap()
    );
    assert_eq!(n.ctx.handoff(), Handoff::MultiParent);
    let root = n.ctx.root_epoch("@alice").unwrap();
    let before = n.rs[0].journal_sequence();
    assert!(n.rs[0].seal(&root, &mut n.j, &n.auth).is_err());
    assert!(n.rs[0].install(&root, &mut n.j, &n.auth).is_err());
    assert!(n.rs[0]
        .prepare_checkpoint("no-proposal", &mut n.j, &n.auth)
        .is_err());
    assert!(n.rs[0]
        .draft_checkpoint(&root, &[], &BTreeSet::new(), &BTreeSet::new())
        .is_err());
    assert_eq!(before, n.rs[0].journal_sequence());
    let mut old = Replica::initialize(legacy.clone(), "@v0", Limits::default(), &mut n.j).unwrap();
    let m = n.rs[0]
        .draft_version(
            &set([root.clone()]),
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::new(),
        )
        .unwrap();
    let v = authorized(&n, m);
    assert!(old.receive_version(v.clone(), &mut n.j, &n.auth).is_err());
    assert!(old
        .adopt_version(&v.manifest.id(n.ctx.id()), &mut n.j, &n.auth)
        .is_err());
    assert!(legacy.version_request(&v.manifest, "@alice").is_err());
    let account = Net::new();
    let inst = Instance::new(&account.d, ThreadId("coin-1".into()), &account.base).unwrap();
    assert!(Context::from_instance_multi_parent(&inst, "coins", None, &account.auth).is_err());
}

#[test]
fn version_authentication_rank_sets_limits_and_overflow_are_checked() {
    let mut x = oracle();
    let valid = x.versions[1].clone().unwrap();
    let reject = |x: &mut OracleNet, v: DagVersion| {
        let before = x.n.rs[0].version_snapshot().unwrap();
        let sequence = x.n.rs[0].journal_sequence();
        assert!(x.n.rs[0].receive_version(v, &mut x.n.j, &x.n.auth).is_err());
        assert_eq!(before, x.n.rs[0].version_snapshot().unwrap());
        assert_eq!(sequence, x.n.rs[0].journal_sequence());
    };
    let mut v = valid.clone();
    v.manifest.rank = 2;
    reject(&mut x, v); // payload changed after actor signature
    let mut v = valid.clone();
    v.authorization.context = "elsewhere".into();
    reject(&mut x, v);
    let mut v = valid.clone();
    v.authorization.signer = COLLECTIVE_POOL.into();
    reject(&mut x, v);
    let mut v = valid.clone();
    v.authorization.signature[0] ^= 1;
    reject(&mut x, v);
    let mut m = valid.manifest.clone();
    m.rank = 0;
    let v = authorized(&x.n, m);
    reject(&mut x, v);
    let mut m = valid.manifest.clone();
    m.parents.clear();
    let v = authorized(&x.n, m);
    reject(&mut x, v);
    let mut m = valid.manifest.clone();
    m.parents = set(["missing".into()]);
    let v = authorized(&x.n, m);
    reject(&mut x, v);
    let mut m = valid.manifest.clone();
    m.allocation.rights = -1;
    let v = authorized(&x.n, m);
    reject(&mut x, v);
    let mut m = valid.manifest.clone();
    m.allocation.rights = 200;
    let v = authorized(&x.n, m);
    reject(&mut x, v);
    let mut m = valid.manifest.clone();
    m.rank = u64::MAX;
    let v = authorized(&x.n, m);
    let id = v.manifest.id(x.n.ctx.id());
    x.n.rs[0].receive_version(v, &mut x.n.j, &x.n.auth).unwrap();
    assert!(x.n.rs[0]
        .draft_version(
            &set([id]),
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::new()
        )
        .unwrap_err()
        .contains("overflow"));
    let mut j = Memory::default();
    let mut r = Replica::initialize(
        x.n.ctx.clone(),
        "@v0",
        Limits {
            checkpoints: 0,
            ..Limits::default()
        },
        &mut j,
    )
    .unwrap();
    assert!(r.receive_version(valid, &mut j, &x.n.auth).is_err());
}

#[test]
fn same_rank_siblings_join_without_a_total_version_order() {
    let mut x = oracle();
    assert!(x.command(&json!(["record", 1, 0])));
    x.register_tx(6); // conservative hold of an uncertified root debit
    let mut b = x.versions[1].as_ref().unwrap().manifest.clone();
    b.held = set([x.acts[6].as_ref().unwrap().address.clone()]);
    b.allocation.rights = 30; // same rank1, distinct semantic node
    let b = authorized(&x.n, b);
    let bid = b.manifest.id(x.n.ctx.id());
    assert_ne!(bid, x.ids[1]);
    for r in &mut x.n.rs {
        r.receive_version(b.clone(), &mut x.n.j, &x.n.auth).unwrap();
    }
    x.n.rs[0]
        .adopt_version(&x.ids[1], &mut x.n.j, &x.n.auth)
        .unwrap();
    x.n.rs[2]
        .adopt_version(&bid, &mut x.n.j, &x.n.auth)
        .unwrap();
    let m = x.n.rs[0]
        .draft_version(
            &set([x.ids[1].clone(), bid]),
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::new(),
        )
        .unwrap();
    assert_eq!(m.rank, 2);
    assert_eq!(m.allocation.rights, 30);
    let m = authorized(&x.n, m);
    let mid = m.manifest.id(x.n.ctx.id());
    for r in &mut x.n.rs {
        r.receive_version(m.clone(), &mut x.n.j, &x.n.auth).unwrap();
    }
    x.n.rs[1]
        .adopt_version(&x.ids[1], &mut x.n.j, &x.n.auth)
        .unwrap();
    for w in [0, 1, 2] {
        x.n.rs[w]
            .adopt_version(&mid, &mut x.n.j, &x.n.auth)
            .unwrap();
    }
    assert_eq!(
        x.n.rs[0].active_epoch("@alice").unwrap(),
        x.n.rs[2].active_epoch("@bob").unwrap()
    );
    // Actor-facing binder uses the adopted DAG ID and keeps external signing.
    let a = ticket(&mut x.n, "@alice", 10, "after-same-rank-join");
    x.n.operation(&a);
    x.n.finalize(&a);
    assert_eq!(x.n.rs[0].finalized_view().unwrap().value, 90);
}

#[test]
fn delayed_local_certificates_do_not_become_global_knowledge() {
    let mut x = oracle();
    x.register_tx(3); // root mint10
    let id = x.acts[3].as_ref().unwrap().address.clone();
    let votes = (0..3)
        .map(|w| {
            sign(
                x.n.rs[w]
                    .prepare_operation(&id, &mut x.n.j, &x.n.auth)
                    .unwrap(),
            )
        })
        .collect();
    let op = Certificate {
        kind: VoteKind::Operation,
        payload: id.clone(),
        votes,
    };
    for w in [0, 1] {
        x.n.rs[w]
            .receive(op.clone(), &mut x.n.j, &x.n.auth)
            .unwrap();
    }
    let before = x.n.rs[2].journal_sequence();
    assert!(x.n.rs[2]
        .prepare_effects(&id, &mut x.n.j, &x.n.auth)
        .is_err());
    assert_eq!(before, x.n.rs[2].journal_sequence());
    let mut votes: Vec<_> = (0..2)
        .map(|w| {
            sign(
                x.n.rs[w]
                    .prepare_effects(&id, &mut x.n.j, &x.n.auth)
                    .unwrap(),
            )
        })
        .collect();
    let mut byz = Vote {
        context: x.n.ctx.id().into(),
        kind: VoteKind::Effects,
        payload: id.clone(),
        signer: "@v3".into(),
        signature: vec![],
    };
    byz.signature = signature(&byz.signer, &byz.preimage());
    votes.push(byz);
    let finality = Certificate {
        kind: VoteKind::Effects,
        payload: id.clone(),
        votes,
    };
    x.n.rs[0]
        .receive(finality.clone(), &mut x.n.j, &x.n.auth)
        .unwrap();
    assert!(x.n.rs[2]
        .receive(finality.clone(), &mut x.n.j, &x.n.auth)
        .is_err());
    let version = x.versions[7].clone().unwrap();
    x.n.rs[0]
        .receive_version(version.clone(), &mut x.n.j, &x.n.auth)
        .unwrap();
    assert!(x.n.rs[2]
        .receive_version(version.clone(), &mut x.n.j, &x.n.auth)
        .is_err());
    assert_eq!(x.n.rs[0].finalized_view().unwrap().value, 110);
    assert_eq!(x.n.rs[2].finalized_view().unwrap().value, 100);
    x.n.rs[2].receive(op, &mut x.n.j, &x.n.auth).unwrap();
    x.n.rs[2].receive(finality, &mut x.n.j, &x.n.auth).unwrap();
    x.n.rs[2]
        .receive_version(version, &mut x.n.j, &x.n.auth)
        .unwrap();
    assert_eq!(x.n.rs[2].finalized_view().unwrap().value, 110);
}

#[test]
fn zero_cost_mint_signatures_are_still_immutable_obligations() {
    let mut n = dag_source(TICKETS);
    let a = n.make("@treasury", "restock", None, 10, "zero-cost");
    n.register(&a);
    let request = n.rs[0]
        .prepare_operation(&a.address, &mut n.j, &n.auth)
        .unwrap();
    let parents = set([n.ctx.root_epoch("@alice").unwrap()]);
    let m = n.rs[0]
        .draft_version(
            &parents,
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::new(),
        )
        .unwrap();
    let v = authorized(&n, m);
    let id = v.manifest.id(n.ctx.id());
    n.rs[0].receive_version(v, &mut n.j, &n.auth).unwrap();
    assert!(n.rs[0].adopt_version(&id, &mut n.j, &n.auth).is_err());
    let m = n.rs[0]
        .draft_version(
            &parents,
            &set([a.address.clone()]),
            &BTreeSet::new(),
            &BTreeSet::new(),
        )
        .unwrap();
    assert_eq!(
        m.allocation,
        Resources {
            rights: 100,
            headroom: 0
        }
    );
    let v = authorized(&n, m);
    let id = v.manifest.id(n.ctx.id());
    n.rs[0].receive_version(v, &mut n.j, &n.auth).unwrap();
    n.rs[0].adopt_version(&id, &mut n.j, &n.auth).unwrap();
    assert_eq!(
        request.preimage(),
        n.rs[0]
            .prepare_operation(&a.address, &mut n.j, &n.auth)
            .unwrap()
            .preimage()
    );
}

#[test]
fn dag_atomic_append_cas_and_recovery_recheck_the_actual_guards() {
    let mut x = oracle();
    let v = x.versions[1].clone().unwrap();
    let before = x.n.rs[0].version_snapshot().unwrap();
    x.n.j.fail = true;
    assert!(x.n.rs[0].receive_version(v, &mut x.n.j, &x.n.auth).is_err());
    assert_eq!(before, x.n.rs[0].version_snapshot().unwrap());
    x.n.j.fail = false;
    assert!(x.command(&json!(["record", 1, 0])));
    assert!(x.command(&json!(["record", 2, 0])));
    let mut stale =
        Replica::recover(x.n.ctx.clone(), "@v0", Limits::default(), &x.n.j, &x.n.auth).unwrap();
    let before = x.n.rs[0].version_snapshot().unwrap();
    x.n.j.fail = true;
    assert!(x.n.rs[0]
        .adopt_version(&x.ids[1], &mut x.n.j, &x.n.auth)
        .is_err());
    assert_eq!(before, x.n.rs[0].version_snapshot().unwrap());
    x.n.j.fail = false;
    x.n.rs[0]
        .adopt_version(&x.ids[1], &mut x.n.j, &x.n.auth)
        .unwrap();
    assert!(stale
        .adopt_version(&x.ids[2], &mut x.n.j, &x.n.auth)
        .unwrap_err()
        .contains("compare-and-append"));
    assert_eq!(stale.version_snapshot().unwrap(), before);
    let key = (x.n.ctx.id().to_string(), "@v0".to_string());
    // Legacy events cannot bypass mode isolation on crash recovery.
    let mut corrupt = Memory {
        logs: x.n.j.logs.clone(),
        fail: false,
    };
    corrupt
        .logs
        .get_mut(&key)
        .unwrap()
        .push(Event::Seal(x.ids[1].clone()));
    assert!(Replica::recover(
        x.n.ctx.clone(),
        "@v0",
        Limits::default(),
        &corrupt,
        &x.n.auth
    )
    .is_err());
    // A direct sibling adoption persisted by a corrupt host is rechecked, not trusted.
    corrupt.logs.get_mut(&key).unwrap().pop();
    corrupt
        .logs
        .get_mut(&key)
        .unwrap()
        .push(Event::AdoptVersion(x.ids[2].clone()));
    assert!(Replica::recover(
        x.n.ctx.clone(),
        "@v0",
        Limits::default(),
        &corrupt,
        &x.n.auth
    )
    .is_err());
    let encoded = serde_json::to_vec(&x.n.j.logs[&key]).unwrap();
    let events: Vec<Event> = serde_json::from_slice(&encoded).unwrap();
    assert_eq!(events, x.n.j.logs[&key]);
}

fn ticket_at(n: &mut Net, w: usize, owner: &str, amount: i64, nonce: &str) -> Act {
    let inst = Instance::new(&n.d, ThreadId("coin-1".into()), &n.base).unwrap();
    let mut f = fields(None, amount);
    f.insert(
        "buyer".into(),
        SExpr::Atom(Atom::Symbol("@customer".into())),
    );
    let m = n.rs[w]
        .intend(&inst, &AgentKey(owner.into()), "sell", f, nonce)
        .unwrap();
    let a = Act::from_message(m, owner).unwrap();
    n.auth.acts.insert((a.address.clone(), owner.into()));
    a
}
fn broadcast_version(n: &mut Net, m: VersionManifest) -> String {
    let v = authorized(n, m);
    let id = v.manifest.id(n.ctx.id());
    for r in &mut n.rs {
        r.receive_version(v.clone(), &mut n.j, &n.auth).unwrap();
    }
    id
}
fn empty_siblings(n: &mut Net) -> (String, String) {
    let root = n.ctx.root_epoch("@alice").unwrap();
    let m = n.rs[0]
        .draft_version(
            &set([root]),
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::new(),
        )
        .unwrap();
    let mut b = m.clone();
    b.rank += 1;
    let a = broadcast_version(n, m);
    let b = broadcast_version(n, b);
    for w in [0, 1] {
        n.rs[w].adopt_version(&a, &mut n.j, &n.auth).unwrap();
    }
    n.rs[2].adopt_version(&b, &mut n.j, &n.auth).unwrap();
    (a, b)
}
#[test]
fn shared_parent_debits_and_credits_are_each_counted_once() {
    let mut x = oracle();
    for cmd in [
        ["sign", "3", "0"],
        ["sign", "3", "1"],
        ["sign", "3", "2"],
        ["effect", "3", "0"],
        ["effect", "3", "1"],
        ["effect", "3", "2"],
    ] {
        assert!(x.command(&json!([
            cmd[0],
            cmd[1].parse::<usize>().unwrap(),
            cmd[2].parse::<usize>().unwrap()
        ])));
    }
    let a = x.versions[7].as_ref().unwrap().manifest.clone();
    let mut b = a.clone();
    b.rank += 1;
    let aid = broadcast_version(&mut x.n, a);
    let bid = broadcast_version(&mut x.n, b);
    for w in [0, 1] {
        x.n.rs[w]
            .adopt_version(&aid, &mut x.n.j, &x.n.auth)
            .unwrap();
    }
    x.n.rs[2]
        .adopt_version(&bid, &mut x.n.j, &x.n.auth)
        .unwrap();
    let m = x.n.rs[0]
        .draft_version(
            &set([aid, bid]),
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::new(),
        )
        .unwrap();
    assert_eq!(m.held.len(), 1);
    assert_eq!(m.credited.len(), 1);
    assert_eq!(
        m.allocation,
        Resources {
            rights: 110,
            headroom: 90
        }
    );
    let id = broadcast_version(&mut x.n, m);
    for w in 0..3 {
        x.n.rs[w].adopt_version(&id, &mut x.n.j, &x.n.auth).unwrap();
    }
    let a = ticket(&mut x.n, "@alice", 60, "after-dedup");
    x.n.operation(&a);
    x.n.finalize(&a);
    assert_eq!(x.n.rs[0].finalized_view().unwrap().value, 50);
}

#[test]
fn crowded_branches_require_cancellation_before_a_funded_join() {
    let mut n = dag_supply(TICKETS, 30);
    let (a, b) = empty_siblings(&mut n);
    let left = ticket_at(&mut n, 0, "@alice", 20, "left");
    let right = ticket_at(&mut n, 2, "@bob", 20, "right");
    n.register(&left);
    n.register(&right);
    for w in [0, 1] {
        n.rs[w]
            .prepare_operation(&left.address, &mut n.j, &n.auth)
            .unwrap();
    }
    n.rs[2]
        .prepare_operation(&right.address, &mut n.j, &n.auth)
        .unwrap();
    let parents = set([a, b]);
    let held = set([left.address.clone(), right.address.clone()]);
    assert!(n.rs[0]
        .draft_version(&parents, &held, &BTreeSet::new(), &BTreeSet::new())
        .unwrap_err()
        .contains("negative"));
    n.cancel(&right);
    n.rs[2].release(&right.address, &mut n.j, &n.auth).unwrap();
    let m = n.rs[0]
        .draft_version(
            &parents,
            &held,
            &set([right.address.clone()]),
            &BTreeSet::new(),
        )
        .unwrap();
    assert_eq!(m.allocation.rights, 10);
    let id = broadcast_version(&mut n, m);
    for w in 0..3 {
        n.rs[w].adopt_version(&id, &mut n.j, &n.auth).unwrap();
    }
    assert!(n.rs[2]
        .version_snapshot()
        .unwrap()
        .signed
        .contains(&right.address));
    assert!(n.rs[2]
        .version_snapshot()
        .unwrap()
        .released
        .contains(&right.address));
    let a = ticket(&mut n, "@alice", 6, "funded-after-join");
    n.operation(&a);
    n.finalize(&a);
    assert_eq!(n.rs[0].finalized_view().unwrap().value, 24);
}

#[test]
fn partial_renewal_counterexample_is_rejected_after_real_quorums() {
    let mut n = dag_supply(TICKETS, 30);
    let operations: Vec<_> = (0..3)
        .map(|i| ticket(&mut n, "@alice", 10, &format!("old-{i}")))
        .collect();
    for op in &operations {
        n.register(op);
    }
    for (i, pair) in [[0, 1], [0, 2], [1, 2]].iter().enumerate() {
        let id = &operations[i].address;
        let mut votes: Vec<_> = pair
            .iter()
            .map(|w| sign(n.rs[*w].prepare_operation(id, &mut n.j, &n.auth).unwrap()))
            .collect();
        let mut byz = Vote {
            context: n.ctx.id().into(),
            kind: VoteKind::Operation,
            payload: id.clone(),
            signer: "@v3".into(),
            signature: vec![],
        };
        byz.signature = signature(&byz.signer, &byz.preimage());
        votes.push(byz);
        let c = Certificate {
            kind: VoteKind::Operation,
            payload: id.clone(),
            votes,
        };
        for r in &mut n.rs {
            r.receive(c.clone(), &mut n.j, &n.auth).unwrap();
        }
    }
    for op in &operations {
        assert!(n.rs[0]
            .certificate(VoteKind::Operation, &op.address)
            .is_some());
    }
    let root = n.ctx.root_epoch("@alice").unwrap();
    let m = n.rs[0]
        .draft_version(
            &set([root]),
            &set([operations[2].address.clone()]),
            &BTreeSet::new(),
            &BTreeSet::new(),
        )
        .unwrap();
    assert_eq!(m.allocation.rights, 20);
    let id = broadcast_version(&mut n, m);
    for w in [1, 2] {
        assert!(n.rs[w]
            .adopt_version(&id, &mut n.j, &n.auth)
            .unwrap_err()
            .contains("historical"));
    }
}
