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
    n.ctx = Context::from_instance(&inst, "tickets", None, &n.auth).unwrap();
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
                phase: VersionPhase::Concurrent,
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
            let s = r.version_snapshot(COLLECTIVE_POOL).unwrap();
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
                    recovered.version_snapshot(COLLECTIVE_POOL).unwrap(),
                    runtime.n.rs[w].version_snapshot(COLLECTIVE_POOL).unwrap()
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
fn quorum_budget_has_one_dag_protocol_and_rejects_legacy_wire_types() {
    let n = dag();
    let account = Net::new();
    let inst = Instance::new(&account.d, ThreadId("coin-1".into()), &account.base).unwrap();
    assert!(Context::from_instance(&inst, "coins", None, &account.auth).is_ok());
    for kind in ["Seal", "Checkpoint", "CheckpointRequest"] {
        let err = serde_json::from_value::<VoteKind>(json!(kind)).unwrap_err();
        assert!(err.to_string().contains("unknown variant"));
    }
    for kind in ["Seal", "Endorse", "Install", "Proposal", "Checkpoint"] {
        let err = serde_json::from_value::<Event>(json!({kind:"obsolete"})).unwrap_err();
        assert!(err.to_string().contains("unknown variant"));
    }
    let text = |s: &str| SExpr::Atom(Atom::Str(s.into()));
    let old_domain = cbcl_core::canonical::canonical_encode(&SExpr::List(vec![
        text("cbcl/quorum-context/v1"),
        text(&cbcl_core::canonical::dialect_hash(&n.d)),
        text("coin-1"),
        text(&n.base[0].address),
        text(&n.base[1].address),
        text("tickets"),
        SExpr::List(
            n.ctx
                .committee()
                .validators
                .iter()
                .map(|k| text(k))
                .collect(),
        ),
        text("1"),
    ]));
    let hash = Sha256::digest(old_domain);
    let mut old_id = String::from("f1220");
    for b in hash {
        old_id.push_str(&format!("{b:02x}"));
    }
    assert_ne!(n.ctx.id(), old_id);
    assert_ne!(n.ctx.id(), account.ctx.id());
}
#[test]
fn version_authentication_rank_sets_limits_and_overflow_are_checked() {
    let mut x = oracle();
    let valid = x.versions[1].clone().unwrap();
    let reject = |x: &mut OracleNet, v: DagVersion| {
        let before = x.n.rs[0].version_snapshot(COLLECTIVE_POOL).unwrap();
        let sequence = x.n.rs[0].journal_sequence();
        assert!(x.n.rs[0].receive_version(v, &mut x.n.j, &x.n.auth).is_err());
        assert_eq!(before, x.n.rs[0].version_snapshot(COLLECTIVE_POOL).unwrap());
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
            versions: 0,
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
    let before = x.n.rs[0].version_snapshot(COLLECTIVE_POOL).unwrap();
    x.n.j.fail = true;
    assert!(x.n.rs[0].receive_version(v, &mut x.n.j, &x.n.auth).is_err());
    assert_eq!(before, x.n.rs[0].version_snapshot(COLLECTIVE_POOL).unwrap());
    x.n.j.fail = false;
    assert!(x.command(&json!(["record", 1, 0])));
    assert!(x.command(&json!(["record", 2, 0])));
    let mut stale =
        Replica::recover(x.n.ctx.clone(), "@v0", Limits::default(), &x.n.j, &x.n.auth).unwrap();
    let before = x.n.rs[0].version_snapshot(COLLECTIVE_POOL).unwrap();
    x.n.j.fail = true;
    assert!(x.n.rs[0]
        .adopt_version(&x.ids[1], &mut x.n.j, &x.n.auth)
        .is_err());
    assert_eq!(before, x.n.rs[0].version_snapshot(COLLECTIVE_POOL).unwrap());
    x.n.j.fail = false;
    x.n.rs[0]
        .adopt_version(&x.ids[1], &mut x.n.j, &x.n.auth)
        .unwrap();
    assert!(stale
        .adopt_version(&x.ids[2], &mut x.n.j, &x.n.auth)
        .unwrap_err()
        .contains("compare-and-append"));
    assert_eq!(stale.version_snapshot(COLLECTIVE_POOL).unwrap(), before);
    let key = (x.n.ctx.id().to_string(), "@v0".to_string());
    // Root replay cannot bypass forward-only adoption on crash recovery.
    let mut corrupt = Memory {
        logs: x.n.j.logs.clone(),
        fail: false,
    };
    corrupt
        .logs
        .get_mut(&key)
        .unwrap()
        .push(Event::AdoptVersion(x.ids[0].clone()));
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
        .version_snapshot(COLLECTIVE_POOL)
        .unwrap()
        .signed
        .contains(&right.address));
    assert!(n.rs[2]
        .version_snapshot(COLLECTIVE_POOL)
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

fn approve_account(n: &mut Net, manifest: VersionManifest) -> String {
    let authorization = sign(n.ctx.version_request(&manifest, &manifest.account).unwrap());
    let id = manifest.id(n.ctx.id());
    let v = DagVersion {
        manifest,
        authorization,
    };
    for r in &mut n.rs {
        r.receive_version(v.clone(), &mut n.j, &n.auth).unwrap();
    }
    id
}
#[test]
fn account_scope_guards_reject_foreign_parents_debits_and_authority() {
    let mut n = Net::new();
    let root = n.ctx.root_epoch("@alice").unwrap();
    let m = n.rs[0]
        .draft_version(
            &set([root.clone()]),
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::new(),
        )
        .unwrap();
    let mut foreign_parent = m.clone();
    foreign_parent
        .parents
        .insert(n.ctx.root_epoch("@treasury").unwrap());
    let v = DagVersion {
        authorization: sign(n.ctx.version_request(&foreign_parent, "@alice").unwrap()),
        manifest: foreign_parent,
    };
    assert!(n.rs[0]
        .receive_version(v, &mut n.j, &n.auth)
        .unwrap_err()
        .contains("parent"));
    let foreign_mint = n.make("@treasury", "mint", None, 10, "foreign-zero-cost");
    n.register(&foreign_mint);
    let mut foreign_held = m.clone();
    foreign_held.held.insert(foreign_mint.address);
    // Cost0 and all other fields valid: only the held operation's scope rejects.
    let v = DagVersion {
        authorization: sign(n.ctx.version_request(&foreign_held, "@alice").unwrap()),
        manifest: foreign_held,
    };
    assert!(n.rs[0]
        .receive_version(v, &mut n.j, &n.auth)
        .unwrap_err()
        .contains("another account"));
    assert!(n.ctx.version_request(&m, "@bob").is_err());
    let mut v = DagVersion {
        authorization: sign(n.ctx.version_request(&m, "@alice").unwrap()),
        manifest: m,
    };
    v.authorization.signer = "@bob".into();
    v.authorization.signature = signature("@bob", &v.authorization.preimage());
    assert!(n.rs[0]
        .receive_version(v, &mut n.j, &n.auth)
        .unwrap_err()
        .contains("actor"));
}

#[test]
fn account_adoption_covers_own_history_without_importing_other_accounts() {
    let mut n = Net::new();
    let pay = n.make("@treasury", "pay", Some("@alice"), 100, "incoming");
    n.operation(&pay);
    n.finalize(&pay);
    let root = n.ctx.root_epoch("@alice").unwrap();
    let m = n.rs[0]
        .draft_version(
            &set([root]),
            &BTreeSet::new(),
            &BTreeSet::new(),
            &set([pay.address.clone()]),
        )
        .unwrap();
    assert_eq!(m.allocation.rights, 100);
    assert!(m.held.is_empty());
    let id = approve_account(&mut n, m);
    for r in &mut n.rs {
        r.adopt_version(&id, &mut n.j, &n.auth).unwrap();
    }
    assert!(n.rs[0]
        .version_snapshot("@alice")
        .unwrap()
        .signed
        .is_empty());
    assert!(n.rs[0]
        .version_snapshot("@treasury")
        .unwrap()
        .signed
        .contains(&pay.address));
    let treasury_root = n.ctx.root_epoch("@treasury").unwrap();
    let bad = n.rs[0]
        .draft_version(
            &set([treasury_root.clone()]),
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::new(),
        )
        .unwrap();
    let bid = approve_account(&mut n, bad);
    assert!(n.rs[0]
        .adopt_version(&bid, &mut n.j, &n.auth)
        .unwrap_err()
        .contains("historical"));
    let good = n.rs[0]
        .draft_version(
            &set([treasury_root]),
            &set([pay.address.clone()]),
            &BTreeSet::new(),
            &BTreeSet::new(),
        )
        .unwrap();
    assert_eq!(good.allocation.rights, 900);
    let tid = approve_account(&mut n, good);
    for r in &mut n.rs {
        r.adopt_version(&tid, &mut n.j, &n.auth).unwrap();
    }
    assert_eq!(n.rs[0].active_epoch("@alice").unwrap(), id);
    assert_eq!(n.rs[0].active_epoch("@treasury").unwrap(), tid);
    let restored =
        Replica::recover(n.ctx.clone(), "@v0", Limits::default(), &n.j, &n.auth).unwrap();
    for account in ["@alice", "@treasury", "@bob"] {
        assert_eq!(
            restored.version_snapshot(account).unwrap(),
            n.rs[0].version_snapshot(account).unwrap()
        );
    }
}
fn account_pay_at(n: &mut Net, w: usize, amount: i64, nonce: &str) -> Act {
    let inst = Instance::new(&n.d, ThreadId("coin-1".into()), &n.base).unwrap();
    let msg = n.rs[w]
        .intend(
            &inst,
            &AgentKey("@alice".into()),
            "pay",
            fields(Some("@bob"), amount),
            nonce,
        )
        .unwrap();
    let a = Act::from_message(msg, "@alice").unwrap();
    n.auth.acts.insert((a.address.clone(), a.signer.clone()));
    a
}
#[test]
fn account_branches_join_with_late_transfers_refunds_and_recovery() {
    let mut n = Net::new();
    let seed = n.make("@treasury", "pay", Some("@alice"), 100, "seed");
    n.operation(&seed);
    n.finalize(&seed);
    let root = n.ctx.root_epoch("@alice").unwrap();
    let a = n.rs[0]
        .draft_version(
            &set([root]),
            &BTreeSet::new(),
            &BTreeSet::new(),
            &set([seed.address.clone()]),
        )
        .unwrap();
    let mut b = a.clone();
    b.rank += 1;
    let aid = approve_account(&mut n, a);
    let bid = approve_account(&mut n, b);
    for w in [0, 1] {
        n.rs[w].adopt_version(&aid, &mut n.j, &n.auth).unwrap();
    }
    for w in [2, 3] {
        n.rs[w].adopt_version(&bid, &mut n.j, &n.auth).unwrap();
    }
    let left = account_pay_at(&mut n, 0, 30, "left");
    let right = account_pay_at(&mut n, 2, 30, "right");
    n.register(&left);
    n.register(&right);
    let mut left_votes = Vec::new();
    for w in [0, 1] {
        left_votes.push(sign(
            n.rs[w]
                .prepare_operation(&left.address, &mut n.j, &n.auth)
                .unwrap(),
        ));
    }
    for w in [2, 3] {
        n.rs[w]
            .prepare_operation(&right.address, &mut n.j, &n.auth)
            .unwrap();
    }
    let m = n.rs[0]
        .draft_version(
            &set([aid, bid]),
            &set([left.address.clone(), right.address.clone()]),
            &BTreeSet::new(),
            &BTreeSet::new(),
        )
        .unwrap();
    assert_eq!(m.allocation.rights, 40);
    assert_eq!(m.credited.len(), 1);
    let mid = approve_account(&mut n, m);
    for r in &mut n.rs {
        r.adopt_version(&mid, &mut n.j, &n.auth).unwrap();
    }
    let current = account_pay_at(&mut n, 0, 20, "current");
    n.operation(&current);
    n.finalize(&current);
    let mut byz = Vote {
        context: n.ctx.id().into(),
        kind: VoteKind::Operation,
        payload: left.address.clone(),
        signer: "@v3".into(),
        signature: vec![],
    };
    byz.signature = signature(&byz.signer, &byz.preimage());
    left_votes.push(byz);
    let c = Certificate {
        kind: VoteKind::Operation,
        payload: left.address.clone(),
        votes: left_votes,
    };
    for r in &mut n.rs {
        r.receive(c.clone(), &mut n.j, &n.auth).unwrap();
    }
    n.finalize(&left);
    let view = n.rs[0].finalized_view().unwrap();
    assert_eq!(view.rights["@alice"], 50);
    assert_eq!(view.rights["@bob"], 50);
    assert_eq!(view.value, 1000);
    n.cancel(&right);
    n.rs[2].release(&right.address, &mut n.j, &n.auth).unwrap();
    let reclaimed = n.advance_version("@alice", std::slice::from_ref(&right.address), &[]);
    assert_eq!(reclaimed.manifest.allocation.rights, 50);
    let restored =
        Replica::recover(n.ctx.clone(), "@v2", Limits::default(), &n.j, &n.auth).unwrap();
    assert_eq!(
        restored.version_snapshot("@alice").unwrap(),
        n.rs[2].version_snapshot("@alice").unwrap()
    );
    assert_eq!(restored.finalized_view().unwrap(), view);
    assert!(restored
        .version_snapshot("@alice")
        .unwrap()
        .released
        .contains(&right.address));
}

/// A local CPU/allocation probe, not a distributed throughput benchmark.
/// Four validators run serially with test authentication and a memory journal.
#[test]
#[ignore = "opt-in performance probe; no network, real crypto or durable storage"]
fn in_memory_throughput_probe() {
    let mut n = dag_supply(TICKETS, 1_000_000);
    let mut completed = 0;
    for target in [50, 100, 250, 500, 1000] {
        let start = std::time::Instant::now();
        let count = target - completed;
        for i in completed..target {
            let a = ticket(&mut n, "@alice", 1, &format!("perf-{i}"));
            n.operation(&a);
            n.finalize(&a);
        }
        let secs = start.elapsed().as_secs_f64();
        println!(
            "COUNTER_TPS history={completed}..{target} count={count} seconds={secs:.6} tps={:.2}",
            count as f64 / secs
        );
        completed = target;
    }
    assert_eq!(n.rs[0].finalized_view().unwrap().value, 999_000);
}

/// Repeat the existing workload long enough for a sampling profiler to attach.
/// Phase timers exclude fixture setup, the final view query and fixture teardown.
#[test]
#[ignore = "opt-in sampling profile; same limitations as the throughput probe"]
fn in_memory_profile_probe() {
    let rounds: usize = std::env::var("CBCL_QUORUM_PROFILE_ROUNDS")
        .map(|s| s.parse().expect("positive integer profile rounds"))
        .unwrap_or(100);
    assert!(rounds > 0);
    let mut construction = std::time::Duration::ZERO;
    let mut operation = std::time::Duration::ZERO;
    let mut finalization = std::time::Duration::ZERO;
    let wall = std::time::Instant::now();
    println!("PROFILE_START pid={} rounds={rounds}", std::process::id());
    for _ in 0..rounds {
        let mut n = dag_supply(TICKETS, 1_000_000);
        for i in 0..1000 {
            let start = std::time::Instant::now();
            let a = ticket(&mut n, "@alice", 1, &format!("perf-{i}"));
            construction += start.elapsed();
            let start = std::time::Instant::now();
            n.operation(&a);
            operation += start.elapsed();
            let start = std::time::Instant::now();
            n.finalize(&a);
            finalization += start.elapsed();
        }
        assert_eq!(n.rs[0].finalized_view().unwrap().value, 999_000);
    }
    let measured = construction + operation + finalization;
    println!(
        "PROFILE_RESULT transactions={} construction_s={:.6} operation_s={:.6} finalization_s={:.6} measured_s={:.6} wall_s={:.6} tps={:.2}",
        rounds * 1000, construction.as_secs_f64(), operation.as_secs_f64(),
        finalization.as_secs_f64(), measured.as_secs_f64(), wall.elapsed().as_secs_f64(),
        (rounds * 1000) as f64 / measured.as_secs_f64()
    );
}

#[test]
fn cached_capacity_changes_only_after_durable_first_sign_and_release() {
    let mut n = dag_source(TICKETS);
    let a = ticket(&mut n, "@alice", 60, "cache-a");
    let b = ticket(&mut n, "@bob", 60, "cache-b");
    let c = ticket(&mut n, "@alice", 10, "cache-c");
    for op in [&a, &b, &c] {
        n.register(op);
    }
    let before = n.rs[0].version_snapshot(COLLECTIVE_POOL).unwrap();
    n.j.fail = true;
    assert!(n.rs[0]
        .prepare_operation(&a.address, &mut n.j, &n.auth)
        .is_err());
    n.j.fail = false;
    assert_eq!(n.rs[0].version_snapshot(COLLECTIVE_POOL).unwrap(), before);
    // Failed A must not consume capacity: B60 must still fit (limit 66).
    let b_request = n.rs[0]
        .prepare_operation(&b.address, &mut n.j, &n.auth)
        .unwrap();
    assert!(n.rs[0]
        .prepare_operation(&a.address, &mut n.j, &n.auth)
        .is_err());
    n.cancel(&b);
    n.j.fail = true;
    assert!(n.rs[0].release(&b.address, &mut n.j, &n.auth).is_err());
    n.j.fail = false;
    // Failed release must not grant capacity or change the original obligation.
    assert!(n.rs[0]
        .prepare_operation(&a.address, &mut n.j, &n.auth)
        .is_err());
    assert!(!n.rs[0]
        .version_snapshot(COLLECTIVE_POOL)
        .unwrap()
        .released
        .contains(&b.address));
    n.rs[0].release(&b.address, &mut n.j, &n.auth).unwrap();
    n.rs[0]
        .prepare_operation(&a.address, &mut n.j, &n.auth)
        .unwrap();
    let sequence = n.rs[0].journal_sequence();
    // A released signature retry is old evidence; it cannot reserve cost again.
    assert_eq!(
        b_request.preimage(),
        n.rs[0]
            .prepare_operation(&b.address, &mut n.j, &n.auth)
            .unwrap()
            .preimage()
    );
    // Neither duplicate release nor signing retry may mint another 60 of capacity.
    n.rs[0].release(&b.address, &mut n.j, &n.auth).unwrap();
    n.rs[0]
        .prepare_operation(&a.address, &mut n.j, &n.auth)
        .unwrap();
    assert_eq!(sequence, n.rs[0].journal_sequence());
    assert!(n.rs[0]
        .prepare_operation(&c.address, &mut n.j, &n.auth)
        .is_err());
    let mut recovered =
        Replica::recover(n.ctx.clone(), "@v0", Limits::default(), &n.j, &n.auth).unwrap();
    assert_eq!(
        recovered.version_snapshot(COLLECTIVE_POOL).unwrap(),
        n.rs[0].version_snapshot(COLLECTIVE_POOL).unwrap()
    );
    assert!(recovered
        .prepare_operation(&c.address, &mut n.j, &n.auth)
        .is_err());
    let sequence = recovered.journal_sequence();
    recovered.release(&b.address, &mut n.j, &n.auth).unwrap();
    assert_eq!(sequence, recovered.journal_sequence());
}

#[test]
fn authoring_rechecks_canonical_identity_and_preserves_rejection_order() {
    use cbcl_core::intend::Reject;
    let n = dag_supply(TICKETS, 1_000_000);
    let request = || {
        let mut f = fields(None, 1);
        f.insert(
            "buyer".into(),
            SExpr::Atom(Atom::Symbol("@customer".into())),
        );
        f
    };
    let author = |d: &Dialect, acts: &[Act], thread: &str, verb: &str, f| {
        let inst = Instance::new(d, ThreadId(thread.into()), acts).unwrap();
        n.rs[0].intend(&inst, &AgentKey("@alice".into()), verb, f, "identity")
    };
    let expected = author(&n.d, &n.base, "coin-1", "sell", request()).unwrap();
    let mut copy = n.d.clone();
    // Convenience integrity fields do not change canonical dialect identity.
    copy.hash = Some("untrusted claim".into());
    copy.signature = Some(vec![1, 2, 3]);
    assert_eq!(
        author(&copy, &n.base, "coin-1", "sell", request()).unwrap(),
        expected
    );
    // Mutating the same caller object after a successful call must be noticed,
    // even if its name and claimed hash still match the pinned dialect.
    copy.hash = Some(cbcl_core::canonical::dialect_hash(&n.d));
    copy.state_bounds = Some(cbcl_core::state::StateBounds {
        max_list: 63,
        ..Default::default()
    });
    assert_ne!(
        cbcl_core::canonical::dialect_hash(&copy),
        cbcl_core::canonical::dialect_hash(&n.d)
    );
    assert!(matches!(
        author(&copy, &n.base, "coin-1", "sell", request()),
        Err(Reject::Resource(_))
    ));
    let altered = Instance::new(&copy, ThreadId("coin-1".into()), &n.base).unwrap();
    assert!(n.rs[0].fold_instance(&altered).is_err());
    assert!(matches!(
        author(&copy, &n.base, "coin-1", "unknown", request()),
        Err(Reject::UnknownVerb)
    ));
    let mut forged_fields = request();
    forged_fields.insert("from".into(), SExpr::Atom(Atom::Symbol("@alice".into())));
    assert!(matches!(
        author(&copy, &n.base, "coin-1", "sell", forged_fields),
        Err(Reject::Forge(_))
    ));
    assert!(matches!(
        author(&n.d, &n.base, "other-thread", "sell", request()),
        Err(Reject::Resource(_))
    ));
    let other = dag_supply(TICKETS, 999_999);
    assert!(matches!(
        author(&n.d, &other.base, "coin-1", "sell", request()),
        Err(Reject::Resource(_))
    ));
    // Public Instance convenience caches cannot override the accepted history.
    let mut forged = Instance::new(&n.d, ThreadId("coin-1".into()), &n.base).unwrap();
    forged.opener = None;
    forged.root = None;
    forged.cast = None;
    assert_eq!(
        n.rs[0]
            .intend(
                &forged,
                &AgentKey("@alice".into()),
                "sell",
                request(),
                "identity"
            )
            .unwrap(),
        expected
    );
    assert_eq!(n.rs[0].journal_sequence(), 1);
}

#[test]
fn cached_genesis_roots_preserve_identity_scope_and_empty_books() {
    for n in [Net::new(), dag()] {
        for actor in ["@alice", "@bob", "@treasury"] {
            let account = if n.ctx.ownership() == cbcl_core::escrow::Ownership::Collective {
                COLLECTIVE_POOL
            } else {
                actor
            };
            let bytes = cbcl_core::canonical::canonical_encode(&SExpr::List(
                ["cbcl/root-epoch/v1", n.ctx.id(), account]
                    .into_iter()
                    .map(|s| SExpr::Atom(Atom::Str(s.into())))
                    .collect(),
            ));
            let expected = format!(
                "f1220{}",
                Sha256::digest(bytes)
                    .iter()
                    .map(|b| format!("{b:02x}"))
                    .collect::<String>()
            );
            assert_eq!(n.ctx.root_epoch(actor).unwrap(), expected);
            assert_eq!(n.ctx.clone().root_epoch(actor).unwrap(), expected);
            let mut returned = n.ctx.root_epoch(actor).unwrap();
            returned.clear();
            assert_eq!(n.ctx.root_epoch(actor).unwrap(), expected);
            let manifest = n.rs[0]
                .draft_version(
                    &set([expected]),
                    &BTreeSet::new(),
                    &BTreeSet::new(),
                    &BTreeSet::new(),
                )
                .unwrap();
            assert_eq!(manifest.account, account);
            assert_eq!(manifest.rank, 1);
            assert!(
                manifest.held.is_empty()
                    && manifest.refunded.is_empty()
                    && manifest.credited.is_empty()
            );
        }
        assert!(n.ctx.root_epoch("@unknown").is_err());
        assert!(n.rs[0]
            .draft_version(
                &set(["unknown-root".into()]),
                &BTreeSet::new(),
                &BTreeSet::new(),
                &BTreeSet::new()
            )
            .is_err());
    }
    let first = dag_supply(TICKETS, 100);
    let second = dag_supply(TICKETS, 101);
    let foreign = second.ctx.root_epoch(COLLECTIVE_POOL).unwrap();
    assert_ne!(first.ctx.root_epoch(COLLECTIVE_POOL).unwrap(), foreign);
    assert!(first.rs[0]
        .draft_version(
            &set([foreign]),
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::new()
        )
        .is_err());
}

#[test]
fn cached_genesis_allocations_preserve_both_budgets_after_context_rebuild() {
    for collective in [false, true] {
        let mut n = if collective {
            dag()
        } else {
            let source = COIN
                .replace("(floor 0)", "(floor 0) (ceiling 2000) (certification quorum-budget (validators @v0 @v1 @v2 @v3))")
                .replace("(initial-rights open :allocations)", "(initial-rights open :allocations) (initial-headroom open :capacity)")
                .replace("(to name allocations)", "(to name allocations capacity)")
                .replace(":allocations allocations))", ":allocations allocations :capacity capacity))")
                .replace("(require :allocations list)", "(require :allocations list) (require :capacity list)");
            Net::source(source, true)
        };
        let limit = if collective { 66 } else { 666 };
        let verbs = if collective {
            ["sell", "restock"]
        } else {
            ["burn", "mint"]
        };
        for verb in verbs {
            let mut make = |amount: i64, nonce: &str| {
                if verb == "sell" {
                    ticket(&mut n, "@alice", amount, nonce)
                } else {
                    n.make("@treasury", verb, None, amount, nonce)
                }
            };
            let too_big = make(limit + 1, &format!("{verb}-too-big"));
            let fits = make(limit, &format!("{verb}-fits"));
            n.register(&too_big);
            n.register(&fits);
            assert!(n.rs[0]
                .prepare_operation(&too_big.address, &mut n.j, &n.auth)
                .is_err());
            n.rs[0]
                .prepare_operation(&fits.address, &mut n.j, &n.auth)
                .unwrap();
        }
        let field = if collective { "tickets" } else { "coins" };
        let account = if collective {
            COLLECTIVE_POOL
        } else {
            "@treasury"
        };
        let inst = Instance::new(&n.d, ThreadId("coin-1".into()), &n.base).unwrap();
        let rebuilt = Context::from_instance(&inst, field, None, &n.auth).unwrap();
        assert_eq!(
            rebuilt.root_epoch(account).unwrap(),
            n.ctx.root_epoch(account).unwrap()
        );
        let mut restored =
            Replica::recover(rebuilt, "@v0", Limits::default(), &n.j, &n.auth).unwrap();
        assert_eq!(
            restored.version_snapshot(account).unwrap(),
            n.rs[0].version_snapshot(account).unwrap()
        );
        let next = if collective {
            ticket(&mut n, "@bob", 1, "after-rebuild")
        } else {
            n.make("@treasury", "burn", None, 1, "after-rebuild")
        };
        restored.register(next.clone(), &mut n.j, &n.auth).unwrap();
        assert!(restored
            .prepare_operation(&next.address, &mut n.j, &n.auth)
            .is_err());
    }
}

#[test]
fn borrowed_identity_rejects_forged_metadata_before_persistence() {
    use cbcl_core::message::Message;
    fn duplicate_amount(message: &mut Message) {
        match message {
            Message::Simple { params, .. } => params.extend([
                SExpr::Atom(Atom::Keyword("amount".into())),
                SExpr::Atom(Atom::Num(2)),
            ]),
            Message::Dialect { inner, .. } => duplicate_amount(inner),
            Message::Wrapped { content, .. } => duplicate_amount(content),
            Message::Meta { .. } => unreachable!(),
        }
    }
    let mut n = dag();
    let original = ticket(&mut n, "@alice", 1, "borrowed-identity");
    let before = n.rs[0].journal_sequence();
    for mutation in 0..5 {
        let mut forged = original.clone();
        match mutation {
            0 => forged.address.push('f'),
            1 => forged.verb = "restock".into(),
            2 => forged.predecessors.clear(),
            3 => {
                forged.recipients.clear();
            }
            _ => {
                forged
                    .fields
                    .insert("amount".into(), SExpr::Atom(Atom::Num(99)));
            }
        }
        n.auth
            .acts
            .insert((forged.address.clone(), forged.signer.clone()));
        let error = n.rs[0].register(forged, &mut n.j, &n.auth).unwrap_err();
        assert_eq!(error, "inconsistent act identity", "mutation {mutation}");
        assert_eq!(n.rs[0].journal_sequence(), before);
    }
    // Coherent last-value-wins caches still reach the original duplicate-key
    // rejection; forging those caches must retain identity-error precedence.
    let mut message = original.message.clone();
    duplicate_amount(&mut message);
    let duplicate = Act::from_message(message, "@alice").unwrap();
    n.auth
        .acts
        .insert((duplicate.address.clone(), duplicate.signer.clone()));
    let mut forged = duplicate.clone();
    forged.fields.clear();
    assert_eq!(
        n.rs[0].register(forged, &mut n.j, &n.auth).unwrap_err(),
        "inconsistent act identity"
    );
    assert_eq!(
        n.rs[0].register(duplicate, &mut n.j, &n.auth).unwrap_err(),
        "duplicate resource keyword"
    );
    assert_eq!(n.rs[0].journal_sequence(), before);
    n.rs[0].register(original, &mut n.j, &n.auth).unwrap();
    assert_eq!(n.rs[0].journal_sequence(), before + 1);
}
