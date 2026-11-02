//! SPEC-033 permanent cutover and full-capacity account continuation.
use super::*;

fn manifest(n: &Net, held: &[Act], allocation: i128) -> VersionManifest {
    VersionManifest {
        phase: VersionPhase::Owned,
        account: "@treasury".into(),
        parents: BTreeSet::from([n.rs[0].active_epoch("@treasury").unwrap().into()]),
        rank: 1,
        held: held.iter().map(|a| a.address.clone()).collect(),
        refunded: BTreeSet::new(),
        credited: BTreeSet::new(),
        allocation: Resources {
            rights: allocation,
            headroom: 0,
        },
    }
}
fn request(n: &Net, mut m: VersionManifest) -> OwnedSealRequest {
    m.phase = VersionPhase::Owned;
    OwnedSealRequest {
        authorization: sign(n.ctx.owned_seal_request(&m, "@treasury").unwrap()),
        version: DagVersion {
            authorization: sign(n.ctx.version_request(&m, "@treasury").unwrap()),
            manifest: m,
        },
    }
}
fn seal(n: &mut Net, req: &OwnedSealRequest) -> String {
    let id = req.version.manifest.id(n.ctx.id());
    let votes =
        n.rs.iter_mut()
            .take(3)
            .map(|r| {
                sign(
                    r.prepare_owned_seal(req.clone(), &mut n.j, &n.auth)
                        .unwrap(),
                )
            })
            .collect();
    let cert = Certificate {
        kind: VoteKind::OwnedSeal,
        payload: id.clone(),
        votes,
    };
    for r in &mut n.rs {
        r.record_owned_proposal(req.clone(), &mut n.j, &n.auth)
            .unwrap();
        r.receive(cert.clone(), &mut n.j, &n.auth).unwrap();
        r.adopt_version(&id, &mut n.j, &n.auth).unwrap();
    }
    id
}
#[test]
fn owned_full_balance_and_last_unit_without_byzantine_votes() {
    let mut n = Net::new();
    let a = n.make("@treasury", "pay", Some("@alice"), 1000, "full");
    n.register(&a);
    assert!(n.rs[0]
        .prepare_operation(&a.address, &mut n.j, &n.auth)
        .is_err());
    let req = request(&n, manifest(&n, &[], 1000));
    let root = seal(&mut n, &req);
    let a = n.make("@treasury", "pay", Some("@alice"), 999, "almost-full");
    n.operation(&a);
    n.finalize(&a);
    let competing = n.make("@treasury", "pay", Some("@bob"), 1, "same-slot");
    n.register(&competing);
    assert!(n.rs[0]
        .prepare_operation(&competing.address, &mut n.j, &n.auth)
        .is_err());
    let mut m = manifest(&n, &[a.clone()], 1);
    m.rank = 2;
    let v = DagVersion {
        authorization: sign(n.ctx.version_request(&m, "@treasury").unwrap()),
        manifest: m,
    };
    let id = v.manifest.id(n.ctx.id());
    for r in &mut n.rs {
        r.receive_version(v.clone(), &mut n.j, &n.auth).unwrap();
        r.adopt_version(&id, &mut n.j, &n.auth).unwrap();
    }
    let last = n.make("@treasury", "pay", Some("@bob"), 1, "last-unit");
    n.operation(&last);
    n.finalize(&last);
    assert_eq!(n.rs[0].finalized_view().unwrap().rights["@treasury"], 0);
    assert_eq!(n.rs[0].owned_root("@treasury"), Some(root.as_str()));
    assert!(!n.rs[3]
        .version_snapshot("@treasury")
        .unwrap()
        .signed
        .contains(&last.address));
    let cancel = sign(
        n.ctx
            .cancellation_request("@treasury", &last.address)
            .unwrap(),
    );
    assert!(n.rs[0].prepare_cancel(cancel, &mut n.j, &n.auth).is_err());
    let recovered =
        Replica::recover(n.ctx.clone(), "@v0", Limits::default(), &n.j, &n.auth).unwrap();
    assert_eq!(
        recovered.finalized_view().unwrap(),
        n.rs[0].finalized_view().unwrap()
    );
    assert_eq!(recovered.owned_root("@treasury"), Some(root.as_str()));
}
#[test]
fn owned_seal_authorization_drain_and_disk_failure() {
    let mut n = Net::new();
    let a = n.make("@treasury", "pay", Some("@alice"), 100, "old");
    n.operation(&a);
    let m = manifest(&n, &[a.clone()], 900);
    let mut req = request(&n, m);
    assert!(n.rs[0]
        .prepare_owned_seal(req.clone(), &mut n.j, &n.auth)
        .is_err());
    n.finalize(&a);
    req.authorization = req.version.authorization.clone();
    assert!(n.rs[0]
        .prepare_owned_seal(req.clone(), &mut n.j, &n.auth)
        .is_err());
    req = request(&n, req.version.manifest);
    n.j.fail = true;
    let before = n.rs[0].journal_sequence();
    assert!(n.rs[0]
        .prepare_owned_seal(req.clone(), &mut n.j, &n.auth)
        .is_err());
    assert_eq!(n.rs[0].journal_sequence(), before);
    n.j.fail = false;
    let new = n.make("@treasury", "pay", Some("@bob"), 1, "not-yet-sealed");
    n.register(&new);
    n.rs[0]
        .prepare_operation(&new.address, &mut n.j, &n.auth)
        .unwrap();
    assert!(n.rs[0]
        .prepare_owned_seal(req.clone(), &mut n.j, &n.auth)
        .is_err());
    // Another validator has no new signature, so it can seal; partial seals do
    // not activate full capacity or permit new old-phase signatures.
    n.rs[1]
        .prepare_owned_seal(req.clone(), &mut n.j, &n.auth)
        .unwrap();
    assert!(n.rs[1]
        .prepare_operation(&new.address, &mut n.j, &n.auth)
        .is_err());
    let mut other = req.version.manifest.clone();
    other.rank = 2;
    let other = request(&n, other);
    assert!(n.rs[1]
        .prepare_owned_seal(other, &mut n.j, &n.auth)
        .is_err());
    let mut r = Replica::recover(n.ctx.clone(), "@v1", Limits::default(), &n.j, &n.auth).unwrap();
    assert!(r
        .prepare_operation(&new.address, &mut n.j, &n.auth)
        .is_err());
    assert_eq!(
        sign(
            r.prepare_owned_seal(req.clone(), &mut n.j, &n.auth)
                .unwrap()
        )
        .kind,
        VoteKind::OwnedSeal
    );
}

#[derive(Default)]
struct Owners {
    logs: BTreeMap<(String, String), Vec<OwnerEvent>>,
    fail: bool,
}
impl OwnerJournal for Owners {
    fn load_owner(&self, c: &str, o: &str) -> Result<Option<Vec<OwnerEvent>>> {
        Ok(self.logs.get(&(c.into(), o.into())).cloned())
    }
    fn append_owner(
        &mut self,
        c: &str,
        o: &str,
        expected: Option<u64>,
        event: &OwnerEvent,
    ) -> Result<()> {
        if self.fail {
            return Err("owner disk failure".into());
        }
        let key = (c.into(), o.into());
        if self.logs.get(&key).map(|l| l.len() as u64) != expected {
            return Err("owner CAS conflict".into());
        }
        self.logs.entry(key).or_default().push(event.clone());
        Ok(())
    }
}
fn publish(n: &mut Net, a: &Act) {
    n.auth.acts.insert((a.address.clone(), a.signer.clone()));
    n.operation(a);
    n.finalize(a);
}
#[test]
fn owned_driver_fifo_drain_recovery_and_full_spend() {
    let mut n = Net::new();
    let mut j = Owners::default();
    let mut owner =
        OwnerDriver::initialize(&n.rs[0], "@treasury", Limits::default(), &mut j).unwrap();
    let first = n.make("@treasury", "pay", Some("@alice"), 600, "fifo-1");
    let second = n.make("@treasury", "pay", Some("@bob"), 400, "fifo-2");
    owner.enqueue(first.clone(), &n.rs[0], &mut j).unwrap();
    owner.enqueue(second, &n.rs[0], &mut j).unwrap();
    let unfunded = n.make("@treasury", "pay", Some("@bob"), 1, "too-much");
    assert!(owner.enqueue(unfunded, &n.rs[0], &mut j).is_err());
    j.fail = true;
    assert!(owner.poll(&n.rs[0], &mut j).is_err());
    j.fail = false;
    let a = published(owner.poll(&n.rs[0], &mut j).unwrap());
    assert_eq!(a, first);
    // Head 2 exceeds remaining concurrent envelope: freeze and retry head 1.
    assert_eq!(published(owner.poll(&n.rs[0], &mut j).unwrap()), a.clone());
    assert!(j
        .logs
        .values()
        .next()
        .unwrap()
        .contains(&OwnerEvent::Freeze));
    owner = OwnerDriver::recover(&n.rs[0], "@treasury", Limits::default(), &j).unwrap();
    assert_eq!(published(owner.poll(&n.rs[0], &mut j).unwrap()), a.clone());
    publish(&mut n, &a);
    let OwnerAction::AuthorizeSeal { manifest: m, .. } = owner.poll(&n.rs[0], &mut j).unwrap()
    else {
        panic!()
    };
    assert_eq!(m.allocation.rights, 400);
    let req = request(&n, m);
    seal(&mut n, &req);
    let b = published(owner.poll(&n.rs[0], &mut j).unwrap());
    assert_eq!(b.fields["amount"], SExpr::Atom(Atom::Num(400)));
    assert_ne!(
        b.fields[cbcl_core::escrow::PREV],
        a.fields[cbcl_core::escrow::PREV]
    );
    owner = OwnerDriver::recover(&n.rs[0], "@treasury", Limits::default(), &j).unwrap();
    assert_eq!(published(owner.poll(&n.rs[0], &mut j).unwrap()), b.clone());
    publish(&mut n, &b);
    assert_eq!(owner.poll(&n.rs[0], &mut j).unwrap(), OwnerAction::Idle);
    OwnerDriver::recover(&n.rs[0], "@treasury", Limits::default(), &j).unwrap();
    assert_eq!(n.rs[0].finalized_view().unwrap().rights["@treasury"], 0);
}

#[test]
fn owned_dual_resource_replenishment_and_account_isolation() {
    let mut n = Net::source(
        COIN.replace(
            "(floor 0)",
            "(floor 0) (ceiling 2000) (certification quorum-budget (validators @v0 @v1 @v2 @v3))",
        )
        .replace(
            "(initial-rights open :allocations)",
            "(initial-rights open :allocations) (initial-headroom open :capacity)",
        )
        .replace("(to name allocations)", "(to name allocations capacity)")
        .replace(
            ":allocations allocations))",
            ":allocations allocations :capacity capacity))",
        )
        .replace(
            "(require :allocations list)",
            "(require :allocations list) (require :capacity list)",
        ),
        true,
    );
    let mut m = manifest(&n, &[], 1000);
    m.allocation.headroom = 1000;
    let req = request(&n, m);
    seal(&mut n, &req);
    let burn = n.make("@treasury", "burn", None, 1000, "burn-all");
    n.operation(&burn);
    n.finalize(&burn);
    let mut held = BTreeSet::from([burn.address.clone()]);
    let mut credited = held.clone();
    let advance = |n: &mut Net, held: &BTreeSet<String>, credits: &BTreeSet<String>| {
        let m = n.rs[0]
            .draft_version(
                &BTreeSet::from([n.rs[0].active_epoch("@treasury").unwrap().into()]),
                held,
                &BTreeSet::new(),
                credits,
            )
            .unwrap();
        let v = DagVersion {
            authorization: sign(n.ctx.version_request(&m, "@treasury").unwrap()),
            manifest: m,
        };
        let id = v.manifest.id(n.ctx.id());
        for r in &mut n.rs {
            r.receive_version(v.clone(), &mut n.j, &n.auth).unwrap();
            r.adopt_version(&id, &mut n.j, &n.auth).unwrap();
        }
    };
    advance(&mut n, &held, &credited);
    let mint = n.make("@treasury", "mint", None, 2000, "mint-from-burn-headroom");
    n.operation(&mint);
    n.finalize(&mint);
    held.insert(mint.address.clone());
    credited.insert(mint.address.clone());
    advance(&mut n, &held, &credited);
    let pay = n.make("@treasury", "pay", Some("@alice"), 2000, "pay-all");
    n.operation(&pay);
    n.finalize(&pay);
    assert_eq!(n.rs[0].finalized_view().unwrap().rights["@treasury"], 0);
    assert_eq!(n.rs[0].finalized_view().unwrap().rights["@alice"], 2000);
    assert_eq!(n.rs[0].owned_root("@alice"), None);
    // Alice independently imports an incoming owned-phase credit, seals and
    // spends its full balance. Treasury's seal does not fence Alice.
    let m = n.rs[0]
        .draft_version(
            &BTreeSet::from([n.rs[0].active_epoch("@alice").unwrap().into()]),
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::from([pay.address.clone()]),
        )
        .unwrap();
    let mut m = m;
    m.phase = VersionPhase::Owned;
    let req = OwnedSealRequest {
        authorization: sign(n.ctx.owned_seal_request(&m, "@alice").unwrap()),
        version: DagVersion {
            authorization: sign(n.ctx.version_request(&m, "@alice").unwrap()),
            manifest: m,
        },
    };
    seal(&mut n, &req);
    let pay = n.make("@alice", "pay", Some("@bob"), 2000, "alice-all");
    n.operation(&pay);
    n.finalize(&pay);
    assert_eq!(n.rs[0].finalized_view().unwrap().rights["@bob"], 2000);
}
#[test]
fn owned_rejects_collective_conversion_and_unsealed_full_capacity() {
    let mut n = collective_source(&TICKETS);
    let root = n.rs[0].active_epoch("@treasury").unwrap().to_string();
    let m = n.rs[0]
        .draft_version(
            &BTreeSet::from([root]),
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::new(),
        )
        .unwrap();
    assert!(n.ctx.owned_seal_request(&m, "@treasury").is_err());
    let req = OwnedSealRequest {
        authorization: sign(n.ctx.version_request(&m, "@treasury").unwrap()),
        version: DagVersion {
            authorization: sign(n.ctx.version_request(&m, "@treasury").unwrap()),
            manifest: m,
        },
    };
    assert!(n.rs[0].prepare_owned_seal(req, &mut n.j, &n.auth).is_err());
    let mut n = Net::new();
    let req = request(&n, manifest(&n, &[], 1000));
    let root = req.version.manifest.id(n.ctx.id());
    for r in &mut n.rs {
        r.receive_version(req.version.clone(), &mut n.j, &n.auth)
            .unwrap();
        assert!(r.adopt_version(&root, &mut n.j, &n.auth).is_err());
    }
    let full = n.make(
        "@treasury",
        "pay",
        Some("@alice"),
        1000,
        "ordinary-version-is-not-seal",
    );
    n.register(&full);
    assert!(n.rs[0]
        .prepare_operation(&full.address, &mut n.j, &n.auth)
        .is_err());
}

#[test]
fn owned_imports_late_credit_from_still_concurrent_account() {
    let mut n = Net::new();
    let req = request(&n, manifest(&n, &[], 1000));
    seal(&mut n, &req);
    let outgoing = n.make("@treasury", "pay", Some("@alice"), 500, "fund-alice");
    publish(&mut n, &outgoing);
    let m = n.rs[0]
        .draft_version(
            &BTreeSet::from([n.rs[0].active_epoch("@alice").unwrap().into()]),
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::from([outgoing.address.clone()]),
        )
        .unwrap();
    let v = DagVersion {
        authorization: sign(n.ctx.version_request(&m, "@alice").unwrap()),
        manifest: m,
    };
    let id = v.manifest.id(n.ctx.id());
    for r in &mut n.rs {
        r.receive_version(v.clone(), &mut n.j, &n.auth).unwrap();
        r.adopt_version(&id, &mut n.j, &n.auth).unwrap();
    }
    let incoming = n.make("@alice", "pay", Some("@treasury"), 100, "return-concurrent");
    publish(&mut n, &incoming);
    assert!(n.rs[0].owned_root("@alice").is_none());
    let m = n.rs[0]
        .draft_version(
            &BTreeSet::from([n.rs[0].active_epoch("@treasury").unwrap().into()]),
            &BTreeSet::from([outgoing.address]),
            &BTreeSet::new(),
            &BTreeSet::from([incoming.address]),
        )
        .unwrap();
    assert_eq!(m.allocation.rights, 600);
    let v = DagVersion {
        authorization: sign(n.ctx.version_request(&m, "@treasury").unwrap()),
        manifest: m,
    };
    let id = v.manifest.id(n.ctx.id());
    for r in &mut n.rs {
        r.receive_version(v.clone(), &mut n.j, &n.auth).unwrap();
        r.adopt_version(&id, &mut n.j, &n.auth).unwrap();
    }
    let a = n.make(
        "@treasury",
        "pay",
        Some("@bob"),
        600,
        "spend-with-late-credit",
    );
    publish(&mut n, &a);
    assert_eq!(n.rs[0].finalized_view().unwrap().rights["@treasury"], 0);
}

fn small_net(supply: i64) -> Net {
    let mut n = Net::new();
    n.base[1] = act(&format!("(signed @treasury (lang example-coin (open (@alice @bob @treasury) :name \"Coin\" :allocations ((@treasury {supply}) (@alice 0) (@bob 0)) :from @treasury :thread \"coin-1\" :caused-by {})))", n.base[0].address), "@treasury");
    n.auth
        .acts
        .insert((n.base[1].address.clone(), "@treasury".into()));
    let inst = Instance::new(&n.d, ThreadId("coin-1".into()), &n.base).unwrap();
    n.ctx = Context::from_instance(&inst, "coins", None, &n.auth).unwrap();
    n.j = Memory::default();
    n.rs = (0..4)
        .map(|i| {
            Replica::initialize(
                n.ctx.clone(),
                &format!("@v{i}"),
                Limits::default(),
                &mut n.j,
            )
            .unwrap()
        })
        .collect();
    n
}
#[test]
fn owned_shared_lean_transition_traces() {
    use serde_json::{json, Value};
    let reference: Value = serde_json::from_str(include_str!(
        "../../../../test-vectors/quorum/owned-lifecycle-lean.json"
    ))
    .unwrap();
    for case in reference["cases"].as_array().unwrap() {
        let supply = case["initial"].as_i64().unwrap();
        let amounts: Vec<i64> = case["amounts"]
            .as_array()
            .unwrap()
            .iter()
            .map(|x| x.as_i64().unwrap())
            .collect();
        let mut n = small_net(supply);
        let req = request(&n, manifest(&n, &[], supply.into()));
        let root = req.version.manifest.id(n.ctx.id());
        let mut seal_votes = Vec::new();
        let mut acts: Vec<Act> = Vec::new();
        let mut op_votes: Vec<Vec<Vote>> = vec![vec![]; amounts.len()];
        let mut effect_votes: Vec<Vec<Vote>> = vec![vec![]; amounts.len()];
        for (step, row) in case["trace"].as_array().unwrap().iter().enumerate() {
            let a = &row["action"];
            let w = a["validator"].as_u64().unwrap() as usize;
            let x = a["operation"].as_u64().unwrap() as usize;
            let kind = a["kind"].as_str().unwrap();
            let accepted = match kind {
                "seal" => {
                    let result = n.rs[w].prepare_owned_seal(req.clone(), &mut n.j, &n.auth);
                    let accepted = result.is_ok();
                    if let Ok(v) = result {
                        seal_votes.push(sign(v));
                    }
                    if seal_votes.len() == 3 {
                        let c = Certificate {
                            kind: VoteKind::OwnedSeal,
                            payload: root.clone(),
                            votes: seal_votes.clone(),
                        };
                        for r in &mut n.rs {
                            r.record_owned_proposal(req.clone(), &mut n.j, &n.auth)
                                .unwrap();
                            r.receive(c.clone(), &mut n.j, &n.auth).unwrap();
                            r.adopt_version(&root, &mut n.j, &n.auth).unwrap();
                        }
                    }
                    accepted
                }
                "sign" => {
                    if acts.len() == x {
                        if x > 0 {
                            let held = acts.iter().map(|a| a.address.clone()).collect();
                            let m = n.rs[0]
                                .draft_version(
                                    &BTreeSet::from([n.rs[0]
                                        .active_epoch("@treasury")
                                        .unwrap()
                                        .into()]),
                                    &held,
                                    &BTreeSet::new(),
                                    &BTreeSet::new(),
                                )
                                .unwrap();
                            let v = DagVersion {
                                authorization: sign(
                                    n.ctx.version_request(&m, "@treasury").unwrap(),
                                ),
                                manifest: m,
                            };
                            let id = v.manifest.id(n.ctx.id());
                            for r in &mut n.rs {
                                r.receive_version(v.clone(), &mut n.j, &n.auth).unwrap();
                                r.adopt_version(&id, &mut n.j, &n.auth).unwrap();
                            }
                        }
                        let act = n.make(
                            "@treasury",
                            "pay",
                            Some("@alice"),
                            amounts[x],
                            &format!("shared-{x}"),
                        );
                        n.register(&act);
                        acts.push(act);
                    }
                    let result = n.rs[w].prepare_operation(&acts[x].address, &mut n.j, &n.auth);
                    let accepted = result.is_ok();
                    if let Ok(v) = result {
                        op_votes[x].push(sign(v));
                    }
                    if op_votes[x].len() == 3 {
                        let c = Certificate {
                            kind: VoteKind::Operation,
                            payload: acts[x].address.clone(),
                            votes: op_votes[x].clone(),
                        };
                        for r in &mut n.rs {
                            r.receive(c.clone(), &mut n.j, &n.auth).unwrap();
                        }
                    }
                    accepted
                }
                "effect" => {
                    let result = n.rs[w].prepare_effects(&acts[x].address, &mut n.j, &n.auth);
                    let accepted = result.is_ok();
                    if let Ok(v) = result {
                        effect_votes[x].push(sign(v));
                    }
                    if effect_votes[x].len() == 3 {
                        let c = Certificate {
                            kind: VoteKind::Effects,
                            payload: acts[x].address.clone(),
                            votes: effect_votes[x].clone(),
                        };
                        for r in &mut n.rs {
                            r.receive(c.clone(), &mut n.j, &n.auth).unwrap();
                        }
                    }
                    accepted
                }
                _ => panic!("unknown reference action"),
            };
            assert_eq!(
                accepted,
                row["accepted"].as_bool().unwrap(),
                "{} step {step}",
                case["name"]
            );
            let snapshots: Vec<_> =
                n.rs.iter()
                    .map(|r| r.version_snapshot("@treasury").unwrap())
                    .collect();
            let flags = |field: fn(&VersionSnapshot) -> &BTreeSet<String>| -> Vec<Vec<bool>> {
                (0..amounts.len())
                    .map(|i| {
                        snapshots
                            .iter()
                            .map(|s| acts.get(i).is_some_and(|a| field(s).contains(&a.address)))
                            .collect()
                    })
                    .collect()
            };
            let certs = |kind| -> Vec<bool> {
                (0..amounts.len())
                    .map(|i| {
                        acts.get(i)
                            .is_some_and(|a| n.rs[0].certificate(kind, &a.address).is_some())
                    })
                    .collect()
            };
            let actual = json!({ "sealed": snapshots.iter().map(|s| s.permanent_seal.is_some()).collect::<Vec<_>>(),
                "signed": flags(|s| &s.signed), "effects": flags(|s| &s.effects), "operation_qc": certs(VoteKind::Operation),
                "effects_qc": certs(VoteKind::Effects), "balance": n.rs[0].finalized_view().unwrap().rights["@treasury"] as i64 });
            assert_eq!(actual, row["state"], "{} step {step}", case["name"]);
        }
    }
}

#[test]
fn owned_future_root_prefence_cannot_become_owned_signature() {
    let mut n = Net::new();
    let req = request(&n, manifest(&n, &[], 1000));
    let root = req.version.manifest.id(n.ctx.id());
    // Future metadata is known, while active versions remain genesis.
    for r in &mut n.rs {
        r.receive_version(req.version.clone(), &mut n.j, &n.auth)
            .unwrap();
    }
    let future = act(&format!("(signed @treasury (lang example-coin (pay (@alice @bob @treasury) () :recipient @alice :amount 1000 :escrow-prev {root} :escrow-deps () :escrow-nonce \"prefenced\" :from @treasury :thread \"coin-1\" :caused-by {})))", n.base[1].address), "@treasury");
    n.auth
        .acts
        .insert((future.address.clone(), future.signer.clone()));
    n.register(&future);
    let cancel = sign(
        n.ctx
            .cancellation_request("@treasury", &future.address)
            .unwrap(),
    );
    let votes =
        n.rs.iter_mut()
            .take(3)
            .map(|r| sign(r.prepare_cancel(cancel.clone(), &mut n.j, &n.auth).unwrap()))
            .collect();
    let cancelled = Certificate {
        kind: VoteKind::Cancel,
        payload: future.address.clone(),
        votes,
    };
    for r in &mut n.rs {
        r.receive(cancelled.clone(), &mut n.j, &n.auth).unwrap();
    }
    seal(&mut n, &req);
    for r in &mut n.rs {
        assert!(r
            .prepare_operation(&future.address, &mut n.j, &n.auth)
            .is_err());
    }
    let mut recovered =
        Replica::recover(n.ctx.clone(), "@v0", Limits::default(), &n.j, &n.auth).unwrap();
    assert!(recovered
        .prepare_operation(&future.address, &mut n.j, &n.auth)
        .is_err());
    let fresh = n.make(
        "@treasury",
        "pay",
        Some("@alice"),
        1000,
        "fresh-after-prefence",
    );
    publish(&mut n, &fresh);
}

#[test]
fn owned_phase_is_bound_and_cannot_downgrade() {
    let mut n = Net::new();
    let mut m = manifest(&n, &[], 1000);
    m.phase = VersionPhase::Concurrent;
    assert!(n.ctx.owned_seal_request(&m, "@treasury").is_err());
    let concurrent_id = m.id(n.ctx.id());
    let req = request(&n, m);
    let root = req.version.manifest.id(n.ctx.id());
    assert_ne!(concurrent_id, root);
    for r in &mut n.rs {
        r.receive_version(req.version.clone(), &mut n.j, &n.auth)
            .unwrap();
        assert!(r.adopt_version(&root, &mut n.j, &n.auth).is_err());
    }
    seal(&mut n, &req);
    let mut child = n.rs[0]
        .draft_version(
            &BTreeSet::from([root]),
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::new(),
        )
        .unwrap();
    assert_eq!(child.phase, VersionPhase::Owned);
    child.phase = VersionPhase::Concurrent;
    let downgrade = DagVersion {
        authorization: sign(n.ctx.version_request(&child, "@treasury").unwrap()),
        manifest: child,
    };
    assert!(n.rs[0]
        .receive_version(downgrade, &mut n.j, &n.auth)
        .is_err());
}

#[test]
fn owned_owner_replay_rejects_changed_issuance_and_forged_completion() {
    let n = Net::new();
    let mut j = Owners::default();
    let mut owner =
        OwnerDriver::initialize(&n.rs[0], "@treasury", Limits::default(), &mut j).unwrap();
    let mut n = n;
    let draft = n.make("@treasury", "pay", Some("@alice"), 10, "replay");
    owner.enqueue(draft.clone(), &n.rs[0], &mut j).unwrap();
    let mut changed = n.make("@treasury", "pay", Some("@bob"), 10, "replay");
    assert!(owner.enqueue(changed.clone(), &n.rs[0], &mut j).is_err());
    let a = published(owner.poll(&n.rs[0], &mut j).unwrap());
    let original = j.logs.values().next().unwrap().clone();
    j.logs
        .values_mut()
        .next()
        .unwrap()
        .push(OwnerEvent::Complete(a.address));
    assert!(OwnerDriver::recover(&n.rs[0], "@treasury", Limits::default(), &j).is_err());
    *j.logs.values_mut().next().unwrap() = original;
    changed
        .fields
        .insert("amount".into(), SExpr::Atom(Atom::Num(1000)));
    if let OwnerEvent::Issue { act, .. } = j.logs.values_mut().next().unwrap().last_mut().unwrap() {
        *act = changed;
    } else {
        panic!()
    }
    assert!(OwnerDriver::recover(&n.rs[0], "@treasury", Limits::default(), &j).is_err());
}

#[test]
fn owned_wire_authority_and_journal_fields_are_closed() {
    let mut n = Net::new();
    let req = request(&n, manifest(&n, &[], 1000));
    let mut value = serde_json::to_value(&req).unwrap();
    value["mode"] = serde_json::json!("owned");
    assert!(serde_json::from_value::<OwnedSealRequest>(value).is_err());
    let act = n.make("@treasury", "pay", Some("@alice"), 1, "closed-fields");
    let event = OwnerEvent::Issue {
        request: act.address.clone(),
        act,
    };
    let mut value = serde_json::to_value(event).unwrap();
    value["Issue"]["trusted_capacity"] = serde_json::json!(1000);
    assert!(serde_json::from_value::<OwnerEvent>(value).is_err());
}

#[test]
fn owned_publication_catches_up_lagging_validator_without_old_adoption_retries() {
    let mut n = Net::new();
    let req = request(&n, manifest(&n, &[], 1000));
    let root = seal(&mut n, &req);
    // h2 sees the root, then falls behind. h0,h1 and Byzantine v3 supply early QCs.
    let first = n.make("@treasury", "pay", Some("@alice"), 100, "early-qc");
    n.register(&first);
    let votes = [0, 1, 3]
        .into_iter()
        .map(|i| {
            sign(
                n.rs[i]
                    .prepare_operation(&first.address, &mut n.j, &n.auth)
                    .unwrap(),
            )
        })
        .collect();
    let op = Certificate {
        kind: VoteKind::Operation,
        payload: first.address.clone(),
        votes,
    };
    for i in [0, 1, 3] {
        n.rs[i].receive(op.clone(), &mut n.j, &n.auth).unwrap();
    }
    let votes = [0, 1, 3]
        .into_iter()
        .map(|i| {
            sign(
                n.rs[i]
                    .prepare_effects(&first.address, &mut n.j, &n.auth)
                    .unwrap(),
            )
        })
        .collect();
    let final_qc = Certificate {
        kind: VoteKind::Effects,
        payload: first.address.clone(),
        votes,
    };
    for i in [0, 1, 3] {
        n.rs[i]
            .receive(final_qc.clone(), &mut n.j, &n.auth)
            .unwrap();
    }
    let m = n.rs[0]
        .draft_version(
            &BTreeSet::from([root.clone()]),
            &BTreeSet::from([first.address]),
            &BTreeSet::new(),
            &BTreeSet::new(),
        )
        .unwrap();
    let v = DagVersion {
        authorization: sign(n.ctx.version_request(&m, "@treasury").unwrap()),
        manifest: m,
    };
    let middle = v.manifest.id(n.ctx.id());
    for i in [0, 1, 3] {
        n.rs[i]
            .receive_version(v.clone(), &mut n.j, &n.auth)
            .unwrap();
        n.rs[i].adopt_version(&middle, &mut n.j, &n.auth).unwrap();
    }
    let m = n.rs[0]
        .draft_version(
            &BTreeSet::from([middle]),
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::new(),
        )
        .unwrap();
    let v = DagVersion {
        authorization: sign(n.ctx.version_request(&m, "@treasury").unwrap()),
        manifest: m,
    };
    let newest = v.manifest.id(n.ctx.id());
    assert!(n.rs[2]
        .receive_version(v.clone(), &mut n.j, &n.auth)
        .is_err());
    assert!(n.rs[2].adopt_version(&newest, &mut n.j, &n.auth).is_err());
    for i in [0, 1, 3] {
        n.rs[i]
            .receive_version(v.clone(), &mut n.j, &n.auth)
            .unwrap();
        n.rs[i].adopt_version(&newest, &mut n.j, &n.auth).unwrap();
    }
    let target = n.make(
        "@treasury",
        "pay",
        Some("@bob"),
        900,
        "after-byzantine-stops",
    );
    let mut publication = n.rs[0].publication(&target).unwrap();
    publication.evidence.reverse();
    let result = n.rs[2]
        .prepare_publication(&publication, &mut n.j, &n.auth)
        .unwrap();
    assert!(
        matches!(result, PublicationResult::Operation(_)),
        "current publication must enable the lagging honest vote"
    );
    assert_eq!(n.rs[2].active_epoch("@treasury").unwrap(), newest);
    let mut recovered =
        Replica::recover(n.ctx.clone(), "@v2", Limits::default(), &n.j, &n.auth).unwrap();
    assert!(matches!(
        recovered
            .prepare_publication(&publication, &mut n.j, &n.auth)
            .unwrap(),
        PublicationResult::Operation(_)
    ));
}

fn published(action: OwnerAction) -> Act {
    match action {
        OwnerAction::Publish(publication) => publication.act,
        _ => panic!("expected durable publication"),
    }
}

fn finish_publication(n: &mut Net, publication: &Publication, signers: &[usize]) {
    n.auth.acts.insert((
        publication.act.address.clone(),
        publication.act.signer.clone(),
    ));
    let votes = signers
        .iter()
        .map(|&i| {
            let PublicationResult::Operation(v) = n.rs[i]
                .prepare_publication(publication, &mut n.j, &n.auth)
                .unwrap()
            else {
                panic!("operation expected")
            };
            sign(v)
        })
        .collect();
    let op = Certificate {
        kind: VoteKind::Operation,
        payload: publication.act.address.clone(),
        votes,
    };
    for &i in signers {
        n.rs[i].receive(op.clone(), &mut n.j, &n.auth).unwrap();
    }
    let publication = n.rs[0].publication(&publication.act).unwrap();
    let votes = signers
        .iter()
        .map(|&i| {
            let PublicationResult::Effects { request: v, .. } = n.rs[i]
                .prepare_publication(&publication, &mut n.j, &n.auth)
                .unwrap()
            else {
                panic!("effects expected")
            };
            sign(v)
        })
        .collect();
    let final_qc = Certificate {
        kind: VoteKind::Effects,
        payload: publication.act.address,
        votes,
    };
    for &i in signers {
        n.rs[i]
            .receive(final_qc.clone(), &mut n.j, &n.auth)
            .unwrap();
    }
}
fn publish_action(action: OwnerAction) -> Publication {
    let OwnerAction::Publish(publication) = action else {
        panic!("publication expected")
    };
    publication
}
fn advance_owner_version(n: &mut Net, action: OwnerAction) -> DagVersion {
    let OwnerAction::AuthorizeVersion(m) = action else {
        panic!("version expected")
    };
    let v = DagVersion {
        authorization: sign(n.ctx.version_request(&m, "@treasury").unwrap()),
        manifest: m,
    };
    let id = v.manifest.id(n.ctx.id());
    for i in [0, 1, 3] {
        n.rs[i]
            .receive_version(v.clone(), &mut n.j, &n.auth)
            .unwrap();
        n.rs[i].adopt_version(&id, &mut n.j, &n.auth).unwrap();
    }
    v
}
#[test]
fn owned_driver_early_byzantine_quorums_then_silence_and_reordered_catchup() {
    let mut n = Net::new();
    let mut j = Owners::default();
    let mut owner =
        OwnerDriver::initialize(&n.rs[0], "@treasury", Limits::default(), &mut j).unwrap();
    for (amount, nonce) in [(700, "first"), (100, "second"), (200, "last")] {
        let a = n.make("@treasury", "pay", Some("@alice"), amount, nonce);
        owner.enqueue(a, &n.rs[0], &mut j).unwrap();
    }
    let OwnerAction::AuthorizeSeal { manifest: m, .. } = owner.poll(&n.rs[0], &mut j).unwrap()
    else {
        panic!()
    };
    let req = request(&n, m);
    seal(&mut n, &req);
    let first = publish_action(owner.poll(&n.rs[0], &mut j).unwrap());
    finish_publication(&mut n, &first, &[0, 1, 3]);
    let action = owner.poll(&n.rs[0], &mut j).unwrap();
    advance_owner_version(&mut n, action);
    let second = publish_action(owner.poll(&n.rs[0], &mut j).unwrap());
    finish_publication(&mut n, &second, &[0, 1, 3]);
    let action = owner.poll(&n.rs[0], &mut j).unwrap();
    let newest = advance_owner_version(&mut n, action);
    let id = newest.manifest.id(n.ctx.id());
    assert!(n.rs[2].receive_version(newest, &mut n.j, &n.auth).is_err());
    assert!(n.rs[2].adopt_version(&id, &mut n.j, &n.auth).is_err());
    // The old adoption messages are not replayed. The current durable publication
    // carries the omitted ancestry/old certificates and is retried after restart.
    let mut target = publish_action(owner.poll(&n.rs[0], &mut j).unwrap());
    target.evidence.reverse();
    owner = OwnerDriver::recover(&n.rs[0], "@treasury", Limits::default(), &j).unwrap();
    assert_eq!(published(owner.poll(&n.rs[0], &mut j).unwrap()), target.act);
    n.auth
        .acts
        .insert((target.act.address.clone(), target.act.signer.clone()));
    n.j.fail = true;
    assert!(n.rs[2]
        .prepare_publication(&target, &mut n.j, &n.auth)
        .is_err());
    n.j.fail = false;
    // Byzantine v3 now contributes nothing: all three honest validators finish.
    finish_publication(&mut n, &target, &[0, 1, 2]);
    assert_eq!(n.rs[2].active_epoch("@treasury").unwrap(), id);
    assert_eq!(owner.poll(&n.rs[0], &mut j).unwrap(), OwnerAction::Idle);
    assert!(j
        .logs
        .values()
        .next()
        .unwrap()
        .contains(&OwnerEvent::Complete(target.act.address.clone())));
    assert_eq!(n.rs[0].finalized_view().unwrap().rights["@treasury"], 0);
}
#[test]
fn owned_partial_publication_remains_pending_and_retries_with_later_evidence() {
    let mut n = Net::new();
    let req = request(&n, manifest(&n, &[], 1000));
    seal(&mut n, &req);
    let act = n.make("@treasury", "pay", Some("@alice"), 1000, "partial");
    let publication = n.rs[0].publication(&act).unwrap();
    let mut j = Memory::default();
    let mut lagging = Replica::initialize(n.ctx.clone(), "@v2", Limits::default(), &mut j).unwrap();
    let partial = Publication {
        act: act.clone(),
        evidence: vec![RelayItem::Act(act.clone())],
    };
    assert!(matches!(
        lagging
            .prepare_publication(&partial, &mut j, &n.auth)
            .unwrap(),
        PublicationResult::Pending { .. }
    ));
    assert!(lagging
        .version_snapshot("@treasury")
        .unwrap()
        .signed
        .is_empty());
    lagging = Replica::recover(n.ctx.clone(), "@v2", Limits::default(), &j, &n.auth).unwrap();
    assert!(matches!(
        lagging
            .prepare_publication(&publication, &mut j, &n.auth)
            .unwrap(),
        PublicationResult::Operation(_)
    ));
}

#[test]
fn owned_seal_publication_supplies_old_effects_to_unsigned_honest_validator() {
    let mut n = Net::new();
    let mut j = Owners::default();
    let mut owner =
        OwnerDriver::initialize(&n.rs[0], "@treasury", Limits::default(), &mut j).unwrap();
    for (amount, nonce) in [(600, "batch"), (400, "outside-envelope")] {
        let a = n.make("@treasury", "pay", Some("@alice"), amount, nonce);
        owner.enqueue(a, &n.rs[0], &mut j).unwrap();
    }
    let first = publish_action(owner.poll(&n.rs[0], &mut j).unwrap());
    finish_publication(&mut n, &first, &[0, 1, 3]);
    let OwnerAction::AuthorizeSeal { manifest, evidence } = owner.poll(&n.rs[0], &mut j).unwrap()
    else {
        panic!()
    };
    let req = request(&n, manifest);
    assert!(n.rs[2]
        .prepare_owned_seal(req.clone(), &mut n.j, &n.auth)
        .is_err());
    let mut seal_pub = SealPublication {
        request: req.clone(),
        evidence,
    };
    seal_pub.evidence.reverse();
    // Old QC was Byzantine-assisted; v3 is now silent. The unsigned h2 can
    // verify that actual old effects QC and seal without producing a stale sign.
    let votes = [0, 1, 2]
        .into_iter()
        .map(|i| {
            let PublicationResult::Seal(v) = n.rs[i]
                .prepare_seal_publication(&seal_pub, &mut n.j, &n.auth)
                .unwrap()
            else {
                panic!()
            };
            sign(v)
        })
        .collect();
    let id = req.version.manifest.id(n.ctx.id());
    let cert = Certificate {
        kind: VoteKind::OwnedSeal,
        payload: id.clone(),
        votes,
    };
    for i in [0, 1, 2] {
        n.rs[i].receive(cert.clone(), &mut n.j, &n.auth).unwrap();
        n.rs[i].adopt_version(&id, &mut n.j, &n.auth).unwrap();
    }
    assert!(!n.rs[2]
        .version_snapshot("@treasury")
        .unwrap()
        .signed
        .contains(&first.act.address));
    let last = publish_action(owner.poll(&n.rs[0], &mut j).unwrap());
    finish_publication(&mut n, &last, &[0, 1, 2]);
    assert_eq!(owner.poll(&n.rs[0], &mut j).unwrap(), OwnerAction::Idle);
    assert_eq!(n.rs[0].finalized_view().unwrap().rights["@treasury"], 0);
}
#[test]
fn owned_catchup_traverses_certified_preseal_ancestry_without_reopening_spending() {
    let mut n = Net::new();
    let m = n.rs[0]
        .draft_version(
            &BTreeSet::from([n.rs[0].active_epoch("@treasury").unwrap().into()]),
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::new(),
        )
        .unwrap();
    let v = DagVersion {
        authorization: sign(n.ctx.version_request(&m, "@treasury").unwrap()),
        manifest: m,
    };
    let concurrent = v.manifest.id(n.ctx.id());
    for i in [0, 1, 3] {
        n.rs[i]
            .receive_version(v.clone(), &mut n.j, &n.auth)
            .unwrap();
        n.rs[i]
            .adopt_version(&concurrent, &mut n.j, &n.auth)
            .unwrap();
    }
    let m = n.rs[0]
        .draft_version(
            &BTreeSet::from([concurrent]),
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::new(),
        )
        .unwrap();
    let req = request(&n, m);
    let root = req.version.manifest.id(n.ctx.id());
    let votes = [0, 1, 3]
        .into_iter()
        .map(|i| {
            sign(
                n.rs[i]
                    .prepare_owned_seal(req.clone(), &mut n.j, &n.auth)
                    .unwrap(),
            )
        })
        .collect();
    let qc = Certificate {
        kind: VoteKind::OwnedSeal,
        payload: root.clone(),
        votes,
    };
    for i in [0, 1, 3] {
        n.rs[i].receive(qc.clone(), &mut n.j, &n.auth).unwrap();
        if i != 1 {
            n.rs[i].adopt_version(&root, &mut n.j, &n.auth).unwrap();
        }
    }
    let target = n.make("@treasury", "pay", Some("@bob"), 1000, "preseal-catchup");
    let pubn = n.rs[0].publication(&target).unwrap();
    assert!(matches!(
        n.rs[2]
            .prepare_publication(&pubn, &mut n.j, &n.auth)
            .unwrap(),
        PublicationResult::Operation(_)
    ));
    assert_eq!(n.rs[2].active_epoch("@treasury").unwrap(), root);
    // A genuine old-epoch Act stays unsignable after catch-up/root QC.
    let concurrent_id = v.manifest.id(n.ctx.id());
    let old = first_old_act(&mut n, &concurrent_id);
    n.rs[2].register(old.clone(), &mut n.j, &n.auth).unwrap();
    assert!(n.rs[2]
        .prepare_operation(&old.address, &mut n.j, &n.auth)
        .is_err());
    n.rs[1].register(old.clone(), &mut n.j, &n.auth).unwrap();
    assert!(n.rs[1]
        .prepare_operation(&old.address, &mut n.j, &n.auth)
        .unwrap_err()
        .contains("outside certified owned continuation"));
}
fn first_old_act(n: &mut Net, epoch: &str) -> Act {
    let a=act(&format!("(signed @treasury (lang example-coin (pay (@alice @bob @treasury) () :recipient @alice :amount 1 :escrow-prev {epoch} :escrow-deps () :escrow-nonce \"old-cannot-reopen\" :from @treasury :thread \"coin-1\" :caused-by {})))",n.base[1].address),"@treasury");
    n.auth.acts.insert((a.address.clone(), a.signer.clone()));
    a
}
#[test]
fn owned_finalized_publication_does_not_accept_a_changed_target() {
    let mut n = Net::new();
    let req = request(&n, manifest(&n, &[], 1000));
    seal(&mut n, &req);
    let a = n.make("@treasury", "pay", Some("@alice"), 1000, "target-auth");
    publish(&mut n, &a);
    let mut publication = n.rs[0].publication(&a).unwrap();
    publication
        .act
        .fields
        .insert("amount".into(), SExpr::Atom(Atom::Num(1)));
    assert!(n.rs[1]
        .prepare_publication(&publication, &mut n.j, &n.auth)
        .is_err());
    let mut req = req;
    req.authorization = req.version.authorization.clone();
    let publication = SealPublication {
        request: req,
        evidence: vec![],
    };
    assert!(n.rs[1]
        .prepare_seal_publication(&publication, &mut n.j, &n.auth)
        .is_err());
}

#[test]
fn owned_relay_rejects_local_decisions_and_oversize_before_mutation() {
    assert!(serde_json::from_value::<RelayItem>(
        serde_json::json!({"Sign":"forged-local-decision"})
    )
    .is_err());
    let mut n = Net::new();
    let a = n.make("@treasury", "pay", Some("@alice"), 1, "bounds");
    let mut publication = n.rs[0].publication(&a).unwrap();
    let before = n.rs[1].journal_sequence();
    publication
        .evidence
        .push(RelayItem::Certificate(Certificate {
            kind: VoteKind::Operation,
            payload: a.address.clone(),
            votes: vec![Vote {
                context: n.ctx.id().into(),
                kind: VoteKind::Operation,
                payload: a.address,
                signer: "@v0".into(),
                signature: vec![0; 8193],
            }],
        }));
    assert!(n.rs[1]
        .prepare_publication(&publication, &mut n.j, &n.auth)
        .is_err());
    assert_eq!(n.rs[1].journal_sequence(), before);
    assert!(n.rs[1]
        .version_snapshot("@treasury")
        .unwrap()
        .signed
        .is_empty());
}

fn peer_qc_without_owner_observation() -> (Net, Act, Publication, Certificate) {
    let mut n = Net::new();
    let req = request(&n, manifest(&n, &[], 1000));
    seal(&mut n, &req);
    let a = n.make("@treasury", "pay", Some("@alice"), 700, "peer-qc");
    n.register(&a);
    let votes = [0, 1, 3]
        .into_iter()
        .map(|i| {
            sign(
                n.rs[i]
                    .prepare_operation(&a.address, &mut n.j, &n.auth)
                    .unwrap(),
            )
        })
        .collect();
    let op = Certificate {
        kind: VoteKind::Operation,
        payload: a.address.clone(),
        votes,
    };
    for i in [1, 2, 3] {
        n.rs[i].receive(op.clone(), &mut n.j, &n.auth).unwrap();
    }
    assert!(n.rs[0]
        .certificate(VoteKind::Operation, &a.address)
        .is_none());
    let publication = n.rs[0].publication(&a).unwrap();
    (n, a, publication, op)
}
#[test]
fn owned_effects_response_relays_the_qc_which_retired_signature_work() {
    let (mut n, a, publication, op) = peer_qc_without_owner_observation();
    let PublicationResult::Effects {
        operation,
        request: _,
    } = n.rs[2]
        .prepare_publication(&publication, &mut n.j, &n.auth)
        .unwrap()
    else {
        panic!()
    };
    assert_eq!(operation, op);
    let report = n.rs[0]
        .receive_evidence(&[RelayItem::Certificate(operation)], &mut n.j, &n.auth)
        .unwrap();
    assert!(report.pending.is_empty());
    let publication = n.rs[0].publication(&a).unwrap();
    let votes = [0, 1, 2]
        .into_iter()
        .map(|i| {
            let PublicationResult::Effects { request, .. } = n.rs[i]
                .prepare_publication(&publication, &mut n.j, &n.auth)
                .unwrap()
            else {
                panic!()
            };
            sign(request)
        })
        .collect();
    n.rs[0]
        .receive(
            Certificate {
                kind: VoteKind::Effects,
                payload: a.address.clone(),
                votes,
            },
            &mut n.j,
            &n.auth,
        )
        .unwrap();
    assert_eq!(n.rs[0].finalized_view().unwrap().rights["@treasury"], 300);
    assert!(!n.rs[2]
        .version_snapshot("@treasury")
        .unwrap()
        .signed
        .contains(&a.address));
}
#[test]
fn owned_finalized_peer_returns_a_complete_verifiable_certificate_chain() {
    let (mut n, a, publication, _) = peer_qc_without_owner_observation();
    let votes = [1, 2, 3]
        .into_iter()
        .map(|i| {
            sign(
                n.rs[i]
                    .prepare_effects(&a.address, &mut n.j, &n.auth)
                    .unwrap(),
            )
        })
        .collect();
    let effects = Certificate {
        kind: VoteKind::Effects,
        payload: a.address.clone(),
        votes,
    };
    n.rs[1].receive(effects.clone(), &mut n.j, &n.auth).unwrap();
    let PublicationResult::Finalized {
        certificate,
        evidence,
    } = n.rs[1]
        .prepare_publication(&publication, &mut n.j, &n.auth)
        .unwrap()
    else {
        panic!()
    };
    assert_eq!(certificate, effects);
    let report = n.rs[0]
        .receive_evidence(&evidence, &mut n.j, &n.auth)
        .unwrap();
    assert!(report.pending.is_empty());
    assert_eq!(
        n.rs[0].certificate(VoteKind::Effects, &a.address),
        Some(&effects)
    );
    assert_eq!(n.rs[0].finalized_view().unwrap().rights["@treasury"], 300);
}
#[test]
fn owned_relay_does_not_add_an_unadvertised_cumulative_manifest_byte_limit() {
    let mut n = Net::new();
    n.j = Memory::default();
    n.rs = (0..4)
        .map(|i| {
            Replica::initialize(
                n.ctx.clone(),
                &format!("@v{i}"),
                Limits {
                    object_bytes: 1200,
                    ..Limits::default()
                },
                &mut n.j,
            )
            .unwrap()
        })
        .collect();
    let mut held = Vec::new();
    for i in 0..20 {
        let a = n.make(
            "@treasury",
            "pay",
            Some("@alice"),
            1,
            &format!("manifest-{i}"),
        );
        publish(&mut n, &a);
        held.push(a);
    }
    let m = manifest(&n, &held, 980);
    assert!(m.held.iter().map(String::len).sum::<usize>() > 1200);
    let req = request(&n, m);
    let evidence = n.rs[0].seal_evidence(&req.version.manifest).unwrap();
    let publication = SealPublication {
        request: req,
        evidence,
    };
    assert!(matches!(
        n.rs[2]
            .prepare_seal_publication(&publication, &mut n.j, &n.auth)
            .unwrap(),
        PublicationResult::Seal(_)
    ));
}

#[test]
fn owned_relay_preserves_independent_signature_and_object_limits() {
    struct LongVotes<'a>(&'a Auth);
    impl Authentication for LongVotes<'_> {
        fn verify(&self, k: &str, m: &[u8], s: &[u8]) -> bool {
            s.len() >= 32 && s[32..].iter().all(|b| *b == 0) && signature(k, m) == s[..32]
        }
        fn authenticate_act(&self, a: &Act) -> bool {
            self.0.authenticate_act(a)
        }
    }
    fn long(req: SigningRequest) -> Vote {
        let mut v = sign(req);
        v.signature.resize(2000, 0);
        v
    }
    let mut n = Net::new();
    n.j = Memory::default();
    n.rs = (0..4)
        .map(|i| {
            Replica::initialize(
                n.ctx.clone(),
                &format!("@v{i}"),
                Limits {
                    object_bytes: 1200,
                    signature_bytes: 8192,
                    ..Limits::default()
                },
                &mut n.j,
            )
            .unwrap()
        })
        .collect();
    let mut req = request(&n, manifest(&n, &[], 1000));
    req.authorization.signature.resize(2000, 0);
    req.version.authorization.signature.resize(2000, 0);
    let auth = LongVotes(&n.auth);
    let votes =
        n.rs.iter_mut()
            .take(3)
            .map(|r| long(r.prepare_owned_seal(req.clone(), &mut n.j, &auth).unwrap()))
            .collect();
    let id = req.version.manifest.id(n.ctx.id());
    let qc = Certificate {
        kind: VoteKind::OwnedSeal,
        payload: id.clone(),
        votes,
    };
    for r in &mut n.rs {
        r.record_owned_proposal(req.clone(), &mut n.j, &auth)
            .unwrap();
        r.receive(qc.clone(), &mut n.j, &auth).unwrap();
        r.adopt_version(&id, &mut n.j, &auth).unwrap();
    }
    let target = n.make("@treasury", "pay", Some("@alice"), 1000, "long-votes");
    let publication = n.rs[0].publication(&target).unwrap();
    let auth = LongVotes(&n.auth);
    assert!(matches!(
        n.rs[2]
            .prepare_publication(&publication, &mut n.j, &auth)
            .unwrap(),
        PublicationResult::Operation(_)
    ));
}

#[test]
fn owned_catchup_searches_a_covering_parent_instead_of_sticking_to_hash_order() {
    let mut n = Net::new();
    let genesis = n.rs[0].active_epoch("@treasury").unwrap().to_string();
    let old = n.make("@treasury", "pay", Some("@alice"), 10, "branch-history");
    publish(&mut n, &old);
    let b = n.rs[0]
        .draft_version(
            &BTreeSet::from([genesis.clone()]),
            &BTreeSet::from([old.address]),
            &BTreeSet::new(),
            &BTreeSet::new(),
        )
        .unwrap();
    let bid = b.id(n.ctx.id());
    let mut a = n.rs[0]
        .draft_version(
            &BTreeSet::from([genesis]),
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::new(),
        )
        .unwrap();
    // Force the noncovering branch to be the old DFS's first choice. Rank is
    // merely a well-founded label; no metadata is installed during this search.
    let rank = (1..4096)
        .find(|rank| {
            a.rank = *rank;
            a.id(n.ctx.id()) > bid
        })
        .expect("ordered branch fixture");
    a.rank = rank;
    let aid = a.id(n.ctx.id());
    for m in [a, b] {
        let v = DagVersion {
            authorization: sign(n.ctx.version_request(&m, "@treasury").unwrap()),
            manifest: m,
        };
        for r in &mut n.rs {
            r.receive_version(v.clone(), &mut n.j, &n.auth).unwrap();
        }
    }
    for i in [0, 1, 3] {
        n.rs[i].adopt_version(&bid, &mut n.j, &n.auth).unwrap();
    }
    let m = n.rs[0]
        .draft_version(
            &BTreeSet::from([aid.clone(), bid.clone()]),
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::new(),
        )
        .unwrap();
    let req = request(&n, m);
    let root = req.version.manifest.id(n.ctx.id());
    let votes = [0, 1, 3]
        .into_iter()
        .map(|i| {
            sign(
                n.rs[i]
                    .prepare_owned_seal(req.clone(), &mut n.j, &n.auth)
                    .unwrap(),
            )
        })
        .collect();
    let qc = Certificate {
        kind: VoteKind::OwnedSeal,
        payload: root.clone(),
        votes,
    };
    for i in [0, 1, 3] {
        n.rs[i].receive(qc.clone(), &mut n.j, &n.auth).unwrap();
        n.rs[i].adopt_version(&root, &mut n.j, &n.auth).unwrap();
    }
    let target = n.make("@treasury", "pay", Some("@bob"), 990, "covering-path");
    let publication = n.rs[0].publication(&target).unwrap();
    assert!(matches!(
        n.rs[2]
            .prepare_publication(&publication, &mut n.j, &n.auth)
            .unwrap(),
        PublicationResult::Operation(_)
    ));
    let snapshot = n.rs[2].version_snapshot("@treasury").unwrap();
    assert!(snapshot.visited.contains(&bid));
    assert!(!snapshot.visited.contains(&aid));
    assert_eq!(snapshot.active, root);
}

#[test]
fn owned_relay_uses_pinned_identity_bounds_instead_of_act_byte_limit() {
    let long = format!("@{}", "v".repeat(1500));
    let d = dialect(&COIN.replace(
        "(floor 0)",
        &format!("(floor 0) (certification quorum-budget (validators {long} @v1 @v2 @v3))"),
    ));
    let base = initial(&d, false);
    let auth = Auth {
        acts: base
            .iter()
            .map(|a| (a.address.clone(), a.signer.clone()))
            .collect(),
    };
    let inst = Instance::new(&d, ThreadId("coin-1".into()), &base).unwrap();
    let ctx = Context::from_instance(&inst, "coins", None, &auth).unwrap();
    let mut j = Memory::default();
    let rs = [long.as_str(), "@v1", "@v2", "@v3"]
        .into_iter()
        .map(|key| {
            Replica::initialize(
                ctx.clone(),
                key,
                Limits {
                    object_bytes: 1200,
                    ..Limits::default()
                },
                &mut j,
            )
            .unwrap()
        })
        .collect();
    let mut n = Net {
        d,
        base,
        ctx,
        auth,
        j,
        rs,
    };
    let req = request(&n, manifest(&n, &[], 1000));
    seal(&mut n, &req);
    let target = n.make("@treasury", "pay", Some("@alice"), 1000, "pinned-name");
    let publication = n.rs[0].publication(&target).unwrap();
    assert!(matches!(
        n.rs[2]
            .prepare_publication(&publication, &mut n.j, &n.auth)
            .unwrap(),
        PublicationResult::Operation(_)
    ));
}
