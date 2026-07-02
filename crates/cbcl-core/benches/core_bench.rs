use criterion::{black_box, criterion_group, criterion_main, Criterion};

use cbcl_core::dialect::{Dialect, DialectRegistry, PerformativeDef, ResourceBounds};
use cbcl_core::evaluator;
use cbcl_core::gossip::{GossipConfig, GossipNetwork, Topology};
use cbcl_core::message::{CausedBy, CorePerformative, Message, Performative};
use cbcl_core::msg_tag;
use cbcl_core::policy::{apply_policy, UnknownPredecessorPolicy};
use cbcl_core::protocol::{verify_causal, CausalProtocol, NodeRef, StepDecl, VerificationResult};
use cbcl_core::r1;
use cbcl_core::r2::{self, ResourceState};
use cbcl_core::r3;
use cbcl_core::sexpr::{Atom, SExpr};
use cbcl_core::shape::{ShapeConstraint, ShapeRule, TypeConstraint};
use cbcl_core::store::{ContentHash, HashIndex, MessageStore, ThreadId, ThreadedMessageStore};
use cbcl_core::template;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn sym(s: &str) -> SExpr {
    SExpr::Atom(Atom::Symbol(String::from(s)))
}

fn str_expr(s: &str) -> SExpr {
    SExpr::Atom(Atom::Str(String::from(s)))
}

fn parse(s: &str) -> SExpr {
    s.parse().unwrap()
}

fn valid_bounds() -> ResourceBounds {
    ResourceBounds {
        max_depth: 8,
        max_expansion_size: 512,
        verification_time_ms: 10,
    }
}

fn make_dialect(name: &str, perfs: Vec<PerformativeDef>) -> Dialect {
    Dialect {
        roles: Vec::new(),
        name: String::from(name),
        extends: vec![String::from("cbcl")],
        author: None,
        performatives: perfs,
        resources: valid_bounds(),
        examples: vec![],
        signature: None,
        hash: None,
        protocol: None,
        causal_protocol: None,
        shapes: Vec::new(),
    }
}

fn make_perf(name: &str, template_str: &str) -> PerformativeDef {
    PerformativeDef {
        role: None,
        name: String::from(name),
        params: vec![],
        template: parse(template_str),
    }
}

fn test_dialect(name: &str) -> Dialect {
    Dialect {
        roles: Vec::new(),
        name: String::from(name),
        extends: Vec::new(),
        author: None,
        performatives: vec![PerformativeDef {
            role: None,
            name: format!("{}-action", name),
            params: Vec::new(),
            template: SExpr::List(vec![
                sym("effect"),
                SExpr::Atom(Atom::Symbol(format!("{}-effect", name))),
            ]),
        }],
        resources: valid_bounds(),
        examples: Vec::new(),
        signature: None,
        hash: None,
        protocol: None,
        causal_protocol: None,
        shapes: Vec::new(),
    }
}

use std::string::String;

// ---------------------------------------------------------------------------
// R1 benchmarks
// ---------------------------------------------------------------------------

fn bench_r1(c: &mut Criterion) {
    let safe_template = parse("(literal (tell recipient message))");
    c.bench_function("r1/verify_single_safe", |b| {
        b.iter(|| r1::verify_r1(black_box("notify"), black_box(&safe_template)))
    });

    let recursive_template = parse("(literal (factorial (- n 1)))");
    c.bench_function("r1/verify_single_recursive", |b| {
        b.iter(|| r1::verify_r1(black_box("factorial"), black_box(&recursive_template)))
    });

    let safe_dialect = make_dialect(
        "safe-dialect",
        vec![
            make_perf("greet", "(literal (tell @alice msg))"),
            make_perf("notify", "(literal (ask @bob content))"),
            make_perf(
                "dispatch",
                "(cond ((= priority urgent) (literal (tell @emergency msg))) (else (literal (tell @normal msg))))",
            ),
        ],
    );
    c.bench_function("r1/verify_dialect_safe_3perfs", |b| {
        b.iter(|| r1::verify_r1_dialect(black_box(&safe_dialect)))
    });

    let recursive_dialect = make_dialect(
        "bad-dialect",
        vec![
            make_perf("a", "(literal (a x))"),
            make_perf("b", "(literal (tell x y))"),
            make_perf("c", "(literal (c z))"),
        ],
    );
    c.bench_function("r1/violations_mixed", |b| {
        b.iter(|| r1::r1_violations(black_box(&recursive_dialect)))
    });

    // Deep nested template for R1 check
    let deep = parse(
        "(sequence (literal (tell coordinator \"starting\")) \
         (literal (tell worker task)) \
         (literal (tell coordinator \"done\")))",
    );
    c.bench_function("r1/verify_deep_template", |b| {
        b.iter(|| r1::verify_r1(black_box("workflow"), black_box(&deep)))
    });
}

// ---------------------------------------------------------------------------
// R2 benchmarks
// ---------------------------------------------------------------------------

fn bench_r2(c: &mut Criterion) {
    let valid_dialect = make_dialect("valid", vec![]);
    c.bench_function("r2/verify_valid_bounds", |b| {
        b.iter(|| r2::verify_r2(black_box(&valid_dialect)))
    });

    let invalid_dialect = Dialect {
        resources: ResourceBounds {
            max_depth: 100,
            max_expansion_size: 512,
            verification_time_ms: 10,
        },
        ..make_dialect("invalid", vec![])
    };
    c.bench_function("r2/verify_invalid_bounds", |b| {
        b.iter(|| r2::verify_r2(black_box(&invalid_dialect)))
    });

    let expr = parse("(tell @alice \"hello world\")");
    c.bench_function("r2/bounded_eval_simple", |b| {
        b.iter(|| {
            let mut rs = ResourceState::new(8, 512);
            r2::bounded_eval(black_box(10), black_box(&expr), &mut rs)
        })
    });

    let nested = parse("(a (b (c (d 42))))");
    c.bench_function("r2/bounded_eval_nested", |b| {
        b.iter(|| {
            let mut rs = ResourceState::new(16, 1024);
            r2::bounded_eval(black_box(20), black_box(&nested), &mut rs)
        })
    });

    c.bench_function("r2/resource_state_enter_exit", |b| {
        b.iter(|| {
            let rs = ResourceState::new(16, 1024);
            let rs1 = rs.enter_depth().unwrap();
            let rs2 = rs1.enter_depth().unwrap();
            let rs3 = rs2.add_expansion(100).unwrap();
            black_box(rs3.exit_depth())
        })
    });
}

// ---------------------------------------------------------------------------
// R3 benchmarks
// ---------------------------------------------------------------------------

fn bench_r3(c: &mut Criterion) {
    let safe_dialect = make_dialect("custom", vec![make_perf("greet", "(literal (tell x y))")]);
    c.bench_function("r3/verify_safe", |b| {
        b.iter(|| r3::verify_r3(black_box(&safe_dialect)))
    });

    let bad_dialect = make_dialect(
        "bad",
        vec![
            make_perf("tell", "(literal (tell x y))"),
            make_perf("custom", "(literal (ask x y))"),
            make_perf("ask", "(literal (ask x y))"),
        ],
    );
    c.bench_function("r3/violations_mixed", |b| {
        b.iter(|| r3::r3_violations(black_box(&bad_dialect)))
    });

    let base = cbcl_core::dialect::base_dialect();
    c.bench_function("r3/verify_base_dialect", |b| {
        b.iter(|| r3::verify_r3(black_box(&base)))
    });
}

// ---------------------------------------------------------------------------
// Template expansion benchmarks
// ---------------------------------------------------------------------------

fn bench_template(c: &mut Criterion) {
    let def = PerformativeDef {
        role: None,
        name: String::from("greet"),
        params: vec![sym("recipient"), sym("msg")],
        template: parse("(tell recipient msg)"),
    };
    let args = vec![sym("@bob"), str_expr("hey")];
    c.bench_function("template/expand_simple", |b| {
        b.iter(|| {
            let mut rs = ResourceState::new(8, 512);
            template::expand_template(black_box(&def), black_box(&args), &mut rs)
        })
    });

    let literal_template = parse("(literal (tell @alice message))");
    let bindings = {
        let mut m = template::Bindings::new();
        m.insert(String::from("message"), str_expr("hello"));
        m
    };
    c.bench_function("template/expand_literal_with_bindings", |b| {
        b.iter(|| {
            let mut rs = ResourceState::new(8, 512);
            template::expand_template_with_bindings(
                black_box(&literal_template),
                black_box(&bindings),
                &mut rs,
            )
        })
    });

    let cond_template = parse(
        "(cond ((= priority urgent) (literal (tell @emergency message))) \
         (else (literal (tell @normal message))))",
    );
    let cond_bindings = {
        let mut m = template::Bindings::new();
        m.insert(String::from("priority"), sym("urgent"));
        m.insert(String::from("message"), str_expr("fire!"));
        m
    };
    c.bench_function("template/expand_cond", |b| {
        b.iter(|| {
            let mut rs = ResourceState::new(8, 512);
            template::expand_template_with_bindings(
                black_box(&cond_template),
                black_box(&cond_bindings),
                &mut rs,
            )
        })
    });

    let seq_template = parse(
        "((literal (tell @coordinator \"start\")) \
         (literal (tell @worker \"task\")) \
         (literal (tell @coordinator \"done\")))",
    );
    c.bench_function("template/expand_sequence", |b| {
        b.iter(|| {
            let mut rs = ResourceState::new(8, 4096);
            template::expand_template_with_bindings(
                black_box(&seq_template),
                black_box(&template::Bindings::new()),
                &mut rs,
            )
        })
    });
}

// ---------------------------------------------------------------------------
// msg_tag benchmarks
// ---------------------------------------------------------------------------

fn bench_msg_tag(c: &mut Criterion) {
    let tell_expr = parse("(tell @bob \"hi\")");
    c.bench_function("msg_tag/simple_head", |b| {
        b.iter(|| msg_tag::msg_tag(black_box(&tell_expr)))
    });

    let lang_expr = parse("(lang logistics (tell @system \"PKG-123\"))");
    c.bench_function("msg_tag/head_and_second", |b| {
        b.iter(|| msg_tag::msg_tag(black_box(&lang_expr)))
    });

    let atom_expr = SExpr::Atom(Atom::Num(42));
    c.bench_function("msg_tag/unknown_atom", |b| {
        b.iter(|| msg_tag::msg_tag(black_box(&atom_expr)))
    });
}

// ---------------------------------------------------------------------------
// Evaluator benchmarks
// ---------------------------------------------------------------------------

fn bench_eval(c: &mut Criterion) {
    let registry = DialectRegistry::new();

    let tell_msg = Message::Simple {
        performative: Performative::Core(CorePerformative::Tell),
        recipient: Some("@bob".into()),
        content: str_expr("hello"),
        params: Vec::new(),
        thread: None,
        sender: None,
        caused_by: None,
    };
    c.bench_function("eval/tell", |b| {
        b.iter(|| evaluator::evaluate(black_box(&tell_msg), black_box(&registry)))
    });

    let ask_msg = Message::Simple {
        performative: Performative::Core(CorePerformative::Ask),
        recipient: Some("@alice".into()),
        content: str_expr("what time?"),
        params: Vec::new(),
        thread: None,
        sender: None,
        caused_by: None,
    };
    c.bench_function("eval/ask", |b| {
        b.iter(|| evaluator::evaluate(black_box(&ask_msg), black_box(&registry)))
    });

    let meta_msg = Message::Meta {
        dialect_def: parse("(define test-dialect (cbcl) @author)"),
    };
    c.bench_function("eval/meta", |b| {
        b.iter(|| evaluator::evaluate(black_box(&meta_msg), black_box(&registry)))
    });

    // Custom performative with a registry that has a dialect installed
    let mut custom_registry = DialectRegistry::new();
    custom_registry
        .install(Dialect {
            roles: Vec::new(),
            name: String::from("logistics"),
            extends: vec![String::from("cbcl")],
            author: None,
            performatives: vec![PerformativeDef {
                role: None,
                name: String::from("ship"),
                params: vec![sym("package"), sym("destination")],
                template: parse("(effect dispatch-shipment)"),
            }],
            resources: valid_bounds(),
            examples: Vec::new(),
            signature: None,
            hash: None,
            protocol: None,
            causal_protocol: None,
            shapes: Vec::new(),
        })
        .unwrap();

    let ship_msg = Message::Simple {
        performative: Performative::Custom(String::from("ship")),
        recipient: None,
        content: str_expr("PKG-123"),
        params: vec![sym("warehouse-A")],
        thread: None,
        sender: None,
        caused_by: None,
    };
    c.bench_function("eval/custom_performative", |b| {
        b.iter(|| evaluator::evaluate(black_box(&ship_msg), black_box(&custom_registry)))
    });
}

// ---------------------------------------------------------------------------
// Gossip simulation benchmarks
// ---------------------------------------------------------------------------

fn bench_gossip(c: &mut Criterion) {
    c.bench_function("gossip/simulate_10_agents", |b| {
        b.iter(|| {
            let config = GossipConfig {
                transmission_probability: 0.8,
                max_rounds: 100,
                topology: Topology::FullyConnected,
            };
            let mut net = GossipNetwork::new(config, 42);
            for i in 0..10 {
                net.add_agent(format!("agent-{}", i));
            }
            net.simulate_propagation(test_dialect("bench"), "agent-0")
        })
    });

    c.bench_function("gossip/simulate_100_agents", |b| {
        b.iter(|| {
            let config = GossipConfig {
                transmission_probability: 0.8,
                max_rounds: 100,
                topology: Topology::FullyConnected,
            };
            let mut net = GossipNetwork::new(config, 42);
            for i in 0..100 {
                net.add_agent(format!("agent-{}", i));
            }
            net.simulate_propagation(test_dialect("bench"), "agent-0")
        })
    });

    c.bench_function("gossip/simulate_100_agents_ring", |b| {
        b.iter(|| {
            let config = GossipConfig {
                transmission_probability: 0.8,
                max_rounds: 200,
                topology: Topology::Ring,
            };
            let mut net = GossipNetwork::new(config, 42);
            for i in 0..100 {
                net.add_agent(format!("agent-{}", i));
            }
            net.simulate_propagation(test_dialect("bench"), "agent-0")
        })
    });

    c.bench_function("gossip/add_100_agents_fully_connected", |b| {
        b.iter(|| {
            let config = GossipConfig::default();
            let mut net = GossipNetwork::new(config, 42);
            for i in 0..100 {
                net.add_agent(format!("agent-{}", i));
            }
            black_box(&net);
        })
    });

    c.bench_function("gossip/estimate_convergence_100", |b| {
        let config = GossipConfig::default();
        let mut net = GossipNetwork::new(config, 42);
        for i in 0..100 {
            net.add_agent(format!("agent-{}", i));
        }
        b.iter(|| net.estimate_convergence_time())
    });
}

// ---------------------------------------------------------------------------
// Causal verification benchmarks (NFR-201, TEST-251)
// ---------------------------------------------------------------------------

fn bench_causal_verification(c: &mut Criterion) {
    // Build a 10-step linear protocol: begin -> step-1 -> step-2 -> ... -> step-10
    let mut steps = std::collections::BTreeMap::new();
    steps.insert(
        String::from("begin"),
        StepDecl {
            performative: String::from("begin"),
            predecessors: vec![],
            successors: vec![NodeRef::Single(String::from("step-1"))],
        },
    );
    for i in 1..=10 {
        let name = format!("step-{}", i);
        let pred = if i == 1 {
            String::from("begin")
        } else {
            format!("step-{}", i - 1)
        };
        let succ = if i < 10 {
            vec![NodeRef::Single(format!("step-{}", i + 1))]
        } else {
            vec![]
        };
        steps.insert(
            name.clone(),
            StepDecl {
                performative: name,
                predecessors: vec![NodeRef::Single(pred)],
                successors: succ,
            },
        );
    }
    let protocol = CausalProtocol { steps };

    // Populate a store with messages for all steps
    let mut store = ThreadedMessageStore::new();
    let thread = ThreadId(String::from("bench-thread"));
    for i in 1..=10 {
        let hash = ContentHash(format!("hash-{}", i));
        let caused = if i == 1 {
            Some(CausedBy::Begin)
        } else {
            Some(CausedBy::Single(format!("hash-{}", i - 1)))
        };
        let msg = Message::Simple {
            performative: Performative::Custom(format!("step-{}", i)),
            recipient: None,
            content: str_expr("payload"),
            params: vec![],
            thread: Some(String::from("bench-thread")),
            sender: None,
            caused_by: caused,
        };
        store.append(hash, thread.clone(), msg);
    }

    // Benchmark: verify a message with a known predecessor (Valid path)
    let caused_by = CausedBy::Single(String::from("hash-5"));
    c.bench_function("causal/verify_single_valid", |b| {
        b.iter(|| {
            verify_causal(
                black_box("step-6"),
                black_box(Some(&caused_by)),
                black_box(&store),
                black_box(&protocol),
                black_box(&thread),
            )
        })
    });

    // Benchmark: verify begin message (no predecessors)
    c.bench_function("causal/verify_begin", |b| {
        b.iter(|| {
            verify_causal(
                black_box("step-1"),
                black_box(Some(&CausedBy::Begin)),
                black_box(&store),
                black_box(&protocol),
                black_box(&thread),
            )
        })
    });

    // Benchmark: verify message with unknown predecessor (Unknown path)
    let unknown_caused = CausedBy::Single(String::from("hash-unknown"));
    c.bench_function("causal/verify_unknown_predecessor", |b| {
        b.iter(|| {
            verify_causal(
                black_box("step-3"),
                black_box(Some(&unknown_caused)),
                black_box(&store),
                black_box(&protocol),
                black_box(&thread),
            )
        })
    });
}

// ---------------------------------------------------------------------------
// Shape check benchmarks (NFR-203, TEST-253)
// ---------------------------------------------------------------------------

fn bench_shape_check(c: &mut Criterion) {
    // Build a shape constraint with 8 rules (matching NFR-202 scale)
    let shape = ShapeConstraint {
        performative: String::from("track-shipment"),
        rules: vec![
            ShapeRule::Require {
                keyword: String::from("package"),
                type_constraint: Some(TypeConstraint::String),
                children: vec![],
            },
            ShapeRule::Require {
                keyword: String::from("route"),
                type_constraint: Some(TypeConstraint::String),
                children: vec![],
            },
            ShapeRule::Require {
                keyword: String::from("sender"),
                type_constraint: Some(TypeConstraint::Symbol),
                children: vec![],
            },
            ShapeRule::Optional {
                keyword: String::from("priority"),
                type_constraint: Some(TypeConstraint::String),
                default: Some(str_expr("normal")),
                children: vec![],
            },
            ShapeRule::Optional {
                keyword: String::from("weight"),
                type_constraint: Some(TypeConstraint::Number),
                default: None,
                children: vec![],
            },
            ShapeRule::Require {
                keyword: String::from("destination"),
                type_constraint: Some(TypeConstraint::String),
                children: vec![],
            },
            ShapeRule::Optional {
                keyword: String::from("fragile"),
                type_constraint: Some(TypeConstraint::Bool),
                default: None,
                children: vec![],
            },
            ShapeRule::MaxDepth(6),
        ],
    };

    // Message that satisfies the shape
    let msg = SExpr::List(vec![
        sym("track-shipment"),
        SExpr::Atom(Atom::Keyword(String::from("package"))),
        str_expr("PKG-42"),
        SExpr::Atom(Atom::Keyword(String::from("route"))),
        str_expr("A-B"),
        SExpr::Atom(Atom::Keyword(String::from("sender"))),
        sym("@alice"),
        SExpr::Atom(Atom::Keyword(String::from("priority"))),
        str_expr("express"),
        SExpr::Atom(Atom::Keyword(String::from("destination"))),
        str_expr("warehouse-B"),
        SExpr::Atom(Atom::Keyword(String::from("fragile"))),
        SExpr::Atom(Atom::Bool(true)),
    ]);

    c.bench_function("shape/check_8_rules_pass", |b| {
        b.iter(|| shape.check(black_box(&msg)))
    });

    // Message that fails (missing required field)
    let msg_fail = SExpr::List(vec![
        sym("track-shipment"),
        SExpr::Atom(Atom::Keyword(String::from("package"))),
        str_expr("PKG-42"),
        // missing :route, :sender, :destination
    ]);
    c.bench_function("shape/check_8_rules_fail", |b| {
        b.iter(|| shape.check(black_box(&msg_fail)))
    });

    // Nested shape with children rules
    let nested_shape = ShapeConstraint {
        performative: String::from("propose-step"),
        rules: vec![
            ShapeRule::Require {
                keyword: String::from("params"),
                type_constraint: Some(TypeConstraint::List),
                children: vec![
                    ShapeRule::Require {
                        keyword: String::from("target"),
                        type_constraint: Some(TypeConstraint::String),
                        children: vec![],
                    },
                    ShapeRule::Require {
                        keyword: String::from("action"),
                        type_constraint: Some(TypeConstraint::Symbol),
                        children: vec![],
                    },
                ],
            },
            ShapeRule::MaxDepth(4),
        ],
    };
    let nested_msg = SExpr::List(vec![
        sym("propose-step"),
        SExpr::Atom(Atom::Keyword(String::from("params"))),
        SExpr::List(vec![
            SExpr::Atom(Atom::Keyword(String::from("target"))),
            str_expr("server-1"),
            SExpr::Atom(Atom::Keyword(String::from("action"))),
            sym("deploy"),
        ]),
    ]);
    c.bench_function("shape/check_nested_children", |b| {
        b.iter(|| nested_shape.check(black_box(&nested_msg)))
    });
}

// ---------------------------------------------------------------------------
// Hash index benchmarks (TEST-309)
// ---------------------------------------------------------------------------

fn bench_hash_index(c: &mut Criterion) {
    // Pre-populate an index with 1000 entries
    let mut index = HashIndex::with_capacity(1000);
    let thread = ThreadId(String::from("thread-1"));
    for i in 0..1000 {
        index.insert(ContentHash(format!("hash-{}", i)), thread.clone(), i);
    }

    // Benchmark lookup of an existing key
    let lookup_hash = ContentHash(String::from("hash-500"));
    c.bench_function("hash_index/lookup_hit", |b| {
        b.iter(|| index.lookup(black_box(&lookup_hash), black_box(&thread)))
    });

    // Benchmark lookup of a missing key
    let missing_hash = ContentHash(String::from("hash-nonexistent"));
    c.bench_function("hash_index/lookup_miss", |b| {
        b.iter(|| index.lookup(black_box(&missing_hash), black_box(&thread)))
    });

    // Benchmark lookup with wrong thread (thread isolation)
    let wrong_thread = ThreadId(String::from("thread-other"));
    c.bench_function("hash_index/lookup_wrong_thread", |b| {
        b.iter(|| index.lookup(black_box(&lookup_hash), black_box(&wrong_thread)))
    });

    // Benchmark insert (new entry)
    c.bench_function("hash_index/insert_new", |b| {
        let mut idx = HashIndex::with_capacity(1);
        let t = ThreadId(String::from("t"));
        b.iter(|| {
            idx = HashIndex::with_capacity(1);
            idx.insert(
                black_box(ContentHash(String::from("new-hash"))),
                black_box(t.clone()),
                black_box(0),
            )
        })
    });
}

// ---------------------------------------------------------------------------
// Dedup overhead benchmarks (NFR-304, TEST-354)
// ---------------------------------------------------------------------------

fn bench_dedup(c: &mut Criterion) {
    let thread = ThreadId(String::from("dedup-thread"));
    let msg = Message::Simple {
        performative: Performative::Core(CorePerformative::Tell),
        recipient: Some("@bob".into()),
        content: str_expr("hello"),
        params: vec![],
        thread: Some(String::from("dedup-thread")),
        sender: None,
        caused_by: None,
    };

    // Benchmark: append a duplicate (should return false quickly)
    c.bench_function("dedup/append_duplicate", |b| {
        b.iter_batched(
            || {
                let mut store = ThreadedMessageStore::new();
                store.append(
                    ContentHash(String::from("dup-hash")),
                    thread.clone(),
                    msg.clone(),
                );
                store
            },
            |mut store| {
                black_box(store.append(
                    ContentHash(String::from("dup-hash")),
                    thread.clone(),
                    msg.clone(),
                ))
            },
            criterion::BatchSize::SmallInput,
        )
    });

    // Benchmark: append a new message (non-duplicate)
    c.bench_function("dedup/append_new", |b| {
        let mut counter = 0u64;
        b.iter(|| {
            let mut store = ThreadedMessageStore::new();
            counter += 1;
            black_box(store.append(
                ContentHash(format!("unique-{}", counter)),
                thread.clone(),
                msg.clone(),
            ))
        })
    });

    // Benchmark: dedup in a store with 1000 existing entries
    c.bench_function("dedup/append_duplicate_1000_entries", |b| {
        b.iter_batched(
            || {
                let mut store = ThreadedMessageStore::new();
                for i in 0..1000 {
                    store.append(
                        ContentHash(format!("msg-{}", i)),
                        thread.clone(),
                        msg.clone(),
                    );
                }
                store
            },
            |mut store| {
                black_box(store.append(
                    ContentHash(String::from("msg-500")),
                    thread.clone(),
                    msg.clone(),
                ))
            },
            criterion::BatchSize::SmallInput,
        )
    });
}

// ---------------------------------------------------------------------------
// Policy benchmarks (TEST-352: zero mutable state under Reject)
// ---------------------------------------------------------------------------

fn bench_policy(c: &mut Criterion) {
    let reject = UnknownPredecessorPolicy::Reject;

    c.bench_function("policy/reject_valid", |b| {
        b.iter(|| apply_policy(black_box(&VerificationResult::Valid), black_box(&reject)))
    });

    c.bench_function("policy/reject_unknown", |b| {
        b.iter(|| apply_policy(black_box(&VerificationResult::Unknown), black_box(&reject)))
    });

    let buffer = UnknownPredecessorPolicy::buffer(300);
    c.bench_function("policy/buffer_unknown", |b| {
        b.iter(|| apply_policy(black_box(&VerificationResult::Unknown), black_box(&buffer)))
    });
}

// ---------------------------------------------------------------------------
// Criterion groups
// ---------------------------------------------------------------------------

criterion_group!(
    benches,
    bench_r1,
    bench_r2,
    bench_r3,
    bench_template,
    bench_msg_tag,
    bench_eval,
    bench_gossip,
    bench_causal_verification,
    bench_shape_check,
    bench_hash_index,
    bench_dedup,
    bench_policy,
);
criterion_main!(benches);
