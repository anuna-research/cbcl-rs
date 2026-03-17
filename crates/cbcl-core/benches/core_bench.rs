use criterion::{black_box, criterion_group, criterion_main, Criterion};

use cbcl_core::dialect::{Dialect, DialectRegistry, PerformativeDef, ResourceBounds};
use cbcl_core::evaluator;
use cbcl_core::gossip::{GossipConfig, GossipNetwork, Topology};
use cbcl_core::message::{CorePerformative, Message, Performative};
use cbcl_core::msg_tag;
use cbcl_core::r1;
use cbcl_core::r2::{self, ResourceState};
use cbcl_core::r3;
use cbcl_core::sexpr::{Atom, SExpr};
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
        name: String::from(name),
        extends: vec![String::from("cbcl")],
        author: None,
        performatives: perfs,
        resources: valid_bounds(),
        examples: vec![],
        signature: None,
        hash: None,
        protocol: None,
    }
}

fn make_perf(name: &str, template_str: &str) -> PerformativeDef {
    PerformativeDef {
        name: String::from(name),
        params: vec![],
        template: parse(template_str),
    }
}

fn test_dialect(name: &str) -> Dialect {
    Dialect {
        name: String::from(name),
        extends: Vec::new(),
        author: None,
        performatives: vec![PerformativeDef {
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
        recipient: Some(String::from("@bob")),
        content: str_expr("hello"),
        params: Vec::new(),
        thread: None,
        sender: None,
    };
    c.bench_function("eval/tell", |b| {
        b.iter(|| evaluator::evaluate(black_box(&tell_msg), black_box(&registry)))
    });

    let ask_msg = Message::Simple {
        performative: Performative::Core(CorePerformative::Ask),
        recipient: Some(String::from("@alice")),
        content: str_expr("what time?"),
        params: Vec::new(),
        thread: None,
        sender: None,
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
            name: String::from("logistics"),
            extends: vec![String::from("cbcl")],
            author: None,
            performatives: vec![PerformativeDef {
                name: String::from("ship"),
                params: vec![sym("package"), sym("destination")],
                template: parse("(effect dispatch-shipment)"),
            }],
            resources: valid_bounds(),
            examples: Vec::new(),
            signature: None,
            hash: None,
            protocol: None,
        })
        .unwrap();

    let ship_msg = Message::Simple {
        performative: Performative::Custom(String::from("ship")),
        recipient: None,
        content: str_expr("PKG-123"),
        params: vec![sym("warehouse-A")],
        thread: None,
        sender: None,
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
);
criterion_main!(benches);
