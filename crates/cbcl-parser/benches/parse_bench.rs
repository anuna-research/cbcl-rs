use criterion::{black_box, criterion_group, criterion_main, Criterion};

use cbcl_parser::{parse, parse_dialect, parse_message, pipeline};

// ---------------------------------------------------------------------------
// S-expression parsing benchmarks
// ---------------------------------------------------------------------------

fn bench_parse_atom(c: &mut Criterion) {
    c.bench_function("parse/atom_symbol", |b| {
        b.iter(|| parse(black_box("hello")))
    });
    c.bench_function("parse/atom_integer", |b| {
        b.iter(|| parse(black_box("42")))
    });
    c.bench_function("parse/atom_string", |b| {
        b.iter(|| parse(black_box("\"hello world\"")))
    });
    c.bench_function("parse/atom_bool", |b| {
        b.iter(|| parse(black_box("#t")))
    });
    c.bench_function("parse/atom_keyword", |b| {
        b.iter(|| parse(black_box(":thread")))
    });
}

fn bench_parse_list(c: &mut Criterion) {
    c.bench_function("parse/list_small", |b| {
        b.iter(|| parse(black_box("(tell @bob \"hello\")")))
    });
    c.bench_function("parse/list_medium", |b| {
        b.iter(|| {
            parse(black_box(
                "(envelope :from @alice :to @bob :timestamp \"2025-01-15T14:30:00Z\" (tell @bob \"hello world\"))",
            ))
        })
    });
    c.bench_function("parse/list_nested", |b| {
        b.iter(|| {
            parse(black_box(
                "(a (b (c (d (e (f (g (h 42))))))))".to_string().as_str(),
            ))
        })
    });
    // A large flat list with many elements
    let large_flat: String = {
        let mut s = String::from("(");
        for i in 0..100 {
            if i > 0 {
                s.push(' ');
            }
            s.push_str(&format!("item-{}", i));
        }
        s.push(')');
        s
    };
    c.bench_function("parse/list_large_flat_100", |b| {
        b.iter(|| parse(black_box(&large_flat)))
    });
}

// ---------------------------------------------------------------------------
// Message parsing benchmarks
// ---------------------------------------------------------------------------

fn bench_parse_message(c: &mut Criterion) {
    let simple = parse("(tell @bob \"The meeting is at 3pm\")").unwrap();
    c.bench_function("parse_message/simple_tell", |b| {
        b.iter(|| parse_message(black_box(&simple)))
    });

    let ask = parse("(ask @alice \"What is the status?\" :thread \"conv-17\" :timeout 30)").unwrap();
    c.bench_function("parse_message/ask_with_keywords", |b| {
        b.iter(|| parse_message(black_box(&ask)))
    });

    let meta =
        parse("(meta (define test-dialect (cbcl) @author))").unwrap();
    c.bench_function("parse_message/meta_define", |b| {
        b.iter(|| parse_message(black_box(&meta)))
    });

    let meta_query =
        parse("(meta (query (speak? cbcl-planning)))").unwrap();
    c.bench_function("parse_message/meta_query", |b| {
        b.iter(|| parse_message(black_box(&meta_query)))
    });

    let dialect_msg =
        parse("(lang logistics (tell @system \"PKG-123\"))").unwrap();
    c.bench_function("parse_message/dialect", |b| {
        b.iter(|| parse_message(black_box(&dialect_msg)))
    });

    let wrapped =
        parse("(envelope :from @alice :to @bob (tell @bob \"Hello\"))").unwrap();
    c.bench_function("parse_message/wrapped_envelope", |b| {
        b.iter(|| parse_message(black_box(&wrapped)))
    });

    let signed =
        parse("(signed \"base64signature\" (tell @bob \"Verified message\"))").unwrap();
    c.bench_function("parse_message/wrapped_signed", |b| {
        b.iter(|| parse_message(black_box(&signed)))
    });
}

// ---------------------------------------------------------------------------
// Dialect parsing benchmarks
// ---------------------------------------------------------------------------

fn bench_parse_dialect(c: &mut Criterion) {
    let minimal =
        parse("(define test-dialect (cbcl) @test-author)").unwrap();
    c.bench_function("parse_dialect/minimal", |b| {
        b.iter(|| parse_dialect(black_box(&minimal)))
    });

    let full = parse(
        "(define cbcl-planning (cbcl) @planning-authority \
         (extend share-conditional (action precondition effect) (effect share-conditional)) \
         (extend propose-step (step-id action achieves) (effect propose)) \
         (:resource-requirements ((max-depth 16) (max-expansion-size 1024) (verification-time 50))) \
         (:protocol \"ed25519\") \
         (:hash \"sha256:planning-dialect-v1.0-hash\") \
         (:signature planning-consortium-key-2024))",
    )
    .unwrap();
    c.bench_function("parse_dialect/full_planning", |b| {
        b.iter(|| parse_dialect(black_box(&full)))
    });
}

// ---------------------------------------------------------------------------
// Pipeline end-to-end benchmarks
// ---------------------------------------------------------------------------

fn bench_pipeline(c: &mut Criterion) {
    c.bench_function("pipeline/simple_tell", |b| {
        b.iter(|| pipeline::run_pipeline(black_box("(tell @bob \"hello\")")))
    });
    c.bench_function("pipeline/meta_define", |b| {
        b.iter(|| {
            pipeline::run_pipeline(black_box(
                "(meta (define test-dialect (cbcl) @author))",
            ))
        })
    });
    c.bench_function("pipeline/meta_query", |b| {
        b.iter(|| {
            pipeline::run_pipeline(black_box(
                "(meta (query (speak? cbcl-planning)))",
            ))
        })
    });
    c.bench_function("pipeline/custom_performative", |b| {
        b.iter(|| {
            pipeline::run_pipeline(black_box(
                "(share-conditional pickup box-location box-in-hand)",
            ))
        })
    });
    c.bench_function("pipeline/parse_error", |b| {
        b.iter(|| pipeline::run_pipeline(black_box("(unclosed")))
    });
}

// ---------------------------------------------------------------------------
// Criterion groups
// ---------------------------------------------------------------------------

criterion_group!(
    benches,
    bench_parse_atom,
    bench_parse_list,
    bench_parse_message,
    bench_parse_dialect,
    bench_pipeline,
);
criterion_main!(benches);
