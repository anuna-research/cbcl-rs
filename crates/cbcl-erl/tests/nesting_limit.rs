//! SPEC-001 REQ-046 through the BEAM binding (BUG-007): an over-deep frame
//! is an ordinary `parse error` reason from every text NIF's pure core, the
//! next call on the same process still works, and nothing exhausts the
//! stack. A stack overflow in a NIF is not a panic — `catch_pure` cannot
//! contain it — it takes the whole node down, so the refusal must happen in
//! the parser.
//!
//! Every call runs on a 320 KiB thread: BEAM's default dirty-scheduler stack
//! (`+sssdcpu 40` kilowords), smaller than the normal scheduler's, so the
//! test does not lean on a generous `cargo test` thread stack.

use cbcl_erl::{
    admit_pure, define_text_pure, describe_dialect_pure, fold_pure, parse_message_lax_pure,
    parse_message_pure, read_act_pure, read_pure, verify_dialect_pure, verify_message_shape_pure,
};
use cbcl_parser::parser::MAX_NESTING_DEPTH as N;

fn on_scheduler_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(320 * 1024)
        .spawn(f)
        .unwrap()
        .join()
        .expect("no stack overflow")
}

fn tell(depth: usize) -> Vec<u8> {
    format!(
        "(tell @room {}{})",
        "(".repeat(depth - 1),
        ")".repeat(depth - 1)
    )
    .into_bytes()
}

fn reason() -> String {
    format!(
        "at byte {}: list nesting exceeds limit {N}",
        "(tell @room ".len() + N - 1
    )
}

#[test]
fn parse_message_strict_and_lax_refuse_then_recover() {
    on_scheduler_stack(|| {
        let far = format!("(tell @room {}", "(".repeat(1_000_000)).into_bytes();
        for _ in 0..3 {
            for over in [tell(N + 1), far.clone()] {
                let (cat, desc) = parse_message_pure(&over).expect_err("strict");
                assert_eq!(cat, "parse error");
                assert_eq!(desc, reason());
                let lax = parse_message_lax_pure(&over).expect_err("lax");
                assert_eq!(lax, format!("parse error: {}", reason()));
            }
            assert!(parse_message_pure(&tell(N)).is_ok());
            assert!(parse_message_lax_pure(&tell(N)).is_ok());
            assert!(parse_message_pure(b"(tell @room \"hi\")").is_ok());
        }
    });
}

#[test]
fn every_text_nif_core_refuses_an_over_deep_frame() {
    on_scheduler_stack(|| {
        let over = tell(N + 1);
        type Core = fn(&[u8]) -> Result<String, String>;
        let cores: [(&str, Core); 8] = [
            ("read", read_pure),
            ("define_text", define_text_pure),
            ("describe_dialect", describe_dialect_pure),
            ("read_act", read_act_pure),
            ("verify_message_shape", verify_message_shape_pure),
            ("fold", fold_pure),
            ("admit", admit_pure),
            ("verify_dialect", |b| {
                verify_dialect_pure(b).map(|()| String::new())
            }),
        ];
        for (name, core) in cores {
            let err = core(&over).expect_err(name);
            assert!(err.contains(&reason()), "{name}: {err}");
            assert!(
                read_pure(b"(tell @room \"hi\")").is_ok(),
                "{name}: recovery"
            );
        }
        let tree = read_pure(&tell(N)).expect("read at the limit");
        assert!(tree.starts_with("[\"tell\",\"@room\",[[["));
    });
}
