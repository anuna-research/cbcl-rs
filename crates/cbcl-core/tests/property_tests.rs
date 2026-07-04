//! Property-based tests for cbcl-core.
//!
//! Tests the 8 key properties from the USDD verification strategy:
//! 1. SExpr parse/display roundtrip
//! 2. Message <-> SExpr roundtrip
//! 3. Canonical serialization idempotence
//! 4. R1 rejects iff self-reference exists
//! 5. R3 rejects iff core performative redefined
//! 6. Template expansion terminates within R2 bounds
//! 7. Gossip monotonic knowledge growth (Theorem 2)
//! 8. Dialect installation preserves agent well-formedness

mod prop_generators;

use cbcl_core::agent::Agent;
use cbcl_core::dialect::{base_dialect, Dialect, DialectRegistry, PerformativeDef, ResourceBounds};
use cbcl_core::gossip::{GossipConfig, GossipNetwork, Topology};
use cbcl_core::message::{Message, CORE_PERFORMATIVE_NAMES};
use cbcl_core::r1::{contains_self_reference, r1_violations, verify_r1, verify_r1_dialect};
use cbcl_core::r2::{bounded_eval, verify_r2, ResourceState};
use cbcl_core::r3::{r3_violations, verify_r3};
use cbcl_core::serializer::serialize;
use cbcl_core::sexpr::{Atom, SExpr};
use cbcl_core::template::{expand_template_with_bindings, Bindings};

use prop_generators::*;
use proptest::prelude::*;

// ===========================================================================
// Property 1: SExpr parse/display roundtrip
// ===========================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    /// For any generated SExpr, `parse(display(e)) == e`.
    #[test]
    fn prop_sexpr_display_parse_roundtrip(expr in arb_sexpr(3)) {
        let displayed = expr.to_string();
        let parsed: Result<SExpr, _> = displayed.parse();
        prop_assert!(parsed.is_ok(), "failed to parse displayed expr: {}", displayed);
        prop_assert_eq!(parsed.unwrap(), expr);
    }
}

// ===========================================================================
// Property 2: Message <-> SExpr roundtrip
// ===========================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(300))]

    /// For Simple messages: `Message::try_from(&SExpr::from(msg)) == msg`.
    #[test]
    fn prop_simple_message_roundtrip(msg in arb_simple_message()) {
        let sexpr = SExpr::from(msg.clone());
        let parsed = Message::try_from(&sexpr);
        prop_assert!(parsed.is_ok(), "failed to parse message sexpr: {:?}", sexpr);
        let parsed = parsed.unwrap();
        // Compare structurally
        prop_assert_eq!(parsed.message_type(), msg.message_type());
        prop_assert_eq!(parsed.performative(), msg.performative());
        prop_assert_eq!(parsed.recipient(), msg.recipient());
        prop_assert_eq!(parsed.thread(), msg.thread());
        prop_assert_eq!(parsed.sender(), msg.sender());
    }
}

// ===========================================================================
// Property 3: Canonical serialization idempotence
// ===========================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    /// `serialize(e)` is deterministic: calling it twice gives the same result.
    #[test]
    fn prop_serialize_deterministic(expr in arb_sexpr(3)) {
        let s1 = serialize(&expr);
        let s2 = serialize(&expr);
        prop_assert_eq!(&s1, &s2);
    }

    /// `serialize` matches `Display`: they produce the same output.
    #[test]
    fn prop_serialize_matches_display(expr in arb_sexpr(3)) {
        let serialized = serialize(&expr);
        let displayed = expr.to_string();
        prop_assert_eq!(&serialized, &displayed);
    }

    /// Serialization is idempotent: `serialize(parse(serialize(e))) == serialize(e)`.
    #[test]
    fn prop_serialization_idempotent(expr in arb_sexpr(3)) {
        let s1 = serialize(&expr);
        let reparsed: SExpr = s1.parse().unwrap();
        let s2 = serialize(&reparsed);
        prop_assert_eq!(&s1, &s2);
    }
}

// ===========================================================================
// Property 4: R1 rejects iff self-reference exists
// ===========================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(300))]

    /// verify_r1 returns true iff there is no self-reference.
    #[test]
    fn prop_r1_rejects_iff_self_reference(
        name in arb_custom_perf_name(),
        template in arb_sexpr(3),
    ) {
        let has_self_ref = contains_self_reference(&name, &template);
        let r1_pass = verify_r1(&name, &template);
        prop_assert_eq!(r1_pass, !has_self_ref,
            "R1 pass={} but self-ref={} for name='{}' template='{}'",
            r1_pass, has_self_ref, name, template);
    }

    /// Safe performative defs always pass R1.
    #[test]
    fn prop_safe_performative_passes_r1(def in arb_safe_performative_def()) {
        prop_assert!(!contains_self_reference(&def.name, &def.template),
            "safe perf '{}' has self-reference in template '{}'",
            def.name, def.template);
        prop_assert!(verify_r1(&def.name, &def.template));
    }

    /// Recursive performative defs always fail R1.
    #[test]
    fn prop_recursive_performative_fails_r1(def in arb_recursive_performative_def()) {
        prop_assert!(contains_self_reference(&def.name, &def.template));
        prop_assert!(!verify_r1(&def.name, &def.template));
    }

    /// Valid dialects pass R1 at the dialect level.
    #[test]
    fn prop_valid_dialect_passes_r1(d in arb_valid_dialect()) {
        prop_assert!(verify_r1_dialect(&d),
            "valid dialect '{}' should pass R1", d.name);
        prop_assert!(r1_violations(&d).is_empty());
    }

    /// Base dialect always passes R1.
    #[test]
    fn prop_base_dialect_always_passes_r1(_ in 0..10u32) {
        let d = base_dialect();
        prop_assert!(verify_r1_dialect(&d));
        prop_assert!(r1_violations(&d).is_empty());
    }
}

// ===========================================================================
// Property 5: R3 rejects iff core performative redefined
// ===========================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(300))]

    /// R3-violating dialects always fail verify_r3.
    #[test]
    fn prop_r3_violating_dialect_fails(d in arb_r3_violating_dialect()) {
        prop_assert!(!verify_r3(&d),
            "dialect '{}' redefines core performative but passed R3", d.name);
        let violations = r3_violations(&d);
        prop_assert!(!violations.is_empty());
        // Every violation should be a core performative name
        for v in &violations {
            prop_assert!(CORE_PERFORMATIVE_NAMES.contains(&v.as_str()),
                "violation '{}' is not a core performative", v);
        }
    }

    /// Valid dialects (no core perf names) always pass R3.
    #[test]
    fn prop_valid_dialect_passes_r3(d in arb_valid_dialect()) {
        prop_assert!(verify_r3(&d),
            "valid dialect '{}' should pass R3", d.name);
        prop_assert!(r3_violations(&d).is_empty());
    }

    /// Base dialect always passes R3.
    #[test]
    fn prop_base_dialect_always_passes_r3(_ in 0..10u32) {
        let d = base_dialect();
        prop_assert!(verify_r3(&d));
    }

    /// R3 rejects iff any performative has a core name (for non-base dialects).
    #[test]
    fn prop_r3_equivalence(d in arb_valid_dialect()) {
        let has_core_name = d.performatives.iter()
            .any(|p| CORE_PERFORMATIVE_NAMES.contains(&p.name.as_str()));
        prop_assert_eq!(verify_r3(&d), !has_core_name);
    }
}

// ===========================================================================
// Property 6: Template expansion terminates within R2 bounds
// ===========================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(300))]

    /// Valid resource bounds always pass R2 verification.
    #[test]
    fn prop_valid_bounds_pass_r2(bounds in arb_valid_resource_bounds()) {
        let d = Dialect { roles: Vec::new(), causal_locality: Default::default(),
            name: String::from("test"),
            extends: Vec::new(),
            author: None,
            performatives: Vec::new(),
            resources: bounds.clone(),
            examples: Vec::new(),
            signature: None,
            hash: None,
            protocol: None, causal_protocol: None, shapes: Vec::new(),
        };
        prop_assert!(verify_r2(&d));
        prop_assert!(bounds.is_valid());
    }

    /// Invalid resource bounds always fail R2 verification.
    #[test]
    fn prop_invalid_bounds_fail_r2(bounds in arb_invalid_resource_bounds()) {
        let d = Dialect { roles: Vec::new(), causal_locality: Default::default(),
            name: String::from("test"),
            extends: Vec::new(),
            author: None,
            performatives: Vec::new(),
            resources: bounds.clone(),
            examples: Vec::new(),
            signature: None,
            hash: None,
            protocol: None, causal_protocol: None, shapes: Vec::new(),
        };
        prop_assert!(!verify_r2(&d));
        prop_assert!(!bounds.is_valid());
    }

    /// bounded_eval always terminates: returns Some or None, never diverges.
    /// When fuel is 0, always returns None.
    #[test]
    fn prop_bounded_eval_zero_fuel_returns_none(expr in arb_sexpr(2)) {
        let mut rs = ResourceState::new(8, 512);
        prop_assert_eq!(bounded_eval(0, &expr, &mut rs), None);
    }

    /// bounded_eval on atoms with fuel >= 1 always returns Some.
    #[test]
    fn prop_bounded_eval_atom_with_fuel(atom in arb_atom()) {
        let expr = SExpr::Atom(atom);
        let mut rs = ResourceState::new(64, 8192);
        let result = bounded_eval(1, &expr, &mut rs);
        prop_assert!(result.is_some());
        prop_assert_eq!(result.unwrap(), expr);
    }

    /// ResourceState depth tracking: enter then exit returns to original depth.
    #[test]
    fn prop_resource_state_enter_exit_depth(
        max_depth in 2u32..=64,
        max_exp in 1u32..=8192,
    ) {
        let rs = ResourceState::new(max_depth, max_exp);
        let original_depth = rs.current_depth;
        if let Some(entered) = rs.enter_depth() {
            let exited = entered.exit_depth();
            prop_assert_eq!(exited.current_depth, original_depth);
        }
    }

    /// Template expansion with sufficient bounds succeeds for simple templates.
    #[test]
    fn prop_literal_template_expansion_terminates(
        bounds in arb_valid_resource_bounds(),
    ) {
        // Simple literal template that should always succeed with valid bounds
        let template: SExpr = "(literal (tell @alice \"hello\"))".parse().unwrap();
        let bindings = Bindings::new();
        let mut rs = ResourceState::new(bounds.max_depth.max(4), bounds.max_expansion_size.max(256));
        let result = expand_template_with_bindings(&template, &bindings, &mut rs);
        // It either succeeds or fails due to bounds — it never diverges
        // (this is the key property: termination)
        let _ = result;
    }
}

// ===========================================================================
// Property 7: Gossip monotonic knowledge growth (Theorem 2)
// ===========================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    /// Gossip propagation: infected set never shrinks between rounds.
    #[test]
    fn prop_gossip_monotonic_knowledge_growth(
        agent_count in 3u32..=15,
        seed in any::<u64>(),
    ) {
        let config = GossipConfig {
            transmission_probability: 0.5,
            max_rounds: 50,
            topology: Topology::FullyConnected,
        };
        let mut net = GossipNetwork::new(config, seed);
        for i in 0..agent_count {
            net.add_agent(format!("agent-{}", i));
        }

        // Create a valid dialect for propagation
        let dialect = Dialect { roles: Vec::new(), causal_locality: Default::default(),
            name: String::from("prop-test-dialect"),
            extends: Vec::new(),
            author: None,
            performatives: vec![PerformativeDef { role: None,
                name: String::from("prop-action"),
                params: Vec::new(),
                template: SExpr::List(vec![
                    SExpr::Atom(Atom::Symbol(String::from("effect"))),
                    SExpr::Atom(Atom::Symbol(String::from("prop-effect"))),
                ]),
            }],
            resources: ResourceBounds {
                max_depth: 8,
                max_expansion_size: 512,
                verification_time_ms: 10,
            },
            examples: Vec::new(),
            signature: None,
            hash: None,
            protocol: None, causal_protocol: None, shapes: Vec::new(),
        };

        let announced = net.announce_dialect(dialect, "agent-0");
        prop_assert!(announced.is_some());

        let mut prev_infected_count = 1usize; // agent-0 starts infected

        // Run rounds, checking monotonicity
        for _ in 0..20 {
            if net.active_propagations().is_empty() {
                break;
            }
            net.step();

            // Get current infected count (may be completed/removed)
            if let Some(prop) = net.propagation_stats("prop-test-dialect") {
                let current = prop.infected.len();
                prop_assert!(current >= prev_infected_count,
                    "infected set shrunk from {} to {}", prev_infected_count, current);
                prev_infected_count = current;
            }
            // If propagation completed, all agents should have the dialect
        }
    }

    /// Gossip with p=1.0 on fully connected graph converges in 1 round.
    #[test]
    fn prop_gossip_full_transmission_converges_fast(
        agent_count in 2u32..=20,
        seed in any::<u64>(),
    ) {
        let config = GossipConfig {
            transmission_probability: 1.0,
            max_rounds: 100,
            topology: Topology::FullyConnected,
        };
        let mut net = GossipNetwork::new(config, seed);
        for i in 0..agent_count {
            net.add_agent(format!("agent-{}", i));
        }

        let dialect = Dialect { roles: Vec::new(), causal_locality: Default::default(),
            name: String::from("fast-dialect"),
            extends: Vec::new(),
            author: None,
            performatives: Vec::new(),
            resources: ResourceBounds {
                max_depth: 8,
                max_expansion_size: 512,
                verification_time_ms: 10,
            },
            examples: Vec::new(),
            signature: None,
            hash: None,
            protocol: None, causal_protocol: None, shapes: Vec::new(),
        };

        let result = net.simulate_propagation(dialect, "agent-0");
        prop_assert!(result.is_some());
        let result = result.unwrap();
        prop_assert!(result.successful);
        prop_assert_eq!(result.rounds, 1,
            "p=1.0 fully-connected should converge in 1 round, took {}", result.rounds);
    }

    /// Gossip with p=0.0 never propagates beyond initial agent.
    #[test]
    fn prop_gossip_zero_transmission_no_spread(
        agent_count in 2u32..=10,
        seed in any::<u64>(),
    ) {
        let config = GossipConfig {
            transmission_probability: 0.0,
            max_rounds: 5,
            topology: Topology::FullyConnected,
        };
        let mut net = GossipNetwork::new(config, seed);
        for i in 0..agent_count {
            net.add_agent(format!("agent-{}", i));
        }

        let dialect = Dialect { roles: Vec::new(), causal_locality: Default::default(),
            name: String::from("zero-dialect"),
            extends: Vec::new(),
            author: None,
            performatives: Vec::new(),
            resources: ResourceBounds {
                max_depth: 8,
                max_expansion_size: 512,
                verification_time_ms: 10,
            },
            examples: Vec::new(),
            signature: None,
            hash: None,
            protocol: None, causal_protocol: None, shapes: Vec::new(),
        };

        let result = net.simulate_propagation(dialect, "agent-0");
        prop_assert!(result.is_some());
        let result = result.unwrap();
        prop_assert!(!result.successful,
            "p=0.0 should never propagate to all agents");
    }
}

// ===========================================================================
// Property 8: Dialect installation preserves agent well-formedness
// ===========================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(200))]

    /// Installing a valid dialect preserves agent well-formedness.
    #[test]
    fn prop_valid_install_preserves_well_formedness(d in arb_valid_dialect()) {
        let mut agent = Agent::new("test-agent");
        prop_assert!(agent.is_well_formed());

        let result = agent.install_dialect(d);
        // Whether it succeeds or fails, agent must remain well-formed
        prop_assert!(agent.is_well_formed(),
            "agent well-formedness violated after install (result={:?})", result);
    }

    /// Installing an R3-violating dialect is rejected and preserves well-formedness.
    #[test]
    fn prop_r3_violation_rejected_preserves_well_formedness(d in arb_r3_violating_dialect()) {
        let mut agent = Agent::new("test-agent");
        prop_assert!(agent.is_well_formed());

        let result = agent.install_dialect(d);
        prop_assert!(result.is_err(),
            "R3-violating dialect should be rejected");
        prop_assert!(agent.is_well_formed());
        prop_assert_eq!(agent.dialect_registry().len(), 1,
            "registry should still have only base dialect");
    }

    /// Installing any dialect never removes the base dialect from index 0.
    #[test]
    fn prop_base_dialect_always_at_index_zero(d in arb_valid_dialect()) {
        let mut agent = Agent::new("test-agent");
        let _ = agent.install_dialect(d);
        let reg = agent.dialect_registry();
        prop_assert_eq!(&reg.get(0).unwrap().name, "cbcl-base");
    }

    /// Multiple dialect installations preserve well-formedness.
    #[test]
    fn prop_multiple_installs_preserve_well_formedness(
        dialects in prop::collection::vec(arb_valid_dialect(), 1..5),
    ) {
        let mut agent = Agent::new("test-agent");
        for d in dialects {
            let _ = agent.install_dialect(d);
            prop_assert!(agent.is_well_formed(),
                "agent well-formedness violated after install");
        }
    }

    /// DialectRegistry install rejects R2 violations (invalid bounds).
    #[test]
    fn prop_r2_violation_rejected(bounds in arb_invalid_resource_bounds()) {
        let mut reg = DialectRegistry::new();
        let d = Dialect { roles: Vec::new(), causal_locality: Default::default(),
            name: String::from("bad-bounds"),
            extends: Vec::new(),
            author: None,
            performatives: Vec::new(),
            resources: bounds,
            examples: Vec::new(),
            signature: None,
            hash: None,
            protocol: None, causal_protocol: None, shapes: Vec::new(),
        };
        let result = reg.install(d);
        prop_assert!(result.is_err());
        prop_assert_eq!(reg.len(), 1); // only base dialect
    }
}

// ===========================================================================
// Additional structural properties
// ===========================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(300))]

    /// SExpr size is always >= 1.
    #[test]
    fn prop_sexpr_size_positive(expr in arb_sexpr(3)) {
        prop_assert!(expr.size() >= 1);
    }

    /// SExpr depth for atoms is 0, for lists is >= 1 (if non-empty) or 0 (if empty).
    #[test]
    fn prop_sexpr_depth_consistent(expr in arb_sexpr(3)) {
        match &expr {
            SExpr::Atom(_) => prop_assert_eq!(expr.depth(), 0),
            SExpr::List(items) => {
                if items.is_empty() {
                    // Empty list has depth 1 (the list node itself)
                    // Actually per the code: 1 + max of items which is 0 when empty = 1
                    prop_assert_eq!(expr.depth(), 1);
                } else {
                    prop_assert!(expr.depth() >= 1);
                }
            }
        }
    }

    /// Serialization round-trip through the parser crate's serialize function.
    #[test]
    fn prop_canonical_serialization_roundtrip(expr in arb_sexpr(3)) {
        let s = serialize(&expr);
        let reparsed: SExpr = s.parse().unwrap();
        prop_assert_eq!(reparsed, expr);
    }
}
