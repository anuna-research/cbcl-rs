//! cbcl-cli: Command-line interface for CBCL.

use std::io::{self, BufRead, Read, Write};

use cbcl_core::gossip::{GossipConfig, GossipNetwork, Topology};
use cbcl_core::prelude::*;
use cbcl_core::serializer::serialize;
use cbcl_core::{r1, r2, r3};
use cbcl_parser::{parse, parse_dialect, run_pipeline, PipelineResult};
use clap::{Parser, Subcommand};

#[derive(Parser)]
#[command(name = "cbcl", about = "CBCL communication language toolkit")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Parse and validate a CBCL message, outputting the result as JSON
    Parse {
        /// Input S-expression (reads from stdin if omitted)
        input: Option<String>,
        /// Output raw S-expression instead of JSON
        #[arg(long)]
        sexpr: bool,
    },
    /// Verify a dialect definition against R1/R2/R3 safety constraints
    Verify {
        /// Input dialect definition (reads from stdin if omitted)
        input: Option<String>,
    },
    /// Run an interactive agent REPL
    Agent {
        /// Agent identifier
        #[arg(short, long, default_value = "@user")]
        id: String,
    },
    /// Simulate gossip dialect propagation
    Simulate {
        /// Number of agents in the network
        #[arg(short = 'n', long, default_value_t = 10)]
        agents: u32,
        /// Transmission probability (0.0–1.0)
        #[arg(short = 'p', long, default_value_t = 0.8)]
        probability: f64,
        /// Maximum rounds before timeout
        #[arg(short, long, default_value_t = 100)]
        max_rounds: u32,
        /// Network topology: fully-connected, ring, or random
        #[arg(short, long, default_value = "fully-connected")]
        topology: String,
        /// Dialect definition to propagate (reads from stdin if omitted)
        input: Option<String>,
        /// RNG seed for deterministic simulation
        #[arg(long, default_value_t = 1234567)]
        seed: u64,
    },
}

fn main() {
    let cli = Cli::parse();

    let exit_code = match cli.command {
        Command::Parse { input, sexpr } => cmd_parse(input, sexpr),
        Command::Verify { input } => cmd_verify(input),
        Command::Agent { id } => cmd_agent(id),
        Command::Simulate {
            agents,
            probability,
            max_rounds,
            topology,
            input,
            seed,
        } => cmd_simulate(agents, probability, max_rounds, topology, input, seed),
    };

    std::process::exit(exit_code);
}

fn read_input(arg: Option<String>) -> String {
    if let Some(input) = arg {
        input
    } else {
        let mut buf = String::new();
        io::stdin()
            .read_to_string(&mut buf)
            .expect("failed to read stdin");
        buf
    }
}

// ---------------------------------------------------------------------------
// parse
// ---------------------------------------------------------------------------

fn cmd_parse(input: Option<String>, sexpr_mode: bool) -> i32 {
    let input = read_input(input);

    if sexpr_mode {
        // Raw S-expression parse + serialize round-trip
        match parse(&input) {
            Ok(expr) => {
                println!("{}", serialize(&expr));
                0
            }
            Err(e) => {
                eprintln!("parse error: {e}");
                1
            }
        }
    } else {
        // Full pipeline: parse → parse_message → validate
        match run_pipeline(&input) {
            PipelineResult::Success(msg) => {
                match serde_json::to_string_pretty(&msg) {
                    Ok(json) => println!("{json}"),
                    Err(_) => println!("{msg:?}"),
                }
                0
            }
            PipelineResult::ParseError(e) => {
                eprintln!("parse error: {e}");
                1
            }
            PipelineResult::ValidationError(e) => {
                eprintln!("validation error: {e}");
                1
            }
        }
    }
}

// ---------------------------------------------------------------------------
// verify
// ---------------------------------------------------------------------------

fn cmd_verify(input: Option<String>) -> i32 {
    let input = read_input(input);

    let expr = match parse(&input) {
        Ok(e) => e,
        Err(e) => {
            eprintln!("parse error: {e}");
            return 1;
        }
    };

    let dialect = match parse_dialect(&expr) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("dialect parse error: {e}");
            return 1;
        }
    };

    let mut violations = Vec::new();

    // R1: No recursion
    if !r1::verify_r1_dialect(&dialect) {
        for name in r1::r1_violations(&dialect) {
            violations.push(format!(
                "R1: performative '{}' contains self-reference",
                name
            ));
        }
    }

    // R2: Resource bounds
    if !r2::verify_r2(&dialect) {
        violations.push(format!(
            "R2: invalid resource bounds (depth={}, expansion={}, time={}ms)",
            dialect.resources.max_depth,
            dialect.resources.max_expansion_size,
            dialect.resources.verification_time_ms
        ));
    }

    // R3: Core preservation
    if !r3::verify_r3(&dialect) {
        for name in r3::r3_violations(&dialect) {
            violations.push(format!("R3: redefines core performative '{}'", name));
        }
    }

    if violations.is_empty() {
        println!(
            "dialect '{}' passed all safety checks (R1, R2, R3)",
            dialect.name
        );
        println!("  performatives: {}", dialect.performatives.len());
        println!(
            "  resource bounds: depth={}, expansion={}, time={}ms",
            dialect.resources.max_depth,
            dialect.resources.max_expansion_size,
            dialect.resources.verification_time_ms
        );
        0
    } else {
        eprintln!("dialect '{}' failed verification:", dialect.name);
        for v in &violations {
            eprintln!("  - {v}");
        }
        1
    }
}

// ---------------------------------------------------------------------------
// agent REPL
// ---------------------------------------------------------------------------

fn cmd_agent(id: String) -> i32 {
    let mut agent = Agent::new(&id);
    let stdout = io::stdout();
    let stdin = io::stdin();

    println!("CBCL Agent REPL ({})", id);
    println!("Commands: .beliefs, .dialects, .queue, .install <dialect-sexpr>, .quit");
    println!("Enter CBCL messages to evaluate them.");
    println!();

    loop {
        print!("{}> ", agent.id());
        if stdout.lock().flush().is_err() {
            break;
        }

        let mut line = String::new();
        match stdin.lock().read_line(&mut line) {
            Ok(0) => break, // EOF
            Ok(_) => {}
            Err(e) => {
                eprintln!("read error: {e}");
                break;
            }
        }

        let line = line.trim();
        if line.is_empty() {
            continue;
        }

        match line {
            ".quit" | ".exit" | ".q" => break,
            ".beliefs" => {
                if agent.beliefs().is_empty() {
                    println!("  (no beliefs)");
                } else {
                    for belief in agent.beliefs() {
                        println!("  {}", serialize(belief));
                    }
                }
            }
            ".dialects" => {
                let reg = agent.dialect_registry();
                for i in 0..reg.len() {
                    if let Some(d) = reg.get(i) {
                        println!(
                            "  [{}] {} ({} performatives)",
                            i,
                            d.name,
                            d.performatives.len()
                        );
                    }
                }
            }
            ".queue" => {
                if agent.message_queue().is_empty() {
                    println!("  (empty queue)");
                } else {
                    for (i, msg) in agent.message_queue().iter().enumerate() {
                        println!("  [{}] {:?}", i, msg);
                    }
                }
            }
            _ if line.starts_with(".install ") => {
                let dialect_src = &line[".install ".len()..];
                match parse(dialect_src) {
                    Ok(expr) => match parse_dialect(&expr) {
                        Ok(dialect) => match agent.install_dialect(dialect) {
                            Ok(()) => println!("  dialect installed"),
                            Err(e) => eprintln!("  install error: {e}"),
                        },
                        Err(e) => eprintln!("  dialect parse error: {e}"),
                    },
                    Err(e) => eprintln!("  parse error: {e}"),
                }
            }
            _ => {
                // Try to parse and evaluate a message
                match run_pipeline(line) {
                    PipelineResult::Success(msg) => match agent.evaluate_and_apply(&msg) {
                        Ok(result) => {
                            println!("  expanded: {}", serialize(&result.expanded));
                            for effect in &result.effects {
                                println!("  effect: {:?}", effect);
                            }
                            if let Some(ref thread) = result.thread {
                                println!("  thread: {thread}");
                            }
                        }
                        Err(e) => eprintln!("  eval error: {e}"),
                    },
                    PipelineResult::ParseError(e) => eprintln!("  parse error: {e}"),
                    PipelineResult::ValidationError(e) => eprintln!("  validation error: {e}"),
                }
            }
        }
    }

    0
}

// ---------------------------------------------------------------------------
// simulate
// ---------------------------------------------------------------------------

fn cmd_simulate(
    agent_count: u32,
    probability: f64,
    max_rounds: u32,
    topology_str: String,
    input: Option<String>,
    seed: u64,
) -> i32 {
    let topology = match topology_str.as_str() {
        "fully-connected" | "full" => Topology::FullyConnected,
        "ring" => Topology::Ring,
        s if s.starts_with("random") => {
            // Parse "random" or "random:0.5"
            let p = s
                .strip_prefix("random:")
                .and_then(|v| v.parse::<f64>().ok())
                .unwrap_or(0.5);
            Topology::Random(p)
        }
        _ => {
            eprintln!("unknown topology: {topology_str}");
            eprintln!("valid options: fully-connected, ring, random, random:<p>");
            return 2;
        }
    };

    if !(0.0..=1.0).contains(&probability) {
        eprintln!("transmission probability must be between 0.0 and 1.0");
        return 2;
    }

    let input = read_input(input);

    let expr = match parse(&input) {
        Ok(e) => e,
        Err(e) => {
            eprintln!("parse error: {e}");
            return 1;
        }
    };

    let dialect = match parse_dialect(&expr) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("dialect parse error: {e}");
            return 1;
        }
    };

    let dialect_name = dialect.name.clone();

    let config = GossipConfig {
        transmission_probability: probability,
        max_rounds,
        topology,
    };

    let mut network = GossipNetwork::new(config, seed);

    for i in 0..agent_count {
        network.add_agent(format!("agent-{i}"));
    }

    println!(
        "Gossip simulation: {} agents, dialect '{}'",
        agent_count, dialect_name
    );
    println!("  topology: {topology_str}, p={probability}, max_rounds={max_rounds}, seed={seed}");
    println!(
        "  estimated convergence: {} rounds",
        network.estimate_convergence_time()
    );
    println!();

    match network.simulate_propagation(dialect, "agent-0") {
        Some(result) => {
            if result.successful {
                println!(
                    "Propagation complete in {} round(s) (coverage: {:.1}%)",
                    result.rounds,
                    result.final_coverage * 100.0
                );
            } else {
                println!(
                    "Propagation timed out after {} round(s) (coverage: {:.1}%)",
                    result.rounds,
                    result.final_coverage * 100.0
                );
            }

            let stats = network.stats();
            println!("  total rounds: {}", stats.total_rounds);
            println!("  successful: {}", stats.successful_propagations);
            println!("  failed: {}", stats.failed_propagations);

            if result.successful {
                0
            } else {
                1
            }
        }
        None => {
            eprintln!("failed to start propagation (agent-0 not found or dialect already active)");
            1
        }
    }
}
