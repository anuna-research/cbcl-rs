#![forbid(unsafe_code)]
use cbcl_quorum_e2e::{client, model::Result, node};
fn execute() -> Result<()> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    if matches!(
        args.first().map(String::as_str),
        Some("validator" | "recover")
    ) {
        if args.len() != 3 || args[1] != "--config" {
            return Err("internal node usage: validator|recover --config PATH".into());
        }
        let result = node::run(std::path::Path::new(&args[2]), args[0] == "recover")?;
        println!(
            "{}",
            serde_json::to_string(&result).map_err(|e| e.to_string())?
        );
    } else {
        client::run(&args)?;
    }
    Ok(())
}
fn main() {
    if let Err(error) = execute() {
        eprintln!("quorum-e2e: {error}");
        std::process::exit(1);
    }
}
