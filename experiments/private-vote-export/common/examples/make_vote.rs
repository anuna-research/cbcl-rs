#[path = "../tests/support/mod.rs"]
mod support;
use std::{fs, io::Read, path::PathBuf};
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args().skip(1);
    let dir = PathBuf::from(
        args.next()
            .ok_or("usage: make_vote OUTPUTDIR [--replacement]")?,
    );
    let replacement = match args.next().as_deref() {
        None => false,
        Some("--replacement") => true,
        _ => return Err("unknown option".into()),
    };
    if args.next().is_some() {
        return Err("extra argument".into());
    }
    let mut input = support::fixture(replacement);
    // Random per export, deliberately never included in expected public output.
    fs::File::open("/dev/urandom")?.read_exact(&mut input.salt)?;
    support::resign(&mut input);
    let bytes = serde_json::to_vec_pretty(&input)?;
    let journal = private_vote_common::compute(&bytes).map_err(std::io::Error::other)?;
    fs::create_dir_all(&dir)?;
    fs::write(dir.join("input.json"), bytes)?;
    fs::write(
        dir.join("expected.json"),
        serde_json::to_vec_pretty(&journal)?,
    )?;
    Ok(())
}
