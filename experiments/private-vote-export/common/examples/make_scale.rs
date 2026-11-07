#[path = "../tests/support/mod.rs"]
mod support;
use cbcl_core::{intend::canonical_text, state::Act};
use private_vote_common::{compute, Record, MAX_MESSAGES};
use std::{fs, io::Read, path::PathBuf};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args().skip(1);
    let dir = PathBuf::from(
        args.next()
            .ok_or("usage: make_scale OUTPUTDIR [TOTAL_MESSAGES=16]")?,
    );
    let total: usize = args.next().map(|s| s.parse()).transpose()?.unwrap_or(16);
    if args.next().is_some() || !(4..=MAX_MESSAGES).contains(&total) {
        return Err("total messages must be 4..32; no extra arguments".into());
    }
    let mut input = support::fixture(false);
    let opener = cbcl_parser::parse_message(
        &cbcl_parser::parse(&input.messages[0].canonical)
            .map_err(|e| std::io::Error::other(e.to_string()))?,
    )
    .map_err(std::io::Error::other)?;
    let address = Act::from_message(opener, "@alice")
        .map_err(std::io::Error::other)?
        .address;
    while input.messages.len() < total {
        let number = input.messages.len();
        let signer = number % input.participants.len();
        let label = &input.participants[signer].label;
        let raw = format!(
            "(lang private-vote (discuss (@alice @bob) :text \"Synthetic scale discussion {number}\" :from {label} :thread \"synthetic-vote-1\" :caused-by {address}))"
        );
        let message = cbcl_parser::parse_message(
            &cbcl_parser::parse(&raw).map_err(|e| std::io::Error::other(e.to_string()))?,
        )
        .map_err(std::io::Error::other)?;
        input.messages.push(Record {
            signer,
            canonical: canonical_text(&message),
            signature: vec![],
        });
    }
    fs::File::open("/dev/urandom")?.read_exact(&mut input.salt)?;
    support::resign(&mut input);
    let bytes = serde_json::to_vec_pretty(&input)?;
    let journal = compute(&bytes).map_err(std::io::Error::other)?;
    if journal.covered_count != total as u64
        || journal.ballot_count != 2
        || journal.tally.get("yes") != Some(&1)
        || journal.tally.get("no") != Some(&1)
    {
        return Err("unexpected native scale-fixture outcome".into());
    }
    fs::create_dir_all(&dir)?;
    fs::write(dir.join("input.json"), bytes)?;
    fs::write(
        dir.join("expected.json"),
        serde_json::to_vec_pretty(&journal)?,
    )?;
    Ok(())
}
