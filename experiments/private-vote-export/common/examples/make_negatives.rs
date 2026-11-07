#[path = "../tests/support/mod.rs"]
mod support;
use private_vote_common::{compute, Input};
use serde::Serialize;
use std::{fs, path::PathBuf};

#[derive(Serialize)]
struct Case {
    name: String,
    path: String,
    error: String,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args().skip(1);
    let dir = PathBuf::from(args.next().ok_or("usage: make_negatives OUTPUTDIR")?);
    if args.next().is_some() {
        return Err("extra argument".into());
    }
    fs::create_dir_all(dir.join("cases"))?;
    let base = support::fixture(false);
    // Refuse to emit negative evidence without a native positive control.
    compute(&serde_json::to_vec(&base)?).map_err(std::io::Error::other)?;
    let mut manifest = Vec::new();
    for name in [
        "invalidmsgsig",
        "invalidclosuresig",
        "missingclosure",
        "duplicatekey",
        "frommismatch",
        "wrongthread",
        "omitmessage",
        "duplicateact",
        "malformedclock",
        "unresolvedcause",
        "changedballot",
    ] {
        let mut input: Input = base.clone();
        let resign = match name {
            "invalidmsgsig" => {
                input.messages[0].signature[0] ^= 1;
                false
            }
            "invalidclosuresig" => {
                input.closure_signatures[0][0] ^= 1;
                false
            }
            "missingclosure" => {
                input.closure_signatures.pop();
                false
            }
            "duplicatekey" => {
                input.participants[1].key = input.participants[0].key;
                false
            }
            "frommismatch" => {
                input.messages[2].canonical = input.messages[2]
                    .canonical
                    .replace(":from @alice", ":from @bob");
                true
            }
            "wrongthread" => {
                input.messages[2].canonical = input.messages[2]
                    .canonical
                    .replace("synthetic-vote-1", "wrong-thread");
                true
            }
            "omitmessage" => {
                input.messages.pop();
                false
            }
            "duplicateact" => {
                input.messages.push(input.messages[2].clone());
                true
            }
            "malformedclock" => {
                input.messages[2].canonical = input.messages[2]
                    .canonical
                    .replace("hlc-0000000000000001-00000000", "invalid-clock");
                true
            }
            "unresolvedcause" => {
                let msg = &input.messages[2].canonical;
                let marker = ":caused-by ";
                let start = msg.find(marker).ok_or("missing caused-by in fixture")? + marker.len();
                let end = msg[start..]
                    .find(|c: char| c.is_whitespace() || c == ')')
                    .ok_or("missing predecessor end")?
                    + start;
                if !msg[start..end].starts_with("sha256-") {
                    return Err("expected single native predecessor".into());
                }
                input.messages[2]
                    .canonical
                    .replace_range(start..end, &format!("sha256-{}", "0".repeat(64)));
                true
            }
            "changedballot" => {
                input.messages[2].canonical =
                    input.messages[2].canonical.replace("\"yes\"", "\"no\"");
                false
            }
            _ => unreachable!(),
        };
        // Deliberate re-signing is possible only because these synthetic keys are
        // public. It lets guest negatives reach native admission after auth.
        if resign {
            support::resign(&mut input);
        }
        let bytes = serde_json::to_vec_pretty(&input)?;
        let error = compute(&bytes)
            .err()
            .ok_or_else(|| format!("negative accepted: {name}"))?;
        let path = format!("cases/{name}.json");
        fs::write(dir.join(&path), bytes)?;
        manifest.push(Case {
            name: name.into(),
            path,
            error,
        });
    }
    fs::write(
        dir.join("manifest.json"),
        serde_json::to_vec_pretty(&manifest)?,
    )?;
    Ok(())
}
