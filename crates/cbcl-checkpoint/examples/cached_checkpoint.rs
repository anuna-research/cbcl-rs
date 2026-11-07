//! Runnable native-signature lifecycle using public deterministic test keys.
extern crate alloc;
pub use cbcl_checkpoint::*;
#[allow(dead_code)]
#[path = "../src/test_support.rs"]
mod support;
use host::{publish, Cache, DurableClient, Limits, Mode, Offer};
fn main() -> Result<()> {
    let f = support::Fixture::new();
    let members = f.members(&[]);
    let cert = f.certificate(&members);
    let directory = std::env::temp_dir().join(format!(
        "cbcl-checkpoint-example-{}-{:?}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    let mut cache = Cache::open(directory.join("cache"))?;
    let blob = publish(&cache, &cert, &f.context, &f.keys, |_| Ok(()))?;
    let client = member::Client::from_certificate(&f.context, &cert, &f.keys)?;
    let mut store = DurableClient::create(directory.join("client"), client, Mode::Enabled)?;
    let message = f.write("red", 1, &[], "@m0");
    let step = members[0].step(&message)?;
    let mut provider = f.members(&[]).remove(0);
    provider.accept(&message, &f.context, &f.keys)?;
    let floor_proofs = store
        .client()
        .frontier
        .iter()
        .map(|id| (id.clone(), provider.coverage().proof(id)))
        .collect();
    let offer = Offer {
        blob,
        tail: vec![step],
        floor_proofs,
    };
    let prepared = store.prepare(
        &mut cache,
        &[offer.encode()],
        &f.context,
        &f.keys,
        &Limits::default(),
    )?;
    let metrics = store.install(prepared)?;
    println!(
        "{}",
        serde_json::json!({"state":store.client().summary.render_json(),"generation":store.generation(),"metrics":metrics,"certificate_endorsements":cert.endorsements.len(),"retained_signed_bodies":store.client().evidence.len()})
    );
    drop(store);
    std::fs::remove_dir_all(directory)?;
    Ok(())
}
