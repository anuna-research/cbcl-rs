//! DE-RISKING STUDY DRIVER: run the candidate `splice_coherence` analyzer over
//! the same corpus `paper_corpus.rs` / `paper_oauth.rs` drive through R6, and
//! emit the per-(protocol, role) verdict table (causally-local vs
//! splice-coherent). Run with:
//!
//!   cargo test -p cbcl-parser --test splice_corpus -- --nocapture
//!
//! The table is computed evidence for the GO/NO-GO memo: it pins which
//! (protocol, role) pairs are splice-coherent-but-NOT-causally-local (the
//! condition being inhabited strictly beyond R6(vi)).

use cbcl_core::r6::r6_violations;
use cbcl_core::role::R6Violation;
use cbcl_core::sexpr::SExpr;
use cbcl_core::splice::{non_coherent_roles, analyze, Discharge};
use cbcl_parser::parse_dialect;

fn parse(src: &str) -> cbcl_core::dialect::Dialect {
    let sexpr: SExpr = src.parse().expect("dialect S-expression");
    parse_dialect(&sexpr).expect("dialect parse")
}

/// Roles onto which R6(vi) `NotCausallyLocal` fires (i.e. NOT causally local).
fn nonlocal_roles(d: &cbcl_core::dialect::Dialect) -> std::collections::BTreeSet<String> {
    r6_violations(d)
        .into_iter()
        .filter_map(|v| match v {
            R6Violation::NotCausallyLocal { role, .. } => Some(role),
            _ => None,
        })
        .collect()
}

fn oauth_src() -> String {
    "(define oauth (cbcl) @example
       (:roles (server client authoriser))
       (extend login (session scope) :from server :to client
         (tell @client :session session :scope scope :domain oauth))
       (extend abort (session reason) :from server :to client
         (tell @client :session session :reason reason :domain oauth))
       (extend passwd (session credential) :from client :to authoriser
         (tell @authoriser :session session :credential credential :domain oauth))
       (extend auth (session grant) :from authoriser :to server
         (tell @server :session session :grant grant :domain oauth))
       (extend quit (session reason) :from client :to authoriser
         (tell @authoriser :session session :reason reason :domain oauth))
       (protocol (then begin (any login abort))
                 (then login passwd auth)
                 (then abort quit)))"
        .to_string()
}

fn logistics_src() -> String {
    "(define logistics (cbcl) @corpus
       (:roles (shipper tracking-svc warehouse))
       (extend track-shipment (item) :from shipper :to tracking-svc
         (tell @tracking-svc :item item :domain logistics))
       (extend accept (item) :from tracking-svc :to shipper
         (tell @shipper :item item :domain logistics))
       (extend reject (item) :from tracking-svc :to shipper
         (tell @shipper :item item :domain logistics))
       (extend dispatch (item) :from warehouse :to shipper
         (tell @shipper :item item :domain logistics))
       (protocol (then begin track-shipment (any accept reject)) (then accept dispatch)))"
        .to_string()
}

fn two_buyer_src() -> String {
    "(define twobuyer (cbcl) @corpus
       (:roles (buyer1 buyer2 seller))
       (extend title (name) :from buyer1 :to seller
         (tell @seller :name name :domain twobuyer))
       (extend quote (price) :from seller :to (buyer1 buyer2)
         (tell @buyer1 :price price :domain twobuyer))
       (extend share (amount) :from buyer1 :to buyer2
         (tell @buyer2 :amount amount :domain twobuyer))
       (extend buy (address) :from buyer2 :to seller
         (tell @seller :address address :domain twobuyer))
       (extend quit (reason) :from buyer2 :to seller
         (tell @seller :reason reason :domain twobuyer))
       (extend date (delivery) :from seller :to buyer2
         (tell @buyer2 :delivery delivery :domain twobuyer))
       (protocol (then begin title quote share (any buy quit)) (then buy date)))"
        .to_string()
}

fn pipeline_src() -> String {
    "(define pipeline (cbcl) @corpus
       (:roles (source kernel sink))
       (extend produce (chunk) :from source :to kernel
         (tell @kernel :chunk chunk :domain pipeline))
       (extend forward (chunk) :from kernel :to sink
         (tell @sink :chunk chunk :domain pipeline))
       (protocol (then begin produce forward)))"
        .to_string()
}

fn ring_src() -> String {
    "(define ring (cbcl) @corpus
       (:roles (a b c))
       (extend fwd1 (token) :from a :to b (tell @b :token token :domain ring))
       (extend fwd2 (token) :from b :to c (tell @c :token token :domain ring))
       (extend fwd3 (token) :from c :to a (tell @a :token token :domain ring))
       (protocol (then begin fwd1 fwd2 fwd3)))"
        .to_string()
}

fn two_pc_src() -> String {
    "(define twopc (cbcl) @corpus
       (:roles (coordinator p1 p2 p3))
       (extend prepare (txn) :from coordinator :to (p1 p2 p3)
         (tell @p1 :txn txn :domain twopc))
       (extend vote1 (v) :from p1 :to coordinator (tell @coordinator :v v :domain twopc))
       (extend vote2 (v) :from p2 :to coordinator (tell @coordinator :v v :domain twopc))
       (extend vote3 (v) :from p3 :to coordinator (tell @coordinator :v v :domain twopc))
       (extend decision (outcome) :from coordinator :to (p1 p2 p3)
         (tell @p1 :outcome outcome :domain twopc))
       (protocol (then begin prepare)
                 (then prepare vote1) (then prepare vote2) (then prepare vote3)
                 (then (all vote1 vote2 vote3) decision)))"
        .to_string()
}

fn reqresp_src() -> String {
    "(define reqresp (cbcl) @corpus
       (:roles (client server))
       (extend rpc-req (payload) :from client :to server
         (tell @server :payload payload :domain reqresp))
       (extend rpc-resp (result) :from server :to client
         (tell @client :result result :domain reqresp))
       (protocol (then begin rpc-req rpc-resp)))"
        .to_string()
}

#[test]
fn corpus_verdict_table_splice_vs_causal_locality() {
    let corpus: Vec<(&str, String)> = vec![
        ("reqresp", reqresp_src()),
        ("oauth", oauth_src()),
        ("logistics", logistics_src()),
        ("twobuyer", two_buyer_src()),
        ("pipeline", pipeline_src()),
        ("ring", ring_src()),
        ("twopc", two_pc_src()),
    ];

    println!("\n=== SPLICE-COHERENCE vs R6(vi) CAUSAL LOCALITY — corpus verdict ===");
    println!(
        "{:<12} {:<14} {:<8} {:<8} {:<10}",
        "protocol", "role", "R6(vi)", "splice", "witness?"
    );

    let mut witnesses: Vec<(String, String)> = Vec::new();

    for (name, src) in &corpus {
        let d = parse(src);
        let nonlocal = nonlocal_roles(&d);
        let non_coherent = non_coherent_roles(&d);
        for role in &d.roles {
            let r = &role.name;
            let local = !nonlocal.contains(r);
            let coherent = !non_coherent.contains(r);
            let witness = coherent && !local; // splice-coherent but NOT causally local
            if witness {
                witnesses.push((name.to_string(), r.clone()));
            }
            println!(
                "{:<12} {:<14} {:<8} {:<8} {:<10}",
                name,
                r,
                if local { "local" } else { "NONLOCAL" },
                if coherent { "yes" } else { "NO" },
                if witness { "<== WITNESS" } else { "" }
            );
        }
    }

    println!("\n--- discharge of each spliced-citation edge (which disjunct fired) ---");
    for (name, src) in &corpus {
        let d = parse(src);
        let (_f, edges) = analyze(&d);
        for e in &edges {
            let how = match e.how {
                Discharge::TypeForced => "(A) type-forced",
                Discharge::Merge => "(B)(a) merge",
                Discharge::HashPinned => "(B)(b) hash-pin",
            };
            println!(
                "{:<12} role={:<12} {} cites bystander {:<14} via {}",
                name, e.role, e.message, e.bystander, how
            );
        }
    }

    println!(
        "\nWITNESSES (splice-coherent but NOT causally-local): {} pairs",
        witnesses.len()
    );
    for (p, r) in &witnesses {
        println!("  {p} / {r}");
    }

    // The GO criterion-1 claim: the condition is inhabited strictly beyond
    // R6(vi) on real protocols — at least the OAuth authoriser.
    assert!(
        witnesses
            .iter()
            .any(|(p, r)| p == "oauth" && r == "authoriser"),
        "OAuth authoriser must be splice-coherent but not causally-local"
    );
    assert!(
        witnesses.len() >= 5,
        "several corpus (protocol, role) pairs must be splice-coherent beyond R6(vi)"
    );
}
