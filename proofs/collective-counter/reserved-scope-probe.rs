// Review probe: append to a temporary copy of quorum_runtime.rs to reuse fixtures.
#[test]
fn review_reserved_pool_is_rejected_as_actor() {
 fn replace(s:&mut SExpr) { match s {SExpr::Atom(Atom::Symbol(v)) if v=="@alice"=>*v=COLLECTIVE_POOL.into(),SExpr::List(xs)=>for x in xs {replace(x)},_=>{}} }
 let mut n=collective();
 let mut raw=SExpr::from(&n.base[0].message);replace(&mut raw);
 let root=Act::from_message(parse_message(&raw).unwrap(),"@treasury").unwrap();
 let open=act(&format!("(signed @treasury (lang {} (open (@alice @bob @treasury) :available 100 :from @treasury :thread \"coin-1\" :caused-by {})))",n.d.name,root.address),"@treasury");

 n.base=vec![root,open];
 n.auth.acts=n.base.iter().map(|a|(a.address.clone(),a.signer.clone())).collect();
 let inst=Instance::new(&n.d,ThreadId("coin-1".into()),&n.base).unwrap();
 assert!(Context::from_instance(&inst,"tickets",None,&n.auth).unwrap_err().contains("reserved"));

}
