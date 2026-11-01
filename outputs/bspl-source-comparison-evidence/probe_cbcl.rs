use cbcl_core::store::MessageStore;
use cbcl_core::{protocol::verify_causal,store::{ThreadedMessageStore,ThreadId,ContentHash},state::wire_address,r6::r6_violations};
use cbcl_parser::{parse,parse_dialect,parse_message};
fn main(){
 let d=parse_dialect(&parse(r#"(define purchase (cbcl) @author
 (extend quote (to order price) (tell to :order order :price price))
 (extend accept (to order price) (tell to :order order :price price))
 (shape quote (require :order string) (require :price number))
 (shape accept (require :order string) (require :price number))
 (protocol (then begin quote accept)))"#).unwrap()).unwrap();
 let quote=parse_message(&parse(r#"(lang purchase (quote @buyer :order "o1" :price 100 :thread "p" :caused-by begin))"#).unwrap()).unwrap();
 let hash=wire_address(&quote);let thread=ThreadId("p".into());let mut store=ThreadedMessageStore::new();
 let cp=d.causal_protocol.as_ref().unwrap();
 let a=parse_message(&parse(&format!(r#"(lang purchase (accept @seller :order "o1" :price 1 :thread "p" :caused-by {hash}))"#)).unwrap()).unwrap();
 println!("changed_price_missing_quote={:?}",verify_causal("accept",a.innermost_simple().unwrap().caused_by(),&store,cp,&thread));
 store.append(ContentHash(hash),thread.clone(),quote);
 println!("changed_price_with_quote={:?}",verify_causal("accept",a.innermost_simple().unwrap().caused_by(),&store,cp,&thread));
 println!("changed_price_shape_ok={}",d.shapes.iter().find(|s|s.performative=="accept").unwrap().check(&parse(r#"(tell @seller :order "o1" :price 1)"#).unwrap()).is_ok());
 let handoff=parse_dialect(&parse(r#"(define handoff (cbcl) @author
 (:roles (a b c))
 (extend m (to id x) :from a :to b (tell to :id id :x x))
 (extend n (to id x y) :from b :to c (tell to :id id :x x :y y))
 (protocol (then begin m n)))"#).unwrap()).unwrap();
 println!("handoff_r6={:?}",r6_violations(&handoff));
}
