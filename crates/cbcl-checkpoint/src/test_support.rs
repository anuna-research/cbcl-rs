use crate::{certificate::*, hex, member::Member, Error, Result};
use alloc::{format, string::String, vec::Vec};
use cbcl_core::{
    canonical::dialect_name,
    dialect::Dialect,
    message::Message,
    sexpr::{Atom, SExpr},
};
use ed25519_dalek::{Signature, Signer, SigningKey};

pub struct Keys;
impl Keys {
    fn key(key: &str) -> Option<SigningKey> {
        let i = if key == "@init" {
            4
        } else {
            key.strip_prefix("@m")?.parse::<u8>().ok()?
        };
        if i > 4 {
            return None;
        }
        Some(SigningKey::from_bytes(&[i + 21; 32]))
    }
}
impl KeyVerifier for Keys {
    fn verify(&self, key: &str, p: &[u8], s: &[u8]) -> bool {
        match (Self::key(key), Signature::from_slice(s)) {
            (Some(k), Ok(s)) => k.verifying_key().verify_strict(p, &s).is_ok(),
            _ => false,
        }
    }
}
impl KeySigner for Keys {
    fn sign(&self, key: &str, p: &[u8]) -> Result<Vec<u8>> {
        Ok(Self::key(key)
            .ok_or(Error::Invalid("test signer"))?
            .sign(p)
            .to_bytes()
            .to_vec())
    }
}
pub fn parse(s: &str) -> Message {
    Message::try_from(&s.parse::<SExpr>().unwrap()).unwrap()
}
pub fn installed(s: &str) -> Dialect {
    let mut x = cbcl_parser::parse(s).unwrap();
    let d = cbcl_parser::parse_dialect(&x).unwrap();
    if let SExpr::List(v) = &mut x {
        v[1] = SExpr::Atom(Atom::Symbol(dialect_name(&d)));
    }
    cbcl_parser::parse_and_install_dialect(&x)
        .unwrap()
        .iter()
        .last()
        .unwrap()
        .clone()
}
pub struct Fixture {
    pub context: Context,
    pub keys: Keys,
    pub opener: SignedMessage,
    pub target_open: SignedMessage,
}
impl Fixture {
    pub fn new() -> Self {
        let target = installed(
            r#"(define checkpoint-target (cbcl) @anuna
   (:roles ((* member)))
   (extend open (to title) :from member :to member (tell to :title title))
   (extend write (to item value clock) :from member :to member (tell to :item item :value value :clock clock))
   (extend drop (to item) :from member :to member (tell to :item item))
   (shape open (require :title string))
   (shape write (require :item string) (require :value string) (require :clock hlc))
   (shape drop (require :item string))
   (protocol (then begin open) (then open write) (then open drop))
   (state (title (initial open :title)) (items (lww-map write :item :value :clock drop)) (versions (multi-value-map write :item :value drop))))"#,
        );
        Self::with_target(target)
    }
    pub fn with_target(target: Dialect) -> Self {
        let keys = Keys;
        let target_root=SignedMessage::sign(parse(&format!("(with-roles ((member @m0 @m1 @m2 @m3)) :dialect {} (hello :sender @m0 :thread \"target\" :caused-by begin))",target.hash.as_ref().unwrap())),"@m0",&keys).unwrap();
        let cd = cbcl_parser::checkpoint_dialect::builtin().unwrap();
        let companion_root=SignedMessage::sign(parse(&format!("(with-roles ((initializer @init) (member @m0 @m1 @m2 @m3)) :dialect {} (hello :sender @init :thread \"checkpoint\" :caused-by begin))",cd.hash.as_ref().unwrap())),"@init",&keys).unwrap();
        if let Message::Wrapped { params, .. } = companion_root.message() {
            cbcl_core::role::parse_wrapper_cast(params, &cd.roles).unwrap();
        }
        let profile = crate::summary::Summary::expected_profile_hash_for(
            target.state.as_ref().unwrap(),
            target.causal_protocol.as_ref(),
        )
        .unwrap();
        let context = Context::new(
            target,
            target_root,
            companion_root,
            Policy {
                roster: (0..4).map(|i| format!("@m{i}")).collect(),
                faults: 1,
            },
            profile,
            &keys,
        )
        .unwrap();
        let scope = format!(
            ":target \"{}\" :context \"{}\" :policy \"{}\" :profile \"{}\"",
            context.target_root().id().unwrap(),
            hex(&context.hash()),
            hex(&context.policy().hash()),
            hex(&context.profile())
        );
        let opener=SignedMessage::sign(parse(&format!("(lang {} (open (@init @m0 @m1 @m2 @m3) {} :version 1 :sender @init :thread \"checkpoint\" :caused-by \"{}\"))",cd.name,scope,context.companion_root().id().unwrap())),"@init",&keys).unwrap();
        let target_open=SignedMessage::sign(parse(&format!("(lang {} (open (@m0 @m1 @m2 @m3) :title \"Drawing\" :sender @m0 :thread \"target\" :caused-by \"{}\"))",context.target().name,context.target_root().id().unwrap())),"@m0",&keys).unwrap();
        Self {
            context,
            keys,
            opener,
            target_open,
        }
    }
    pub fn write(
        &self,
        value: &str,
        clock: u64,
        replaces: &[String],
        signer: &str,
    ) -> SignedMessage {
        SignedMessage::sign(parse(&format!("(lang {} (write (@m0 @m1 @m2 @m3) :item \"shape\" :value \"{}\" :clock \"hlc-{:016x}-00000000\" :replaces ({}) :sender {} :thread \"target\" :caused-by \"{}\"))",self.context.target().name,value,clock,replaces.join(" "),signer,self.target_open.id().unwrap())),signer,&self.keys).unwrap()
    }
    pub fn endorsement(&self, m: &Member, manifest: &Manifest) -> SignedMessage {
        let cd = cbcl_parser::checkpoint_dialect::builtin().unwrap();
        let key = m.signer();
        let unsigned=parse(&format!("(lang {} (endorse (@init @m0 @m1 @m2 @m3) :target \"{}\" :context \"{}\" :policy \"{}\" :profile \"{}\" :manifest \"{}\" :sender {} :thread \"checkpoint\" :caused-by \"{}\"))",cd.name,manifest.target,hex(&manifest.context),hex(&manifest.policy),hex(&manifest.profile),hex(&manifest.hash()),key,self.opener.id().unwrap()));
        m.authorize_endorse_with_opener(manifest, unsigned, &self.opener, &self.context, &self.keys)
            .unwrap()
            .sign(&self.keys)
            .unwrap()
    }
    pub fn members(&self, history: &[SignedMessage]) -> Vec<Member> {
        (0..4)
            .map(|i| {
                let mut m = Member::new(&self.context, &format!("@m{i}"), &self.keys).unwrap();
                m.accept(&self.target_open, &self.context, &self.keys)
                    .unwrap();
                for a in history {
                    m.accept(a, &self.context, &self.keys).unwrap()
                }
                m
            })
            .collect()
    }
    pub fn certificate(&self, members: &[Member]) -> Certificate {
        let manifest = members[0].manifest(&self.context).unwrap();
        let endorsements = members
            .iter()
            .take(3)
            .map(|m| self.endorsement(m, &manifest))
            .collect();
        Certificate {
            summary: members[0].client().summary.encode(),
            manifest,
            opener: self.opener.clone(),
            endorsements,
        }
    }
}
