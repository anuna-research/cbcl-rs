//! Native companion endorsements and content-bound certificate verification.
use crate::{
    codec::{self, put_bytes, put_string, put_u32, Reader},
    hash, hex, Error, Hash, Result,
};
use alloc::{boxed::Box, collections::BTreeSet, string::String, vec, vec::Vec};
use cbcl_core::{
    canonical::dialect_hash,
    dialect::Dialect,
    equivocation::message_content_hash,
    keyid::KeyId,
    message::{Message, WrapperType},
    projection::verify_causal_for_role,
    protocol::VerificationResult,
    role::{parse_wrapper_cast, AgentKey, Endpoint},
    sexpr::{Atom, SExpr},
    state::Act,
    store::{ContentHash, MessageStore, ThreadId, ThreadedMessageStore},
};
use serde::{Deserialize, Serialize};

pub trait KeyVerifier {
    fn verify(&self, key: &str, preimage: &[u8], signature: &[u8]) -> bool;
}
pub trait KeySigner: KeyVerifier {
    fn sign(&self, key: &str, preimage: &[u8]) -> Result<Vec<u8>>;
}

/// Keep raw key custody behind this boundary when exposing authoring to callers.
/// Unlike the low-level host crypto trait, it has no unrestricted endorsement path.
pub struct ManagedSigner<K> {
    keys: K,
}
impl<K: KeySigner> ManagedSigner<K> {
    pub fn new(keys: K) -> Self {
        Self { keys }
    }
    pub fn sign_native(&self, message: Message, key: &str) -> Result<SignedMessage> {
        if message
            .innermost_simple()
            .and_then(Message::performative)
            .is_some_and(|p| p.name() == "endorse")
        {
            return Err(Error::Invalid("endorsement requires profile capability"));
        }
        SignedMessage::sign(message, key, &self.keys)
    }
    pub fn sign_endorsement(
        &self,
        capability: crate::member::EndorsementCapability,
    ) -> Result<SignedMessage> {
        capability.sign(&self.keys)
    }
}
impl<K: KeyVerifier> KeyVerifier for ManagedSigner<K> {
    fn verify(&self, key: &str, preimage: &[u8], signature: &[u8]) -> bool {
        self.keys.verify(key, preimage, signature)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SignedMessage {
    message: Message,
}
impl SignedMessage {
    pub fn from_message(message: Message) -> Self {
        Self { message }
    }
    pub fn message(&self) -> &Message {
        &self.message
    }
    pub fn encode(&self) -> Vec<u8> {
        codec::message_bytes(&self.message)
    }
    pub fn decode(bytes: &[u8]) -> Result<Self> {
        Ok(Self {
            message: codec::decode_message(bytes)?,
        })
    }
    pub fn id(&self) -> Result<String> {
        Ok(message_content_hash(
            self.message
                .innermost_simple()
                .ok_or(Error::Invalid("missing simple message"))?,
        ))
    }
    pub fn authenticate(&self, keys: &dyn KeyVerifier) -> Result<Act> {
        bounded_message(&self.message)?;
        if self.encode().len() > 256 * 1024 {
            return Err(Error::Budget);
        }
        let (unsigned, key, sig) = signature_parts(&self.message)?;
        if !keys.verify(&key, &codec::message_bytes(&unsigned), &sig) {
            return Err(Error::Invalid("native signature"));
        }
        let a = Act::from_message(self.message.clone(), &key).map_err(|_| Error::Invalid("act"))?;
        let simple = self
            .message
            .innermost_simple()
            .ok_or(Error::Invalid("simple"))?;
        if simple.sender() != Some(key.as_str())
            && a.fields.get("from") != Some(&SExpr::Atom(Atom::Symbol(key.clone())))
        {
            // `from` is a routing field, so inspect it directly below.
            let Message::Simple { params, .. } = simple else {
                return Err(Error::Invalid("simple"));
            };
            let from = params.windows(2).find_map(|p| {
                if p[0] == SExpr::Atom(Atom::Keyword("from".into())) {
                    match &p[1] {
                        SExpr::Atom(Atom::Symbol(s) | Atom::Str(s)) => Some(s.as_str()),
                        _ => None,
                    }
                } else {
                    None
                }
            });
            if from != Some(key.as_str()) {
                return Err(Error::Invalid("signed sender mismatch"));
            }
        }
        Ok(a)
    }
    pub fn sign(message: Message, key: &str, keys: &dyn KeySigner) -> Result<Self> {
        bounded_message(&message)?;
        KeyId::parse(key).map_err(|_| Error::Invalid("signer key"))?;
        let mut m = match message {
            Message::Wrapped {
                wrapper: WrapperType::WithRoles,
                params,
                content,
            } => Message::Wrapped {
                wrapper: WrapperType::WithRoles,
                params,
                content: Box::new(wrap(*content, key)),
            },
            m => wrap(m, key),
        };
        let (unsigned, _, _) = signature_parts(&m)?;
        let signature = keys.sign(key, &codec::message_bytes(&unsigned))?;
        set_signature(&mut m, hex(&signature))?;
        let out = Self { message: m };
        out.authenticate(keys)?;
        Ok(out)
    }
}
fn bounded_message(message: &Message) -> Result<()> {
    let mut messages = vec![(message, 0usize)];
    let mut expressions = Vec::new();
    let mut bytes = 0usize;
    let mut nodes = 0usize;
    while let Some((m, d)) = messages.pop() {
        if d > 64 {
            return Err(Error::Budget);
        }
        nodes += 1;
        match m {
            Message::Simple {
                content,
                params,
                thread,
                sender,
                recipient,
                caused_by,
                ..
            } => {
                if params.len() > 32768 {
                    return Err(Error::Budget);
                }
                expressions.push((content, d));
                for p in params {
                    expressions.push((p, d));
                }
                bytes = bytes
                    .saturating_add(thread.as_ref().map_or(0, String::len))
                    .saturating_add(sender.as_ref().map_or(0, String::len));
                match recipient {
                    Some(cbcl_core::message::Recipients::One(s)) => {
                        bytes = bytes.saturating_add(s.len())
                    }
                    Some(cbcl_core::message::Recipients::Set(ss)) => {
                        if ss.len() > 512 {
                            return Err(Error::Budget);
                        }
                        for s in ss {
                            bytes = bytes.saturating_add(s.len());
                        }
                    }
                    None => {}
                }
                match caused_by {
                    Some(cbcl_core::message::CausedBy::Single(s)) => {
                        bytes = bytes.saturating_add(s.len())
                    }
                    Some(cbcl_core::message::CausedBy::Multiple(ss)) => {
                        if ss.len() > 256 {
                            return Err(Error::Budget);
                        }
                        for s in ss {
                            bytes = bytes.saturating_add(s.len());
                        }
                    }
                    _ => {}
                }
            }
            Message::Meta { dialect_def } => expressions.push((dialect_def, d)),
            Message::Dialect {
                dialect_name,
                inner,
            } => {
                bytes = bytes.saturating_add(dialect_name.len());
                messages.push((inner, d + 1));
            }
            Message::Wrapped {
                params, content, ..
            } => {
                if params.len() > 32768 {
                    return Err(Error::Budget);
                }
                for p in params {
                    expressions.push((p, d));
                }
                messages.push((content, d + 1));
            }
        }
    }
    while let Some((x, d)) = expressions.pop() {
        if d > 64 {
            return Err(Error::Budget);
        }
        nodes += 1;
        match x {
            SExpr::List(xs) => {
                if xs.len() > 32768 {
                    return Err(Error::Budget);
                }
                for x in xs {
                    expressions.push((x, d + 1));
                }
            }
            SExpr::Atom(Atom::Symbol(s) | Atom::Keyword(s) | Atom::Str(s)) => {
                bytes = bytes.saturating_add(s.len())
            }
            _ => bytes = bytes.saturating_add(32),
        }
        if nodes > 32768 || bytes > 256 * 1024 {
            return Err(Error::Budget);
        }
    }
    if bytes > 256 * 1024 || nodes > 32768 {
        return Err(Error::Budget);
    }
    Ok(())
}
fn wrap(m: Message, key: &str) -> Message {
    Message::Wrapped {
        wrapper: WrapperType::Signed,
        params: vec![
            SExpr::Atom(Atom::Symbol(key.into())),
            SExpr::Atom(Atom::Str(String::new())),
        ],
        content: Box::new(m),
    }
}
fn signature_parts(m: &Message) -> Result<(Message, String, Vec<u8>)> {
    match m {
        Message::Wrapped {
            wrapper: WrapperType::WithRoles,
            params,
            content,
        } => {
            let (u, k, s) = signature_parts(content)?;
            Ok((
                Message::Wrapped {
                    wrapper: WrapperType::WithRoles,
                    params: params.clone(),
                    content: Box::new(u),
                },
                k,
                s,
            ))
        }
        Message::Wrapped {
            wrapper: WrapperType::Signed,
            params,
            content,
        } => {
            let [SExpr::Atom(Atom::Symbol(key)), SExpr::Atom(Atom::Str(sig))] = params.as_slice()
            else {
                return Err(Error::Invalid("native signed wrapper"));
            };
            let kid = KeyId::parse(key).map_err(|_| Error::Invalid("key"))?;
            if !kid.suite.is_implemented() {
                return Err(Error::Unsupported);
            }
            if matches!(content.as_ref(), Message::Wrapped { .. }) {
                return Err(Error::Invalid("nested signature wrapper"));
            }
            let sig = unhex(sig)?;
            Ok((
                Message::Wrapped {
                    wrapper: WrapperType::Signed,
                    params: vec![params[0].clone()],
                    content: content.clone(),
                },
                key.clone(),
                sig,
            ))
        }
        _ => Err(Error::Invalid("unsigned native message")),
    }
}
fn set_signature(m: &mut Message, s: String) -> Result<()> {
    match m {
        Message::Wrapped {
            wrapper: WrapperType::WithRoles,
            content,
            ..
        } => set_signature(content, s),
        Message::Wrapped {
            wrapper: WrapperType::Signed,
            params,
            ..
        } => {
            params[1] = SExpr::Atom(Atom::Str(s));
            Ok(())
        }
        _ => Err(Error::Invalid("signature slot")),
    }
}
pub fn unhex(s: &str) -> Result<Vec<u8>> {
    if s.len() % 2 != 0 || s.len() > 4096 {
        return Err(Error::Invalid("hex"));
    }
    s.as_bytes()
        .chunks(2)
        .map(|p| {
            let f = |c: u8| match c {
                b'0'..=b'9' => Ok(c - b'0'),
                b'a'..=b'f' => Ok(c - b'a' + 10),
                _ => Err(Error::Invalid("hex")),
            };
            Ok(f(p[0])? * 16 + f(p[1])?)
        })
        .collect()
}
pub fn native_id(s: &str) -> Result<()> {
    cbcl_core::multihash::decode(s)
        .map(|_| ())
        .ok_or(Error::Invalid("native id"))
}
pub fn native(s: &str) -> String {
    s.into()
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Policy {
    pub roster: Vec<String>,
    pub faults: usize,
}
impl Policy {
    pub fn validate(&self) -> Result<()> {
        let n = self.roster.len();
        if n == 0
            || n > 256
            || self
                .faults
                .checked_mul(3)
                .and_then(|x| x.checked_add(1))
                .filter(|min| n >= *min)
                .is_none()
        {
            return Err(Error::Invalid("quorum policy"));
        }
        let mut keys = BTreeSet::new();
        for k in &self.roster {
            let key = KeyId::parse(k).map_err(|_| Error::Invalid("roster key"))?;
            if !key.suite.is_implemented() || !keys.insert(key.canonical_spelling()) {
                return Err(Error::Invalid("duplicate roster key"));
            }
        }
        Ok(())
    }
    pub fn threshold(&self) -> usize {
        self.roster.len() - self.faults
    }
    pub fn hash(&self) -> Hash {
        let mut b = Vec::new();
        put_u32(&mut b, self.faults);
        for k in &self.roster {
            put_string(&mut b, k)
        }
        hash(b"cbcl/checkpoint/policy/v1", &b)
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Context {
    pub(crate) target: Dialect,
    pub(crate) target_root: SignedMessage,
    pub(crate) companion_root: SignedMessage,
    pub(crate) policy: Policy,
    pub(crate) profile: Hash,
    validated: bool,
}
impl Context {
    /// Construct from an independently installed native target and pinned roots.
    /// Fields are immutable to callers, so the installed code hash is sufficient
    /// for subsequent context hashing; admission need not rehash the whole dialect.
    pub fn new(
        target: Dialect,
        target_root: SignedMessage,
        companion_root: SignedMessage,
        policy: Policy,
        profile: Hash,
        keys: &dyn KeyVerifier,
    ) -> Result<Self> {
        let mut c = Self {
            target,
            target_root,
            companion_root,
            policy,
            profile,
            validated: false,
        };
        c.validate(keys)?;
        crate::member::validate_root_uncached(&c, keys)?;
        c.validated = true;
        Ok(c)
    }
    pub fn target(&self) -> &Dialect {
        &self.target
    }
    pub fn target_root(&self) -> &SignedMessage {
        &self.target_root
    }
    pub fn companion_root(&self) -> &SignedMessage {
        &self.companion_root
    }
    pub fn policy(&self) -> &Policy {
        &self.policy
    }
    pub fn profile(&self) -> Hash {
        self.profile
    }
    pub(crate) fn validate_runtime(&self, keys: &dyn KeyVerifier) -> Result<()> {
        if !self.validated {
            return Err(Error::Invalid("unvalidated context"));
        }
        self.policy.validate()?;
        self.target_root.authenticate(keys)?;
        self.companion_root.authenticate(keys)?;
        Ok(())
    }
    pub fn validate(&self, keys: &dyn KeyVerifier) -> Result<()> {
        self.policy.validate()?;
        self.target_root.authenticate(keys)?;
        let root = self.companion_root.authenticate(keys)?;
        if self.target.hash.as_deref() != Some(dialect_hash(&self.target).as_str())
            || self.target.name != cbcl_core::canonical::dialect_name(&self.target)
            || self.target_root.id()? == self.companion_root.id()?
        {
            return Err(Error::Invalid("context pin"));
        }
        let d = cbcl_parser::checkpoint_dialect::builtin()
            .map_err(|_| Error::Invalid("builtin dialect"))?;
        let Message::Wrapped {
            wrapper: WrapperType::WithRoles,
            params,
            ..
        } = self.companion_root.message()
        else {
            return Err(Error::Invalid("companion cast"));
        };
        let cast =
            parse_wrapper_cast(params, &d.roles).map_err(|_| Error::Invalid("companion cast"))?;
        if cast.dialect_pin != d.hash || root.verb != "hello" {
            return Err(Error::Invalid("companion dialect pin"));
        }
        let members = cast
            .indexed
            .get("member")
            .ok_or(Error::Invalid("member role"))?;
        if members.iter().map(|k| &k.0).collect::<BTreeSet<_>>()
            != self.policy.roster.iter().collect()
        {
            return Err(Error::Invalid("cast roster mismatch"));
        }
        if cast.singleton.get("initializer").map(|k| k.0.as_str()) != Some(root.signer.as_str()) {
            return Err(Error::Invalid("initializer"));
        }
        struct RootGate<'a> {
            root: &'a SignedMessage,
            keys: &'a dyn KeyVerifier,
        }
        impl cbcl_core::admission::AdmissionGate for RootGate<'_> {
            fn authenticate(
                &self,
                m: &Message,
            ) -> core::result::Result<ContentHash, alloc::string::String> {
                if m != self.root.message() {
                    return Err("unexpected bootstrap message".into());
                }
                self.root
                    .authenticate(self.keys)
                    .map_err(|_| alloc::string::String::from("bootstrap signature"))?;
                self.root
                    .id()
                    .map(ContentHash)
                    .map_err(|_| alloc::string::String::from("bootstrap identity"))
            }
        }
        let root_id = self.companion_root.id()?;
        let mut monitor = cbcl_core::admission::AdmissionMonitor::new(
            d,
            Endpoint {
                role: "initializer".into(),
                occupant: None,
            },
            self.companion_root.message().clone(),
            RootGate {
                root: &self.companion_root,
                keys,
            },
        )
        .map_err(|_| Error::Invalid("companion root admission"))?;
        monitor.drain_ready();
        if monitor.state(&ContentHash(root_id))
            != Some(&cbcl_core::admission::AdmissionState::Accepted)
        {
            return Err(Error::Invalid("unaccepted companion root"));
        }
        Ok(())
    }
    pub fn hash(&self) -> Hash {
        let mut b = Vec::new();
        put_string(&mut b, self.target.hash.as_deref().unwrap_or("uninstalled"));
        put_string(&mut b, &self.target.name);
        put_bytes(&mut b, &self.target_root.encode());
        put_bytes(&mut b, &self.companion_root.encode());
        b.extend(self.policy.hash());
        b.extend(self.profile);
        hash(b"cbcl/checkpoint/context/v1", &b)
    }
    pub fn manifest(
        &self,
        coverage: Hash,
        summary: Hash,
        frontier: Vec<String>,
    ) -> Result<Manifest> {
        let m = Manifest {
            version: 1,
            target: self.target_root.id()?,
            context: self.hash(),
            companion: self.companion_root.id()?,
            policy: self.policy.hash(),
            profile: self.profile,
            coverage,
            summary,
            frontier,
        };
        m.validate(self)?;
        Ok(m)
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Manifest {
    pub version: u32,
    pub target: String,
    pub context: Hash,
    pub companion: String,
    pub policy: Hash,
    pub profile: Hash,
    pub coverage: Hash,
    pub summary: Hash,
    pub frontier: Vec<String>,
}
impl Manifest {
    pub fn encode(&self) -> Vec<u8> {
        let mut b = Vec::new();
        put_u32(&mut b, self.version as usize);
        put_string(&mut b, &self.target);
        b.extend(self.context);
        put_string(&mut b, &self.companion);
        for h in [self.policy, self.profile, self.coverage, self.summary] {
            b.extend(h)
        }
        put_u32(&mut b, self.frontier.len());
        for id in &self.frontier {
            put_string(&mut b, id)
        }
        b
    }
    pub fn decode(r: &mut Reader<'_>) -> Result<Self> {
        let version = r.u32()? as u32;
        let target = r.string(71)?;
        let context = r.hash()?;
        let companion = r.string(71)?;
        let policy = r.hash()?;
        let profile = r.hash()?;
        let coverage = r.hash()?;
        let summary = r.hash()?;
        let n = r.count(4096)?;
        let mut frontier = Vec::new();
        for _ in 0..n {
            frontier.push(r.string(71)?)
        }
        Ok(Self {
            version,
            target,
            context,
            companion,
            policy,
            profile,
            coverage,
            summary,
            frontier,
        })
    }
    pub fn hash(&self) -> Hash {
        hash(b"cbcl/checkpoint/manifest/v1", &self.encode())
    }
    pub fn validate(&self, c: &Context) -> Result<()> {
        if self.version != 1
            || self.context != c.hash()
            || self.target != c.target_root.id()?
            || self.companion != c.companion_root.id()?
            || self.policy != c.policy.hash()
            || self.profile != c.profile
        {
            return Err(Error::Invalid("manifest context"));
        }
        if self.frontier.is_empty()
            || self.frontier.len() > 4096
            || self.frontier.windows(2).any(|w| w[0] >= w[1])
        {
            return Err(Error::Invalid("frontier"));
        }
        for id in &self.frontier {
            native_id(id)?
        }
        Ok(())
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Certificate {
    pub manifest: Manifest,
    pub summary: Vec<u8>,
    pub opener: SignedMessage,
    pub endorsements: Vec<SignedMessage>,
}
impl Certificate {
    pub fn encode(&self, c: &Context) -> Vec<u8> {
        let mut b = self.manifest.encode();
        put_bytes(&mut b, &self.summary);
        put_bytes(&mut b, &c.companion_root.encode());
        put_bytes(&mut b, &self.opener.encode());
        put_u32(&mut b, self.endorsements.len());
        for e in &self.endorsements {
            put_bytes(&mut b, &e.encode())
        }
        b
    }
    pub fn decode(bytes: &[u8], c: &Context) -> Result<Self> {
        let mut r = Reader::new(bytes, 16 * 1024 * 1024)?;
        let manifest = Manifest::decode(&mut r)?;
        let summary = r.bytes(16 * 1024 * 1024)?.to_vec();
        let root = SignedMessage::decode(r.bytes(256 * 1024)?)?;
        if root != c.companion_root {
            return Err(Error::Invalid("foreign companion"));
        }
        let opener = SignedMessage::decode(r.bytes(256 * 1024)?)?;
        let n = r.count(c.policy.roster.len())?;
        let mut endorsements = Vec::new();
        for _ in 0..n {
            endorsements.push(SignedMessage::decode(r.bytes(256 * 1024)?)?)
        }
        r.finish()?;
        Ok(Self {
            manifest,
            summary,
            opener,
            endorsements,
        })
    }
    pub fn blob_id(&self, c: &Context) -> Hash {
        hash(b"cbcl/checkpoint/blob/v1", &self.encode(c))
    }
    pub fn verify(&self, c: &Context, keys: &dyn KeyVerifier) -> Result<Vec<String>> {
        c.validate_runtime(keys)?;
        self.manifest.validate(c)?;
        if hash(b"cbcl/checkpoint/summary/v2", &self.summary) != self.manifest.summary {
            return Err(Error::Invalid("summary hash"));
        }
        let d =
            cbcl_parser::checkpoint_dialect::builtin().map_err(|_| Error::Invalid("builtin"))?;
        let root = c.companion_root.id()?;
        let opener = self.opener.authenticate(keys)?;
        verify_coordination(
            &self.opener,
            c,
            &d,
            core::slice::from_ref(&c.companion_root),
            keys,
        )?;
        if opener.verb != "open" || opener.predecessors != vec![root] {
            return Err(Error::Invalid("companion opener"));
        }
        check_scope(&opener, c, None)?;
        if opener.fields.get("version") != Some(&SExpr::Atom(Atom::Num(1))) {
            return Err(Error::Invalid("opener version"));
        }
        let mut seen = BTreeSet::new();
        let mut previous = None;
        let mut signers = Vec::new();
        if self.endorsements.len() < c.policy.threshold()
            || self.endorsements.len() > c.policy.roster.len()
        {
            return Err(Error::Invalid("endorsement threshold"));
        }
        for e in &self.endorsements {
            let a = e.authenticate(keys)?;
            verify_coordination(
                e,
                c,
                &d,
                &[c.companion_root.clone(), self.opener.clone()],
                keys,
            )?;
            if a.verb != "endorse" || a.predecessors != vec![self.opener.id()?] {
                return Err(Error::Invalid("endorsement verb/parent"));
            }
            check_scope(&a, c, Some(self.manifest.hash()))?;
            let i = c
                .policy
                .roster
                .iter()
                .position(|k| k == &a.signer)
                .ok_or(Error::Invalid("untrusted endorser"))?;
            if previous.is_some_and(|p| p >= i) || !seen.insert(i) {
                return Err(Error::Invalid("distinct sorted endorsers"));
            }
            previous = Some(i);
            signers.push(a.signer);
        }
        Ok(signers)
    }
}
pub fn check_scope(a: &Act, c: &Context, manifest: Option<Hash>) -> Result<()> {
    for (k, v) in [
        ("target", c.target_root.id()?),
        ("context", hex(&c.hash())),
        ("policy", hex(&c.policy.hash())),
        ("profile", hex(&c.profile)),
    ] {
        if a.fields.get(k) != Some(&SExpr::Atom(Atom::Str(v))) {
            return Err(Error::Invalid("coordination scope"));
        }
    }
    if let Some(h) = manifest {
        if a.fields.get("manifest") != Some(&SExpr::Atom(Atom::Str(hex(&h)))) {
            return Err(Error::Invalid("endorsement manifest"));
        }
    }
    Ok(())
}
/// Fully recognize a coordination assertion before deriving any semantic result.
pub fn recognize_coordination(message: &Message, d: &Dialect) -> Result<()> {
    let simple = message
        .innermost_simple()
        .ok_or(Error::Invalid("coordination simple"))?;
    let perf = simple
        .performative()
        .ok_or(Error::Invalid("coordination performative"))?
        .name();
    let expected: &[&str] = match perf {
        "open" => &["target", "context", "policy", "profile", "version"],
        "propose" => &[
            "target",
            "context",
            "policy",
            "profile",
            "manifest",
            "descriptor",
        ],
        "endorse" => &["target", "context", "policy", "profile", "manifest"],
        "publish" => &[
            "target",
            "context",
            "policy",
            "profile",
            "manifest",
            "certificate",
            "locations",
        ],
        _ => return Err(Error::Invalid("coordination verb")),
    };
    let Message::Simple { params, .. } = simple else {
        return Err(Error::Invalid("coordination simple"));
    };
    if params.len() % 2 != 0 {
        return Err(Error::Invalid("coordination fields"));
    }
    let mut seen = BTreeSet::new();
    let mut fields = Vec::new();
    for pair in params.chunks_exact(2) {
        let SExpr::Atom(Atom::Keyword(k)) = &pair[0] else {
            return Err(Error::Invalid("coordination keyword"));
        };
        if !seen.insert(k) {
            return Err(Error::Invalid("duplicate coordination field"));
        }
        if cbcl_core::state::ROUTING_KEYWORDS.contains(&k.as_str()) {
            continue;
        }
        fields.push(k.as_str());
        match k.as_str() {
            "target" => {
                let SExpr::Atom(Atom::Str(id)) = &pair[1] else {
                    return Err(Error::Invalid("target field"));
                };
                native_id(id)?;
            }
            "version" => {
                if pair[1] != SExpr::Atom(Atom::Num(1)) {
                    return Err(Error::Invalid("coordination version"));
                }
            }
            "locations" => {
                let SExpr::List(xs) = &pair[1] else {
                    return Err(Error::Invalid("locations list"));
                };
                if xs.len() > 8 {
                    return Err(Error::Budget);
                }
                for x in xs {
                    if !matches!(x,SExpr::Atom(Atom::Str(s))if s.len()<=2048) {
                        return Err(Error::Invalid("location"));
                    }
                }
            }
            _ => {
                let SExpr::Atom(Atom::Str(s)) = &pair[1] else {
                    return Err(Error::Invalid("hash field"));
                };
                if s.len() != 64 || unhex(s)?.len() != 32 {
                    return Err(Error::Invalid("coordination hash"));
                }
            }
        }
    }
    if fields != expected {
        return Err(Error::Invalid("closed ordered coordination fields"));
    }
    for shape in d.shapes.iter().filter(|s| s.performative == perf) {
        shape
            .check(&SExpr::from(simple.clone()))
            .map_err(|_| Error::Invalid("coordination shape"))?;
    }
    Ok(())
}

pub fn verify_coordination(
    msg: &SignedMessage,
    c: &Context,
    d: &Dialect,
    base: &[SignedMessage],
    keys: &dyn KeyVerifier,
) -> Result<()> {
    let a = msg.authenticate(keys)?;
    let mut store = ThreadedMessageStore::new();
    let root = c.companion_root.id()?;
    let thread = ThreadId(
        c.companion_root
            .message()
            .innermost_simple()
            .and_then(Message::thread)
            .ok_or(Error::Invalid("companion thread"))?
            .into(),
    );
    if msg.message().innermost_simple().and_then(Message::thread) != Some(thread.0.as_str()) {
        return Err(Error::Invalid("foreign or missing companion thread"));
    }
    let mut m = msg.message();
    if let Message::Wrapped {
        wrapper: WrapperType::Signed,
        content,
        ..
    } = m
    {
        m = content;
    }
    if !matches!(m,Message::Dialect{dialect_name,..}if dialect_name==&d.name) {
        return Err(Error::Invalid("native language pin"));
    }
    for b in base {
        b.authenticate(keys)?;
        store.append(ContentHash(b.id()?), thread.clone(), b.message().clone());
    }
    let Message::Wrapped { params, .. } = c.companion_root.message() else {
        return Err(Error::Invalid("cast"));
    };
    let cast = parse_wrapper_cast(params, &d.roles).map_err(|_| Error::Invalid("cast"))?;
    recognize_coordination(msg.message(), d)?;
    cbcl_core::r7::verify_state_shape(d, msg.message())
        .map_err(|_| Error::Invalid("native shape"))?;
    let verdict = verify_causal_for_role(
        msg.message(),
        &Endpoint {
            role: "member".into(),
            occupant: Some(AgentKey(a.signer)),
        },
        d,
        &cast,
        &store,
        &thread,
        &ContentHash(root),
    );
    if verdict != VerificationResult::Valid {
        return Err(Error::Invalid("native causal/role admission"));
    }
    Ok(())
}
