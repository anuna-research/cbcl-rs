//! SPEC-043 TEST-4308..4310: public keys, bounds and frozen canonical bytes.
use cbcl_core::{
    canonical::{dialect_body_hash, dialect_hash, dialect_name},
    dialect::base_dialect,
    keyid::{KeyId, SignatureSuite},
    multikey::{Multikey, MultikeyError, PublicKeyCodec, MAX_TEXT_BYTES},
    numeric::{Decimal, Float},
    r2::ResourceState,
};

#[test]
fn resource_overflow_refuses_without_panicking() {
    let mut state = ResourceState::new(u32::MAX, u32::MAX);
    state.current_depth = u32::MAX;
    state.expansion_size = u32::MAX - 1;
    assert_eq!(state.enter_depth(), None);
    assert_eq!(state.add_expansion(2), None);
    assert_eq!(state.add_expansion(u32::MAX), None);
    let state = ResourceState::new(2, 3);
    assert!(state.enter_depth().is_some());
    assert!(state.enter_depth().unwrap().enter_depth().is_none());
    assert!(state.add_expansion(2).is_some());
    assert!(state.add_expansion(3).is_none());
}

#[test]
fn frozen_numeric_spellings_cover_binary64_boundaries() {
    let cases = [
        (0.0, "0.0".to_string()),
        (-0.0, "0.0".to_string()),
        (1.0, "1.0".to_string()),
        (
            f64::from_bits(998u64 << 52),
            "0.000000029802322387695313".into(),
        ),
        (
            -f64::from_bits(998u64 << 52),
            "-0.000000029802322387695313".into(),
        ),
        (
            f64::from_bits(1.0f64.to_bits() + 1),
            "1.0000000000000002".into(),
        ),
        (1e20, "100000000000000000000.0".into()),
        (1e-6, "0.000001".into()),
        (f64::from_bits(1), format!("0.{}5", "0".repeat(323))),
        (f64::MAX, format!("17976931348623157{}.0", "0".repeat(292))),
    ];
    for (value, expected) in cases {
        let float = Float::new(value).unwrap();
        assert_eq!(float.to_string(), expected);
        assert_eq!(expected.parse::<Float>().unwrap(), float);
    }
    for (input, expected) in [
        ("-000.000", "0m"),
        ("0012.3400", "12.34m"),
        (
            "123456789012345678901234567890.00000000000000000001",
            "123456789012345678901234567890.00000000000000000001m",
        ),
    ] {
        assert_eq!(input.parse::<Decimal>().unwrap().to_string(), expected);
    }
}

#[test]
fn self_name_is_acyclic_and_distinct_from_named_form_integrity() {
    let mut dialect = base_dialect();
    let body_hash = dialect_body_hash(&dialect);
    let name = dialect_name(&dialect);
    assert_eq!(
        name,
        "f122072473de3c800aabc310df8e6881c194e759d7774e701ec260eab09646d15245e"
    );
    dialect.name = name.clone();
    assert_eq!(dialect_body_hash(&dialect), body_hash);
    assert_eq!(dialect_name(&dialect), name);
    assert_eq!(
        dialect_hash(&dialect),
        "f1220d6c54de6d6e68f6783aaff737c85e705ea184dbe12169af931e769156265b21a"
    );
    assert_ne!(dialect_hash(&dialect), name);
    dialect.hash = Some("ignored integrity metadata".into());
    dialect.signature = Some(vec![1, 2, 3]);
    assert_eq!(dialect_name(&dialect), name);
}

#[test]
fn w3c_ed25519_public_multikey_vector() {
    // https://www.w3.org/TR/2025/REC-cid-1.0-20250515/#multikey
    let text = "z6MkmM42vxfqZQsv4ehtTjFFxQ4sQKS2w6WR7emozFAn5cxu";
    let key = Multikey::parse(text).unwrap();
    assert_eq!(key.codec(), PublicKeyCodec::Ed25519);
    // Independently decoded from the published base58btc value.
    assert_eq!(
        key.public_key_bytes(),
        &[
            0x66, 0x6a, 0xbe, 0x08, 0x90, 0x35, 0xed, 0x4a, 0x45, 0x79, 0x59, 0x89, 0xfa, 0x72,
            0x0a, 0x0e, 0xe0, 0xc4, 0x85, 0x49, 0xe8, 0x45, 0x23, 0x48, 0x5c, 0x56, 0xf1, 0xc8,
            0x1b, 0x42, 0x87, 0xa6,
        ]
    );
    assert_eq!(key.to_string(), text);
    assert_eq!(
        Multikey::new(key.codec(), key.public_key_bytes()).unwrap(),
        key
    );
}

#[test]
fn codec_roundtrips_are_typed_and_bounded() {
    for (codec, size) in [
        (PublicKeyCodec::Ed25519, 32),
        (PublicKeyCodec::X25519, 32),
        (PublicKeyCodec::P256, 33),
        (PublicKeyCodec::P384, 49),
    ] {
        let mut bytes = vec![42; size];
        if matches!(codec, PublicKeyCodec::P256 | PublicKeyCodec::P384) {
            bytes[0] = 2;
        }
        let key = Multikey::new(codec, &bytes).unwrap();
        assert_eq!(Multikey::parse(&key.to_string()).unwrap(), key);
        assert!(key.to_string().len() <= MAX_TEXT_BYTES);
        assert!(Multikey::new(codec, &bytes[..size - 1]).is_err());
        bytes.push(0);
        assert!(Multikey::new(codec, &bytes).is_err());
    }
    assert_eq!(
        Multikey::new(PublicKeyCodec::P256, &[4; 33]),
        Err(MultikeyError::InvalidPublicKey)
    );
}

fn encoded(payload: &[u8]) -> String {
    format!("z{}", bs58::encode(payload).into_string())
}

#[test]
fn malformed_multikeys_fail_closed() {
    for bad in ["", "z", "f00", "uAA", "z0", "zO", "zI", "zl", "zé", "z 1"] {
        assert!(Multikey::parse(bad).is_err(), "{bad}");
    }
    assert!(Multikey::parse(&format!("z{}", "1".repeat(MAX_TEXT_BYTES))).is_err());
    for truncated in [&[0xed][..], &[0x80][..]] {
        assert!(Multikey::parse(&encoded(truncated)).is_err());
    }
    for prefix in [
        vec![0xed, 0x81, 0x00], // Ed25519 with a nonminimal code.
        vec![0xed],             // Unsupported codec when followed by key bytes.
        vec![0x80, 0x26],       // Ed25519 private key (0x1300).
        vec![0x01],             // Unrecognized codec.
        vec![0xff; 11],         // Overflowing varint.
    ] {
        let mut bytes = prefix;
        bytes.extend_from_slice(&[42; 32]);
        assert!(Multikey::parse(&encoded(&bytes)).is_err());
    }
    for size in [0, 31, 33] {
        let mut bytes = vec![0xed, 1];
        bytes.extend(vec![42; size]);
        assert!(Multikey::parse(&encoded(&bytes)).is_err());
    }
}

#[test]
fn explicit_multikey_constructor_preserves_existing_principals() {
    let text = "z6MkmM42vxfqZQsv4ehtTjFFxQ4sQKS2w6WR7emozFAn5cxu";
    let key = Multikey::parse(text).unwrap();
    let derived = KeyId::from_multikey(&key).unwrap();
    let explicit = KeyId::parse(&format!("@ed25519:{text}")).unwrap();
    assert_eq!(derived, explicit);
    assert_eq!(derived.canonical_spelling(), explicit.canonical_spelling());
    // No reinterpretation of previously representable unknown-suite principals.
    let old = KeyId::parse(&format!("@multikey:{text}")).unwrap();
    assert_eq!(old.suite, SignatureSuite::Other("multikey".into()));
    assert_ne!(old, derived);
    let exchange = Multikey::new(PublicKeyCodec::X25519, &[42; 32]).unwrap();
    assert!(KeyId::from_multikey(&exchange).is_err());
    let mut compressed = [42; 33];
    compressed[0] = 2;
    let unsupported = Multikey::new(PublicKeyCodec::P256, &compressed).unwrap();
    assert!(KeyId::from_multikey(&unsupported).is_err());
    assert_eq!(
        KeyId::parse("@alice").unwrap().canonical_spelling(),
        "@ed25519:alice"
    );
}

#[test]
fn multikey_conversion_preserves_attestation_preimages() {
    use cbcl_core::attest::{attestation_preimage, AttestationHeader};
    use std::collections::BTreeSet;
    let text = "z6MkmM42vxfqZQsv4ehtTjFFxQ4sQKS2w6WR7emozFAn5cxu";
    let old_key = KeyId::parse(&format!("@ed25519:{text}")).unwrap();
    let new_key = KeyId::from_multikey(&Multikey::parse(text).unwrap()).unwrap();
    let mut header = AttestationHeader {
        content_hash: cbcl_core::multihash::encode(&[42; 32]),
        performative: "tell".into(),
        from: old_key,
        to: BTreeSet::new(),
        thread: "archived-thread".into(),
        caused_by: None,
    };
    let before = attestation_preimage(&header);
    header.from = new_key;
    assert_eq!(attestation_preimage(&header), before);
    header.from = KeyId::parse(&format!("@multikey:{text}")).unwrap();
    assert_ne!(attestation_preimage(&header), before);
}

proptest::proptest! {
    #[test]
    fn multikey_ed25519_roundtrips_arbitrary_bytes(bytes in proptest::array::uniform32(proptest::num::u8::ANY)) {
        let key = Multikey::new(PublicKeyCodec::Ed25519, &bytes).unwrap();
        proptest::prop_assert_eq!(Multikey::parse(&key.to_string()).unwrap(), key);
    }

    #[test]
    fn multikey_parser_does_not_panic_on_arbitrary_input(text in ".{0,300}") {
        if let Ok(key) = Multikey::parse(&text) {
            proptest::prop_assert_eq!(key.to_string(), text);
        }
    }
}

// Independent exact-rational oracle for the canonical float selection rule.
// Production uses Rust's float formatter; this deliberately uses BigUint division
// and candidate selection instead, so formatter changes can be detected.
fn reference_float_text(value: f64) -> String {
    use num_bigint::BigUint;
    if value == 0.0 {
        return "0.0".into();
    }
    let bits = value.abs().to_bits();
    let exponent = ((bits >> 52) & 0x7ff) as i32;
    let mantissa = (bits & ((1u64 << 52) - 1)) | if exponent == 0 { 0 } else { 1u64 << 52 };
    let binary_scale = if exponent == 0 {
        -1074
    } else {
        exponent - 1023 - 52
    };
    let mut numerator = BigUint::from(mantissa);
    let mut denominator = BigUint::from(1u8);
    if binary_scale >= 0 {
        numerator <<= binary_scale as usize;
    } else {
        denominator <<= -binary_scale as usize;
    }
    let ten = BigUint::from(10u8);
    let mut order =
        numerator.to_str_radix(10).len() as i32 - denominator.to_str_radix(10).len() as i32;
    let below_order = if order >= 0 {
        numerator < &denominator * ten.pow(order as u32)
    } else {
        &numerator * ten.pow(-order as u32) < denominator
    };
    if below_order {
        order -= 1;
    }
    for precision in 1..=17 {
        let scale = order - precision + 1;
        let (n, d) = if scale >= 0 {
            (numerator.clone(), &denominator * ten.pow(scale as u32))
        } else {
            (&numerator * ten.pow(-scale as u32), denominator.clone())
        };
        let lower = &n / &d;
        let remainder = &n % &d;
        let upper = &lower + BigUint::from(1u8);
        let upper_distance = &d - &remainder;
        // Preserve the current profile's decimal tie choice: greater magnitude.
        let candidates = if remainder < upper_distance {
            [lower, upper]
        } else {
            [upper, lower]
        };
        for significand in candidates {
            let digits = significand.to_str_radix(10);
            let point = digits.len() as i32 + scale;
            let mut text = if point <= 0 {
                format!("0.{}{digits}", "0".repeat(-point as usize))
            } else if point as usize >= digits.len() {
                format!("{digits}{}.0", "0".repeat(point as usize - digits.len()))
            } else {
                format!(
                    "{}.{}",
                    &digits[..point as usize],
                    &digits[point as usize..]
                )
            };
            if text.parse::<f64>().unwrap().to_bits() == bits {
                while text.ends_with('0') && !text.ends_with(".0") {
                    text.pop();
                }
                if value.is_sign_negative() {
                    text.insert(0, '-');
                }
                return text;
            }
        }
    }
    panic!("no round-tripping decimal within 17 digits for {bits:016x}")
}

#[test]
fn float_formatter_matches_exact_oracle_at_binary_binades() {
    for exponent in 0..2047u64 {
        let bits = exponent << 52;
        for sample in [bits.saturating_sub(1), bits, bits + 1] {
            let value = f64::from_bits(sample);
            assert_eq!(
                Float::new(value).unwrap().to_string(),
                reference_float_text(value)
            );
        }
    }
}

proptest::proptest! {
    #[test]
    fn float_formatter_matches_exact_rational_oracle(bits in proptest::num::u64::ANY) {
        let value = f64::from_bits(bits);
        proptest::prop_assume!(value.is_finite());
        proptest::prop_assert_eq!(Float::new(value).unwrap().to_string(), reference_float_text(value));
    }
}
