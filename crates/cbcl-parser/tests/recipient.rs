use cbcl_parser::recipient_of;
#[test]
fn audience_golden_corpus() {
    for text in [
        r#"(tell @bob "hello")"#,
        r#"(ask @bob "hello")"#,
        r#"(lang d (tell @bob "hello"))"#,
        r#"(lang d (lang e (ask @bob "hello")))"#,
    ] {
        assert_eq!(recipient_of(text).as_deref(), Ok("@bob"), "{text}");
    }
    for text in [
        r#"(meta (teach @bob (define d (cbcl) @author)))"#,
        r#"(reply "hello")"#,
        r#"(tell "hello")"#,
        r#"(meta (define d (cbcl) @author))"#,
        r#"(tell (@alice @bob) "hello")"#,
        r#"(tell @alice @bob)"#,
    ] {
        assert!(recipient_of(text).is_err(), "{text}");
    }
}

#[test]
fn current_hub_room_corpus() {
    let corpus: serde_json::Value =
        serde_json::from_str(include_str!("../../../test-vectors/frame-rooms.json")).unwrap();
    for row in corpus["rows"].as_array().unwrap() {
        let result = cbcl_parser::recipient_of_lax(row["frame"].as_str().unwrap());
        assert_eq!(
            result.ok().as_deref(),
            row["room"].as_str(),
            "{}",
            row["name"]
        );
    }
}

#[test]
fn envelope_keywords_can_be_in_any_order_and_duplicates_fail_closed() {
    for text in [
        "(envelope :via @other :to @room (tell @bob hello))",
        "(envelope :to @room :via @other (tell @bob hello))",
    ] {
        assert_eq!(recipient_of(text).as_deref(), Ok("@room"));
    }
    assert!(recipient_of("(envelope :to @one :to @two (tell @bob hello))").is_err());
}
