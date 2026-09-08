//! Message parser: SExpr → Message.
//!
//! Mirrors `parse-cbcl-message-legacy` in `cbcl.scm:300–326`.
//! Delegates to `Message::try_from(&SExpr)` for structural parsing.

#![forbid(unsafe_code)]

use alloc::string::String;
use cbcl_core::message::Message;
use cbcl_core::sexpr::SExpr;

/// Parse an S-expression into a Message (REQ-044).
///
/// Classification (matching `parse-cbcl-message-legacy`):
/// - `(meta operation)` → Meta
/// - `(lang dialect-name inner)` → Dialect
/// - `(envelope ...)` / `(signed ...)` / `(with-limits ...)` → Wrapped
/// - `(performative params...)` → Simple
pub fn parse_message(sexpr: &SExpr) -> Result<Message, String> {
    Message::try_from(sexpr).map_err(|e| e.0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::string::String;
    use alloc::vec;
    use cbcl_core::message::{CorePerformative, MessageType, Performative, WrapperType};
    use cbcl_core::sexpr::Atom;

    fn sym(s: &str) -> SExpr {
        SExpr::Atom(Atom::Symbol(String::from(s)))
    }

    fn str_expr(s: &str) -> SExpr {
        SExpr::Atom(Atom::Str(String::from(s)))
    }

    fn list(items: Vec<SExpr>) -> SExpr {
        SExpr::List(items)
    }

    #[test]
    fn parse_simple_tell() {
        let msg = list(vec![sym("tell"), str_expr("hello")]);
        let m = parse_message(&msg).unwrap();
        assert_eq!(m.message_type(), MessageType::Simple);
        assert_eq!(
            m.performative(),
            Some(&Performative::Core(CorePerformative::Tell))
        );
        assert_eq!(m.content(), Some(&str_expr("hello")));
    }

    #[test]
    fn parse_all_core_performatives() {
        for name in &[
            "tell", "ask", "reply", "error", "ok", "cancel", "hello", "bye",
        ] {
            let msg = list(vec![sym(name), str_expr("arg")]);
            let m = parse_message(&msg).unwrap();
            assert_eq!(m.message_type(), MessageType::Simple);
            assert!(m.performative().unwrap().is_core());
        }
    }

    #[test]
    fn parse_custom_performative() {
        let inner = list(vec![sym("propose-step"), sym("s1"), sym("pickup")]);
        assert!(parse_message(&inner).is_err());
        let msg = list(vec![sym("lang"), sym("cbcl-planning"), inner]);
        let m = parse_message(&msg).unwrap();
        assert_eq!(m.message_type(), MessageType::Dialect);
        assert_eq!(
            m.innermost_simple().unwrap().performative(),
            Some(&Performative::Custom(String::from("propose-step")))
        );
        // s1 is content, pickup is param
        assert_eq!(m.innermost_simple().unwrap().content(), Some(&sym("s1")));
        if let Some(Message::Simple { params, .. }) = m.inner_message() {
            assert_eq!(params.len(), 1);
        }
    }

    #[test]
    fn custom_performatives_require_lang_through_wrappers() {
        for input in [
            "(ship parcel)",
            "(signed signature (ship parcel))",
            "(with-limits () (signed signature (ship parcel)))",
            "(envelope :from @alice (ship parcel))",
        ] {
            let sexpr = crate::parse(input).unwrap();
            assert!(parse_message(&sexpr).is_err(), "must reject {input}");
            assert!(Message::try_from(&sexpr).is_err());
        }
        for input in [
            "(lang logistics (ship parcel))",
            "(lang logistics (signed signature (ship parcel)))",
            "(signed signature (lang logistics (ship parcel)))",
            "(lang outer (with-limits () (lang logistics (ship parcel))))",
        ] {
            let sexpr = crate::parse(input).unwrap();
            let msg = parse_message(&sexpr).expect(input);
            assert_eq!(
                msg.innermost_simple()
                    .unwrap()
                    .performative()
                    .unwrap()
                    .name(),
                "ship"
            );
            assert_eq!(parse_message(&SExpr::from(&msg)).unwrap(), msg);
        }
    }

    #[test]
    fn parse_meta_message() {
        let meta_op = list(vec![sym("define"), sym("my-dialect"), list(vec![])]);
        let msg = list(vec![sym("meta"), meta_op.clone()]);
        let m = parse_message(&msg).unwrap();
        assert_eq!(m.message_type(), MessageType::Meta);
        assert_eq!(m.dialect_def(), Some(&meta_op));
    }

    #[test]
    fn parse_dialect_message() {
        let inner = list(vec![sym("propose-step"), sym("s1")]);
        let msg = list(vec![sym("lang"), sym("cbcl-planning"), inner]);
        let m = parse_message(&msg).unwrap();
        assert_eq!(m.message_type(), MessageType::Dialect);
        assert_eq!(m.dialect_name(), Some("cbcl-planning"));
    }

    #[test]
    fn parse_wrapped_envelope() {
        let msg = list(vec![
            sym("envelope"),
            SExpr::Atom(Atom::Keyword("from".into())),
            sym("@alice"),
            list(vec![sym("tell"), str_expr("hi")]),
        ]);
        let m = parse_message(&msg).unwrap();
        assert_eq!(m.message_type(), MessageType::Wrapped);
        assert_eq!(m.wrapper_type(), Some(WrapperType::Envelope));
    }

    #[test]
    fn parse_wrapped_signed() {
        let msg = list(vec![
            sym("signed"),
            str_expr("sig"),
            list(vec![sym("ok"), str_expr("ack")]),
        ]);
        let m = parse_message(&msg).unwrap();
        assert_eq!(m.message_type(), MessageType::Wrapped);
        assert_eq!(m.wrapper_type(), Some(WrapperType::Signed));
    }

    #[test]
    fn parse_wrapped_with_limits() {
        let msg = list(vec![
            sym("with-limits"),
            list(vec![]),
            list(vec![sym("tell"), str_expr("hi")]),
        ]);
        let m = parse_message(&msg).unwrap();
        assert_eq!(m.message_type(), MessageType::Wrapped);
        assert_eq!(m.wrapper_type(), Some(WrapperType::WithLimits));
    }

    #[test]
    fn parse_with_thread_keyword() {
        let msg = list(vec![
            sym("tell"),
            str_expr("hello"),
            SExpr::Atom(Atom::Keyword(String::from("thread"))),
            sym("planning-session"),
        ]);
        let m = parse_message(&msg).unwrap();
        assert_eq!(m.thread(), Some("planning-session"));
        // :thread and value filtered out; content is "hello"
        if let Message::Simple { params, .. } = &m {
            assert!(params.is_empty());
        }
    }

    #[test]
    fn reject_empty_list() {
        assert!(parse_message(&list(vec![])).is_err());
    }

    #[test]
    fn reject_non_list() {
        assert!(parse_message(&sym("hello")).is_err());
    }

    #[test]
    fn reject_non_symbol_head() {
        assert!(parse_message(&list(vec![str_expr("tell")])).is_err());
    }

    #[test]
    fn parse_from_text() {
        let input = "(lang cbcl-planning (share-conditional pickup box-location box-in-hand))";
        let sexpr = crate::parser::parse(input).unwrap();
        let m = parse_message(&sexpr).unwrap();
        assert_eq!(
            m.innermost_simple().unwrap().performative(),
            Some(&Performative::Custom(String::from("share-conditional")))
        );
        // pickup is content, box-location and box-in-hand are params
        if let Some(Message::Simple { params, .. }) = m.inner_message() {
            assert_eq!(params.len(), 2);
        }
    }

    #[test]
    fn parse_test_vector_messages() {
        // dial-msg-001
        let input = "(lang cbcl-planning (share-conditional pickup box-location box-in-hand))";
        let sexpr = crate::parser::parse(input).unwrap();
        let m = parse_message(&sexpr).unwrap();
        assert_eq!(
            m.innermost_simple().unwrap().performative(),
            Some(&Performative::Custom("share-conditional".into()))
        );

        // dial-msg-003
        let input =
            "(lang agriculture (plant \"field-test\" \"corn\" \"30000\" \"2-in\" \"30-in\"))";
        let sexpr = crate::parser::parse(input).unwrap();
        let m = parse_message(&sexpr).unwrap();
        assert_eq!(
            m.innermost_simple().unwrap().performative(),
            Some(&Performative::Custom("plant".into()))
        );
        // "field-test" is content, rest are params
        if let Some(Message::Simple { params, .. }) = m.inner_message() {
            assert_eq!(params.len(), 4);
        }
    }

    // -----------------------------------------------------------------------
    // Test vector integration: simple messages (msg-simple-*)
    // -----------------------------------------------------------------------

    fn parse_text(input: &str) -> Message {
        let sexpr = crate::parser::parse(input).unwrap();
        parse_message(&sexpr).unwrap()
    }

    #[test]
    fn tv_simple_001_basic_tell() {
        let m = parse_text("(tell @bob \"The meeting is at 3pm\")");
        assert_eq!(m.message_type(), MessageType::Simple);
        assert_eq!(
            m.performative(),
            Some(&Performative::Core(CorePerformative::Tell))
        );
        assert_eq!(m.recipient(), Some("@bob"));
        assert_eq!(m.content(), Some(&str_expr("The meeting is at 3pm")));
    }

    #[test]
    fn tv_simple_002_ask_with_keywords() {
        let m = parse_text("(ask @alice \"What is the status?\" :thread \"conv-17\" :timeout 30)");
        assert_eq!(
            m.performative(),
            Some(&Performative::Core(CorePerformative::Ask))
        );
        assert_eq!(m.recipient(), Some("@alice"));
        assert_eq!(m.content(), Some(&str_expr("What is the status?")));
        assert_eq!(m.thread(), Some("conv-17"));
        // :timeout 30 should be in params
        if let Message::Simple { params, .. } = &m {
            assert_eq!(params.len(), 2); // :timeout, 30
        }
    }

    #[test]
    fn tv_simple_003_reply_with_thread() {
        let m = parse_text("(reply \"Task is complete\" :thread \"conv-17\")");
        assert_eq!(
            m.performative(),
            Some(&Performative::Core(CorePerformative::Reply))
        );
        assert!(m.recipient().is_none());
        assert_eq!(m.content(), Some(&str_expr("Task is complete")));
        assert_eq!(m.thread(), Some("conv-17"));
    }

    #[test]
    fn tv_simple_004_tell_sexpr_content() {
        let m = parse_text("(tell @alice (greeting \"hello\"))");
        assert_eq!(
            m.performative(),
            Some(&Performative::Core(CorePerformative::Tell))
        );
        assert_eq!(m.recipient(), Some("@alice"));
        // content is (greeting "hello")
        assert_eq!(
            m.content(),
            Some(&list(vec![sym("greeting"), str_expr("hello")]))
        );
    }

    #[test]
    fn tv_simple_005_tell_string_content() {
        let m = parse_text("(tell @bob \"Hello world\")");
        assert_eq!(m.content(), Some(&str_expr("Hello world")));
    }

    #[test]
    fn tv_simple_006_tell_with_thread_and_priority() {
        let m = parse_text("(tell @alice \"Status update\" :thread \"conv-123\" :priority high)");
        assert_eq!(m.thread(), Some("conv-123"));
        // :priority high in params
        if let Message::Simple { params, .. } = &m {
            assert_eq!(params.len(), 2);
        }
    }

    #[test]
    fn tv_simple_007_ok() {
        let m = parse_text("(ok @alice \"acknowledged\")");
        assert_eq!(
            m.performative(),
            Some(&Performative::Core(CorePerformative::Ok))
        );
    }

    #[test]
    fn tv_simple_008_error() {
        let m = parse_text("(error @bob \"invalid request\")");
        assert_eq!(
            m.performative(),
            Some(&Performative::Core(CorePerformative::Error))
        );
    }

    #[test]
    fn tv_simple_009_cancel() {
        let m = parse_text("(cancel @alice \"abort task\")");
        assert_eq!(
            m.performative(),
            Some(&Performative::Core(CorePerformative::Cancel))
        );
    }

    #[test]
    fn tv_simple_010_hello() {
        let m = parse_text("(hello @bob \"greetings\")");
        assert_eq!(
            m.performative(),
            Some(&Performative::Core(CorePerformative::Hello))
        );
    }

    #[test]
    fn tv_simple_011_bye() {
        let m = parse_text("(bye @bob \"farewell\")");
        assert_eq!(
            m.performative(),
            Some(&Performative::Core(CorePerformative::Bye))
        );
    }

    // -----------------------------------------------------------------------
    // Test vector integration: meta messages (msg-meta-*)
    // -----------------------------------------------------------------------

    #[test]
    fn tv_meta_001_query_speak() {
        let m = parse_text("(meta (query (speak? logistics)))");
        assert_eq!(m.message_type(), MessageType::Meta);
        let def = m.dialect_def().unwrap();
        // (query (speak? logistics))
        if let SExpr::List(items) = def {
            assert!(items[0] == sym("query"));
        } else {
            panic!("expected list");
        }
    }

    #[test]
    fn tv_meta_002_query_cbcl() {
        let m = parse_text("(meta (query (speak? cbcl)))");
        assert_eq!(m.message_type(), MessageType::Meta);
    }

    #[test]
    fn tv_meta_003_query_precision_ag() {
        let m = parse_text("(meta (query (speak? precision-ag)))");
        assert_eq!(m.message_type(), MessageType::Meta);
    }

    #[test]
    fn tv_meta_004_define() {
        let m = parse_text("(meta (define test-dialect))");
        assert_eq!(m.message_type(), MessageType::Meta);
    }

    #[test]
    fn tv_meta_005_define_with_extends() {
        let m = parse_text("(meta (define planning-v2 :extends cbcl :author @alice))");
        assert_eq!(m.message_type(), MessageType::Meta);
    }

    // -----------------------------------------------------------------------
    // Test vector integration: lang messages (msg-lang-*)
    // -----------------------------------------------------------------------

    #[test]
    fn tv_lang_001_logistics() {
        let m = parse_text("(lang logistics (tell @system \"PKG-123\"))");
        assert_eq!(m.message_type(), MessageType::Dialect);
        assert_eq!(m.dialect_name(), Some("logistics"));
        let inner = m.inner_message().unwrap();
        assert_eq!(inner.message_type(), MessageType::Simple);
        assert_eq!(
            inner.performative(),
            Some(&Performative::Core(CorePerformative::Tell))
        );
        assert_eq!(inner.recipient(), Some("@system"));
        assert_eq!(inner.content(), Some(&str_expr("PKG-123")));
    }

    #[test]
    fn tv_lang_002_precision_ag() {
        let m = parse_text("(lang precision-ag (tell @farmer \"plant\"))");
        assert_eq!(m.dialect_name(), Some("precision-ag"));
        let inner = m.inner_message().unwrap();
        assert_eq!(inner.recipient(), Some("@farmer"));
        assert_eq!(inner.content(), Some(&str_expr("plant")));
    }

    // -----------------------------------------------------------------------
    // Test vector integration: wrapped messages (msg-wrap-*)
    // -----------------------------------------------------------------------

    #[test]
    fn tv_wrap_001_envelope() {
        let m = parse_text("(envelope :from @alice :to @bob (tell @bob \"Hello\"))");
        assert_eq!(m.message_type(), MessageType::Wrapped);
        assert_eq!(m.wrapper_type(), Some(WrapperType::Envelope));
        if let Message::Wrapped { params, .. } = &m {
            // :from @alice :to @bob
            assert_eq!(params.len(), 4);
        }
        let inner = m.inner_message().unwrap();
        assert_eq!(
            inner.performative(),
            Some(&Performative::Core(CorePerformative::Tell))
        );
    }

    #[test]
    fn tv_wrap_002_envelope_timestamp() {
        let m = parse_text(
            "(envelope :from @alice :timestamp \"2025-01-15T14:30:00Z\" (tell @bob \"Wrapped message\"))",
        );
        assert_eq!(m.wrapper_type(), Some(WrapperType::Envelope));
        if let Message::Wrapped { params, .. } = &m {
            // :from @alice :timestamp "2025-01-15T14:30:00Z"
            assert_eq!(params.len(), 4);
        }
    }

    #[test]
    fn tv_wrap_003_signed() {
        let m = parse_text("(signed \"base64signature\" (tell @bob \"Verified message\"))");
        assert_eq!(m.wrapper_type(), Some(WrapperType::Signed));
        if let Message::Wrapped { params, .. } = &m {
            assert_eq!(params, &[str_expr("base64signature")]);
        }
    }

    #[test]
    fn tv_wrap_004_with_limits() {
        let m = parse_text("(with-limits :depth 10 :cpu 100 (tell @bob \"Constrained\"))");
        assert_eq!(m.wrapper_type(), Some(WrapperType::WithLimits));
    }

    #[test]
    fn tv_wrap_005_with_limits_max() {
        let m = parse_text(
            "(with-limits :max-depth 16 :max-expansion-size 1024 (tell @alice \"bounded\"))",
        );
        assert_eq!(m.wrapper_type(), Some(WrapperType::WithLimits));
    }

    #[test]
    fn tv_wrap_006_signed_alt() {
        let m = parse_text("(signed \"base64sig==\" (tell @alice \"verified\"))");
        assert_eq!(m.wrapper_type(), Some(WrapperType::Signed));
        let inner = m.inner_message().unwrap();
        assert_eq!(inner.recipient(), Some("@alice"));
    }

    // -----------------------------------------------------------------------
    // Test vector integration: invalid messages (msg-inv-*)
    // -----------------------------------------------------------------------

    #[test]
    fn tv_inv_003_empty_message() {
        let sexpr = crate::parser::parse("()").unwrap();
        assert!(parse_message(&sexpr).is_err());
    }

    #[test]
    fn tv_inv_004_unclosed_paren() {
        assert!(crate::parser::parse("(tell @bob \"hello\"").is_err());
    }

    #[test]
    fn tv_inv_006_keyword_missing_value() {
        let sexpr = crate::parser::parse("(tell @alice \"hello\" :thread)").unwrap();
        assert!(parse_message(&sexpr).is_err());
    }

    #[test]
    fn tv_inv_007_unterminated_string() {
        assert!(crate::parser::parse("(tell @bob \"hello)").is_err());
    }

    // -----------------------------------------------------------------------
    // Test vector integration: string parsing (msg-str-*)
    // -----------------------------------------------------------------------

    #[test]
    fn tv_str_001_simple_string() {
        let sexpr = crate::parser::parse("\"hello\"").unwrap();
        assert_eq!(sexpr, SExpr::Atom(Atom::Str("hello".into())));
    }

    #[test]
    fn tv_str_002_newline_escape() {
        let sexpr = crate::parser::parse("\"hello\\nworld\"").unwrap();
        assert_eq!(sexpr, SExpr::Atom(Atom::Str("hello\nworld".into())));
    }

    #[test]
    fn tv_str_003_tab_escape() {
        let sexpr = crate::parser::parse("\"hello\\tworld\"").unwrap();
        assert_eq!(sexpr, SExpr::Atom(Atom::Str("hello\tworld".into())));
    }

    #[test]
    fn tv_str_004_escaped_quotes() {
        let sexpr = crate::parser::parse("\"say \\\"hi\\\"\"").unwrap();
        assert_eq!(sexpr, SExpr::Atom(Atom::Str("say \"hi\"".into())));
    }

    #[test]
    fn tv_str_005_escaped_backslashes() {
        let sexpr = crate::parser::parse("\"path\\\\to\\\\file\"").unwrap();
        assert_eq!(sexpr, SExpr::Atom(Atom::Str("path\\to\\file".into())));
    }

    #[test]
    fn tv_str_006_identifier() {
        let sexpr = crate::parser::parse("hello").unwrap();
        assert_eq!(sexpr, SExpr::Atom(Atom::Symbol("hello".into())));
    }

    #[test]
    fn tv_str_007_number() {
        let sexpr = crate::parser::parse("42").unwrap();
        assert_eq!(sexpr, SExpr::Atom(Atom::Num(42)));
    }

    #[test]
    fn tv_str_008_bool_true() {
        let sexpr = crate::parser::parse("#t").unwrap();
        assert_eq!(sexpr, SExpr::Atom(Atom::Bool(true)));
    }

    #[test]
    fn tv_str_009_bool_false() {
        let sexpr = crate::parser::parse("#f").unwrap();
        assert_eq!(sexpr, SExpr::Atom(Atom::Bool(false)));
    }

    #[test]
    fn tv_str_010_agent_id() {
        let sexpr = crate::parser::parse("@alice").unwrap();
        assert_eq!(sexpr, SExpr::Atom(Atom::Symbol("@alice".into())));
    }

    #[test]
    fn tv_str_011_keyword() {
        let sexpr = crate::parser::parse(":thread").unwrap();
        assert_eq!(sexpr, SExpr::Atom(Atom::Keyword("thread".into())));
    }

    #[test]
    fn tv_str_012_identifier_hyphens() {
        let sexpr = crate::parser::parse("my-variable").unwrap();
        assert_eq!(sexpr, SExpr::Atom(Atom::Symbol("my-variable".into())));
    }

    #[test]
    fn tv_str_013_identifier_underscores() {
        let sexpr = crate::parser::parse("my_var").unwrap();
        assert_eq!(sexpr, SExpr::Atom(Atom::Symbol("my_var".into())));
    }

    #[test]
    fn tv_str_014_sequence_parsing() {
        let sexpr = crate::parser::parse("(hello)").unwrap();
        assert_eq!(
            sexpr,
            SExpr::List(vec![SExpr::Atom(Atom::Symbol("hello".into()))])
        );
    }

    // -----------------------------------------------------------------------
    // Test vector integration: canonicalization (msg-canon-*)
    // -----------------------------------------------------------------------

    #[test]
    fn tv_canon_001_already_canonical() {
        let input = "(tell @alice (greeting \"hello\"))";
        let sexpr = crate::parser::parse(input).unwrap();
        let m = parse_message(&sexpr).unwrap();
        let back = SExpr::from(m);
        assert_eq!(back.to_string(), input);
    }

    // -----------------------------------------------------------------------
    // Roundtrip: parse text → Message → SExpr → text
    // -----------------------------------------------------------------------

    #[test]
    fn roundtrip_all_simple_vectors() {
        for input in &[
            "(tell @bob \"The meeting is at 3pm\")",
            "(reply \"Task is complete\" :thread \"conv-17\")",
            "(tell @alice (greeting \"hello\"))",
            "(tell @bob \"Hello world\")",
            "(ok @alice \"acknowledged\")",
            "(error @bob \"invalid request\")",
            "(cancel @alice \"abort task\")",
            "(hello @bob \"greetings\")",
            "(bye @bob \"farewell\")",
        ] {
            let sexpr = crate::parser::parse(input).unwrap();
            let msg = parse_message(&sexpr).unwrap();
            let back = SExpr::from(msg);
            assert_eq!(back.to_string(), *input, "roundtrip failed for: {input}");
        }
    }

    #[test]
    fn roundtrip_meta_vectors() {
        for input in &[
            "(meta (query (speak? logistics)))",
            "(meta (query (speak? cbcl)))",
            "(meta (query (speak? precision-ag)))",
            "(meta (define test-dialect))",
        ] {
            let sexpr = crate::parser::parse(input).unwrap();
            let msg = parse_message(&sexpr).unwrap();
            let back = SExpr::from(msg);
            assert_eq!(back.to_string(), *input, "roundtrip failed for: {input}");
        }
    }

    #[test]
    fn roundtrip_lang_vectors() {
        for input in &[
            "(lang logistics (tell @system \"PKG-123\"))",
            "(lang precision-ag (tell @farmer \"plant\"))",
        ] {
            let sexpr = crate::parser::parse(input).unwrap();
            let msg = parse_message(&sexpr).unwrap();
            let back = SExpr::from(msg);
            assert_eq!(back.to_string(), *input, "roundtrip failed for: {input}");
        }
    }

    #[test]
    fn roundtrip_wrapped_vectors() {
        for input in &[
            "(signed \"base64signature\" (tell @bob \"Verified message\"))",
            "(signed \"base64sig==\" (tell @alice \"verified\"))",
        ] {
            let sexpr = crate::parser::parse(input).unwrap();
            let msg = parse_message(&sexpr).unwrap();
            let back = SExpr::from(msg);
            assert_eq!(back.to_string(), *input, "roundtrip failed for: {input}");
        }
    }

    // -----------------------------------------------------------------------
    // Deterministic msg_tag dispatch (mirrors Lean msgTag)
    // -----------------------------------------------------------------------

    #[test]
    fn msg_tag_dispatch_consistency() {
        use cbcl_core::msg_tag::{msg_tag, MsgTag};

        // Simple messages → Head tag
        let sexpr = crate::parser::parse("(tell @bob \"hi\")").unwrap();
        assert_eq!(msg_tag(&sexpr), MsgTag::Head("tell".into()));
        assert_eq!(
            parse_message(&sexpr).unwrap().message_type(),
            MessageType::Simple
        );

        // Meta → Head tag "meta"
        let sexpr = crate::parser::parse("(meta (query (speak? cbcl)))").unwrap();
        assert_eq!(msg_tag(&sexpr), MsgTag::Head("meta".into()));
        assert_eq!(
            parse_message(&sexpr).unwrap().message_type(),
            MessageType::Meta
        );

        // Lang → HeadAndSecond tag
        let sexpr = crate::parser::parse("(lang logistics (tell @system \"PKG-123\"))").unwrap();
        assert_eq!(
            msg_tag(&sexpr),
            MsgTag::HeadAndSecond("lang".into(), "logistics".into())
        );
        assert_eq!(
            parse_message(&sexpr).unwrap().message_type(),
            MessageType::Dialect
        );

        // Wrapped → Head tag for wrapper
        for wrapper in &["envelope", "signed", "with-limits"] {
            let input = alloc::format!("({wrapper} (tell @bob \"hi\"))");
            let sexpr = crate::parser::parse(&input).unwrap();
            assert_eq!(msg_tag(&sexpr), MsgTag::Head(String::from(*wrapper)));
            assert_eq!(
                parse_message(&sexpr).unwrap().message_type(),
                MessageType::Wrapped
            );
        }
    }
}
