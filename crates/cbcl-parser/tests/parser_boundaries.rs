use cbcl_parser::parser::{parse, ParseError};

#[test]
fn boundary_rejects_trailing_expressions_at_their_byte_offset() {
    assert_eq!(
        parse("(a)  b"),
        Err(ParseError::UnexpectedChar {
            offset: 5,
            found: 'b',
            expected: "end of input",
        })
    );
}

#[test]
fn boundary_unterminated_list_reports_the_missing_delimiter() {
    assert_eq!(
        parse("(a"),
        Err(ParseError::UnexpectedEof {
            offset: 2,
            expected: "')'",
        })
    );
}

#[test]
fn boundary_malformed_booleans_report_the_character_after_the_hash() {
    // Exercise both zero and nonzero offsets, including UTF-8 before the error.
    for (input, offset) in [("#x", 1), ("(a #x)", 4), ("(\"é\" #x)", 7)] {
        assert_eq!(
            parse(input),
            Err(ParseError::UnexpectedChar {
                offset,
                found: 'x',
                expected: "'t' or 'f'",
            }),
            "{input}"
        );
    }
    for (input, offset) in [("#", 1), ("(a #", 4)] {
        assert_eq!(
            parse(input),
            Err(ParseError::UnexpectedEof {
                offset,
                expected: "'t' or 'f'",
            })
        );
    }
}

#[test]
fn boundary_parser_diagnostics_include_location_and_reason() {
    assert_eq!(
        parse("#x").unwrap_err().to_string(),
        "at byte 1: unexpected 'x', expected 't' or 'f'"
    );
    assert_eq!(
        parse("(a").unwrap_err().to_string(),
        "at byte 2: unexpected end of input, expected ')'"
    );
}

#[test]
fn boundary_symbols_accept_underscores_alongside_letters() {
    assert_eq!(
        parse("hello_world").unwrap(),
        cbcl_core::sexpr::SExpr::Atom(cbcl_core::sexpr::Atom::Symbol("hello_world".into()))
    );
}
