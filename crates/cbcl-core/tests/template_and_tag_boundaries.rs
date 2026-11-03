use cbcl_core::msg_tag::{msg_tag, MsgTag};
use cbcl_core::r2::ResourceState;
use cbcl_core::sexpr::SExpr;
use cbcl_core::template::{expand_template_with_bindings, Bindings, ExpandedTemplate};

#[test]
fn boundary_only_lang_uses_the_second_symbol_as_a_tag() {
    for input in ["(tell payload)", "(tell)", "(lang)"] {
        let expr: SExpr = input.parse().unwrap();
        let head = if input.starts_with("(lang") {
            "lang"
        } else {
            "tell"
        };
        assert_eq!(msg_tag(&expr), MsgTag::Head(head.into()), "{input}");
    }
}

#[test]
fn boundary_malformed_conditional_clauses_fail_without_panicking() {
    for input in [
        "(cond ())",
        "(cond ((= x x)))",
        "(cond ((= x x) yes extra))",
    ] {
        let template: SExpr = input.parse().unwrap();
        assert_eq!(
            expand_template_with_bindings(
                &template,
                &Bindings::new(),
                &mut ResourceState::new(8, 512)
            ),
            None,
            "{input}"
        );
    }
}

#[test]
fn boundary_malformed_conditions_do_not_select_a_branch() {
    for input in [
        "(cond ((= x) yes) (else no))",
        "(cond ((= x x extra) yes) (else no))",
    ] {
        let template: SExpr = input.parse().unwrap();
        assert_eq!(
            expand_template_with_bindings(
                &template,
                &Bindings::new(),
                &mut ResourceState::new(8, 512)
            ),
            Some(ExpandedTemplate::Single("no".parse().unwrap())),
            "{input}"
        );
    }
}

#[test]
fn boundary_empty_nested_lists_remain_plain_expressions() {
    let template: SExpr = "(())".parse().unwrap();
    assert_eq!(
        expand_template_with_bindings(&template, &Bindings::new(), &mut ResourceState::new(8, 512)),
        Some(ExpandedTemplate::Single(template))
    );
}
