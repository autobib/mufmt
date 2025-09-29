use super::*;

#[test]
fn parse() {
    fn check_parts<const N: usize>(
        template: &str,
        expected: [(Span<&'static str, &'static str>, usize); N],
    ) {
        let mut oneshot = Oneshot::new(template);
        for (span, offset) in expected.into_iter() {
            assert_eq!(
                oneshot.next_span::<&str, ()>(),
                Ok(Some(IndexedSpan { span, offset }))
            );
        }
    }

    check_parts(
        "Hello {name}!",
        [
            (Span::Text("Hello "), 0),
            (Span::Block("name"), 7),
            (Span::Text("!"), 12),
        ],
    );

    check_parts(
        "A {{bracket}}",
        [
            (Span::Text("A "), 0),
            (Span::Text("{bracket"), 3),
            (Span::Text("}"), 12),
        ],
    );

    check_parts(
        "{{{{}}}}",
        [
            (Span::Text("{"), 1),
            (Span::Text("{"), 3),
            (Span::Text("}"), 5),
            (Span::Text("}"), 7),
        ],
    );

    check_parts(
        "{{{}}}",
        [
            (Span::Text("{"), 1),
            (Span::Block(""), 3),
            (Span::Text("}"), 5),
        ],
    );

    check_parts("{## #}##}", [(Span::Block(" #}"), 3)]);
    check_parts("{# ##}", [(Span::Block(" #"), 2)]);
    check_parts("{## ####}", [(Span::Block(" ##"), 3)]);
}

#[test]
fn parse_err() {
    let mut oneshot = Oneshot::new(" {");
    assert_eq!(
        oneshot.next_span::<&str, ()>(),
        Ok(Some(IndexedSpan {
            span: Span::Text(" "),
            offset: 0
        }))
    );
    assert_eq!(
        oneshot.next_span::<&str, ()>(),
        Err(SyntaxError::UnclosedBlock(1))
    );

    let mut oneshot = Oneshot::new("{# }");
    assert_eq!(
        oneshot.next_span::<&str, ()>(),
        Err(SyntaxError::UnclosedBlock(0))
    );

    let mut oneshot = Oneshot::new(" }");
    assert_eq!(
        oneshot.next_span::<&str, ()>(),
        Ok(Some(IndexedSpan {
            span: Span::Text(" "),
            offset: 0
        }))
    );
    assert_eq!(
        oneshot.next_span::<&str, ()>(),
        Err(SyntaxError::ExtraBracket(1))
    );
}

#[test]
fn render() {
    use std::collections::HashMap;

    let template = BorrowedTemplate::<&str>::compile("Hello {name}!").unwrap();

    let mut ctx: HashMap<&'static str, &'static str> = HashMap::new();
    ctx.insert("name", "Alex");
    assert_eq!(template.render(&ctx).unwrap(), "Hello Alex!");

    let mut ctx: HashMap<&'static str, String> = HashMap::new();
    ctx.insert("name", "Bob".to_owned());
    assert_eq!(template.render(&ctx).unwrap(), "Hello Bob!");

    let ctx: HashMap<&'static str, &'static str> = HashMap::new();
    assert!(template.render(&ctx).is_err());
}
