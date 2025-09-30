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
            (Span::Expr("name"), 7),
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
            (Span::Expr(""), 3),
            (Span::Text("}"), 5),
        ],
    );

    check_parts("{## #}##}", [(Span::Expr(" #}"), 3)]);
    check_parts("{# ##}", [(Span::Expr(" #"), 2)]);
    check_parts("{## ####}", [(Span::Expr(" ##"), 3)]);
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
        Err(SyntaxError::UnclosedExpr(1))
    );

    let mut oneshot = Oneshot::new("{# }");
    assert_eq!(
        oneshot.next_span::<&str, ()>(),
        Err(SyntaxError::UnclosedExpr(0))
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

    let mut mfst: HashMap<&'static str, &'static str> = HashMap::new();
    mfst.insert("name", "Alex");
    assert_eq!(template.render(&mfst).unwrap(), "Hello Alex!");

    let mut mfst: HashMap<&'static str, String> = HashMap::new();
    mfst.insert("name", "Bob".to_owned());
    assert_eq!(template.render(&mfst).unwrap(), "Hello Bob!");

    let mfst: HashMap<&'static str, &'static str> = HashMap::new();
    assert!(template.render(&mfst).is_err());

    let template = BorrowedTemplate::<usize>::compile("{1}, {3}").unwrap();
    assert_eq!(
        template
            .render(&|n: &usize| { Ok::<usize, ()>(*n + 3) })
            .unwrap(),
        "4, 6"
    );
    let replace = "123".to_owned();
    assert_eq!(
        template
            .render(&|_: &usize| { Ok::<&str, ()>(&replace) })
            .unwrap(),
        "123, 123"
    );

    fn ident_lifetime<'fmt>(s: &&'fmt str) -> Result<&'fmt str, std::convert::Infallible> {
        Ok(s)
    }
    let template = BorrowedTemplate::<&str>::compile("{sh}").unwrap();
    assert_eq!(template.render(&ident_lifetime).unwrap(), "sh");
}
