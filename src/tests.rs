use super::*;

#[test]
fn lifetimes() {
    // check that things compile with different lifetimes

    #[allow(unused)]
    struct S {
        inner: String,
    }

    #[allow(unused)]
    enum OneOf<'a, 'b, 'c, 'd> {
        A(&'a str),
        B(&'b str),
        C(&'c str),
        D(&'d str),
    }

    impl<'a, 'b, 'c, 'd> fmt::Display for OneOf<'a, 'b, 'c, 'd> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Self::A(s) => f.write_str(s),
                Self::B(s) => f.write_str(s),
                Self::C(s) => f.write_str(s),
                Self::D(s) => f.write_str(s),
            }
        }
    }

    impl ManifestMut<String> for S {
        type Error = ();

        type State<'s> = (bool, bool, &'s str, String);

        fn init_state(&self) -> Self::State<'_> {
            (true, false, self.inner.trim(), "hello".into())
        }

        fn manifest_mut(
            &self,
            ast: &String,
            state: &mut Self::State<'_>,
        ) -> Result<impl fmt::Display, Self::Error> {
            if state.0 {
                Ok(OneOf::A(&self.inner))
            } else if state.1 {
                Ok(OneOf::B(state.2))
            } else if !state.0 && !state.1 {
                Ok(OneOf::C(ast))
            } else {
                Ok(OneOf::D(&state.3))
            }
        }
    }
}

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
        "A {{brace}}",
        [
            (Span::Text("A "), 0),
            (Span::Text("{brace"), 3),
            (Span::Text("}"), 10),
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

    // whitespace handling is only propagated to the error; we always keep track of
    // the full span internally so that spans are contiguous
    check_parts("A {  b}", [(Span::Text("A "), 0), (Span::Expr("  b"), 3)]);
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
        Err(SyntaxError {
            span: 1..2,
            kind: SyntaxErrorKind::UnclosedExpr
        })
    );

    let mut oneshot = Oneshot::new("{# }");
    assert_eq!(
        oneshot.next_span::<&str, ()>(),
        Err(SyntaxError {
            span: 0..4,
            kind: SyntaxErrorKind::UnclosedExpr
        })
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
        Err(SyntaxError {
            span: 1..2,
            kind: SyntaxErrorKind::ExtraBrace
        })
    );
}

#[test]
fn parse_err_location() {
    let s = "{# bad  #}";
    let mut template_spans = TemplateSpans::<usize>::new(s);
    let err = template_spans.next().unwrap().unwrap_err();

    let usize_err = "bad".parse::<usize>().unwrap_err();

    assert_eq!(
        err,
        SyntaxError {
            span: 3..6,
            kind: SyntaxErrorKind::InvalidExpr(usize_err),
        }
    );

    assert_eq!(&s[err.locate()], "bad");
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
