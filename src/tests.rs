use super::*;

#[test]
fn parse() {
    fn check_parts<const N: usize>(template: &str, expected: [(Part<&'static str>, usize); N]) {
        let mut oneshot = Oneshot::new(template);
        for (part, offset) in expected.into_iter() {
            assert_eq!(
                oneshot.next_part::<()>(),
                Ok(Some(SpannedPart { part, offset }))
            );
        }
    }

    check_parts(
        "Hello {name}!",
        [
            (Part::Text("Hello "), 0),
            (Part::Block("name"), 7),
            (Part::Text("!"), 12),
        ],
    );

    check_parts(
        "A {{bracket}}",
        [
            (Part::Text("A "), 0),
            (Part::Text("{bracket"), 3),
            (Part::Text("}"), 12),
        ],
    );

    check_parts(
        "{{{{}}}}",
        [
            (Part::Text("{"), 1),
            (Part::Text("{"), 3),
            (Part::Text("}"), 5),
            (Part::Text("}"), 7),
        ],
    );

    check_parts(
        "{{{}}}",
        [
            (Part::Text("{"), 1),
            (Part::Block(""), 3),
            (Part::Text("}"), 5),
        ],
    );

    check_parts("{## #}##}", [(Part::Block(" #}"), 3)]);
    check_parts("{# ##}", [(Part::Block(" #"), 2)]);
    check_parts("{## ####}", [(Part::Block(" ##"), 3)]);
}

#[test]
fn parse_err() {
    let mut oneshot = Oneshot::new(" {");
    assert_eq!(
        oneshot.next_part::<()>(),
        Ok(Some(SpannedPart {
            part: Part::Text(" "),
            offset: 0
        }))
    );
    assert_eq!(
        oneshot.next_part::<()>(),
        Err(SyntaxError::UnclosedBlock(1))
    );

    let mut oneshot = Oneshot::new("{# }");
    assert_eq!(
        oneshot.next_part::<()>(),
        Err(SyntaxError::UnclosedBlock(0))
    );

    let mut oneshot = Oneshot::new(" }");
    assert_eq!(
        oneshot.next_part::<()>(),
        Ok(Some(SpannedPart {
            part: Part::Text(" "),
            offset: 0
        }))
    );
    assert_eq!(oneshot.next_part::<()>(), Err(SyntaxError::ExtraBracket(1)));
}

#[test]
fn render() {
    use std::collections::HashMap;

    let template = Template::compile("Hello {name}!").unwrap();

    let mut ctx: HashMap<&'static str, &'static str> = HashMap::new();
    ctx.insert("name", "Alex");
    assert_eq!(template.render(&ctx).unwrap(), "Hello Alex!");

    let mut ctx: HashMap<&'static str, String> = HashMap::new();
    ctx.insert("name", "Bob".to_owned());
    assert_eq!(template.render(&ctx).unwrap(), "Hello Bob!");

    let ctx: HashMap<&'static str, &'static str> = HashMap::new();
    assert!(template.render(&ctx).is_err());
}
