// Tests to check that the README examples work correctly

#[test]
fn example_1() {
    use mufmt::Template;

    use std::collections::HashMap;

    // The `Ast` is &str
    let template = Template::<&str, &str>::compile("Hello {name}!").unwrap();
    // The `Manifest` is `HashMap<str, str>`
    let mfst = HashMap::from([("name", "John")]);

    assert_eq!(template.render(&mfst).unwrap(), "Hello John!");
}

#[test]
fn example_2() {
    use mufmt::Template;

    let s = "Order: {1}".to_owned();

    // The `Ast` is usize; also use a String to store the template text
    // which unlinks the lifetime
    let template = Template::<String, usize>::compile(&s).unwrap();

    // we can drop the original template string
    drop(s);

    // The `Manifest` is `Vec<&str>`
    let mut mfst = vec!["Grapes", "Apples"];
    assert_eq!(template.render(&mfst).unwrap(), "Order: Apples");

    // Render again, but with new data
    mfst.clear();
    mfst.push("Cheese");
    mfst.push("Milk");
    assert_eq!(template.render(&mfst).unwrap(), "Order: Milk");

    // You can even change the type, as long as the `Ast` is the same
    let new_mfst = vec![12, 5];
    assert_eq!(template.render(&new_mfst).unwrap(), "Order: 5");
}
