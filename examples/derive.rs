//! This example demonstrates the `Ast` derive macro.
use std::{collections::HashMap, fmt, num::ParseIntError, str::FromStr};

use mufmt::{Ast, BorrowedTemplate};

#[derive(Debug, Clone, PartialEq, Eq, Hash, Ast)]
struct UserId(u32);

impl FromStr for UserId {
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.parse().map(UserId)
    }
}

impl fmt::Display for UserId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

fn main() {
    // `Ast` is implemented via the derive macro
    let template = BorrowedTemplate::<UserId>::compile("User ID: {123}").unwrap();

    let mut users: HashMap<UserId, &str> = HashMap::new();
    users.insert(UserId(123), "Alice");
    users.insert(UserId(456), "Bob");

    assert_eq!(template.render(&users).unwrap(), "User ID: Alice");
}
