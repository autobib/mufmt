//! ### An example template language
//! To understand how these two phases interact, let's define a custom template language. The idea
//! will be as follows:
//! - The user will provide blocks of the form `{<str>:<u8>}`, which is then
//!   formatted to repeat the provided `<str>` `<u8>` times. For example, the
//!   template `"{ AB : 3 }"` renders to `ABABAB`.
//! - Since we don't want the strings to be too long, we will provide an additional
//!   `u8` which will specify a limit for the number of repetitions.

use mufmt::{Ast, Manifest};
use std::{convert::Infallible, fmt, num::ParseIntError};

// First, we must determine our intermediate `Ast` type. The natural candidate here is a
// tuple `(&'fmt, u8)`.
struct Repeat<'fmt>(&'fmt str, u8);

// We also need an error type, which will result during template compilation.
#[derive(Debug)]
pub enum Error {
    /// Failed to parse the int
    InvalidInt(ParseIntError),
    /// Missing the `:` delimeter
    MissingDelimeter,
}

// Now, we implement `Ast`. We can borrow from the template string to save some allocations.
impl<'fmt> Ast<'fmt> for Repeat<'fmt> {
    type Error = Error;

    /// Parse a block of the form `{<str> : <u8>}`
    fn from_block(block: &'fmt str) -> Result<Self, Self::Error> {
        match block.split_once(':') {
            Some((left, right)) => {
                // parse the u8 using `u8::from_str`
                let count = right.trim().parse().map_err(Error::InvalidInt)?;

                Ok(Self(left.trim(), count))
            }
            None => Err(Error::MissingDelimeter),
        }
    }
}

// Implement `Display` so we can use it as the return type for `Manifest::render`
// as well.
impl<'fmt> fmt::Display for Repeat<'fmt> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for _ in 0..self.1 {
            f.write_str(self.0)?;
        }
        Ok(())
    }
}

/// The context information used to render the `Ast`
pub struct Limit(u8);

impl Manifest<Repeat<'_>> for Limit {
    // rendering never produces an error
    type Error = Infallible;

    fn manifest(&self, ast: &Repeat<'_>) -> Result<impl fmt::Display, Self::Error> {
        // limit the number of repetitions to the provided value
        let reps = ast.1.min(self.0);
        Ok(Repeat(ast.0, reps))
    }
}

#[test]
fn test() {
    use mufmt::BorrowedTemplate;

    let template = BorrowedTemplate::compile("{%: 7}!").unwrap();

    assert_eq!(template.render(&Limit(10)).unwrap(), "%%%%%%%!");
    assert_eq!(template.render(&Limit(3)).unwrap(), "%%%!");
}
