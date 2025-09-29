[![Current crates.io release](https://img.shields.io/crates/v/mufmt)](https://crates.io/crates/mufmt)
[![Documentation](https://img.shields.io/badge/docs.rs-mufmt-66c2a5?labelColor=555555&logoColor=white&logo=data:image/svg+xml;base64,PHN2ZyByb2xlPSJpbWciIHhtbG5zPSJodHRwOi8vd3d3LnczLm9yZy8yMDAwL3N2ZyIgdmlld0JveD0iMCAwIDUxMiA1MTIiPjxwYXRoIGZpbGw9IiNmNWY1ZjUiIGQ9Ik00ODguNiAyNTAuMkwzOTIgMjE0VjEwNS41YzAtMTUtOS4zLTI4LjQtMjMuNC0zMy43bC0xMDAtMzcuNWMtOC4xLTMuMS0xNy4xLTMuMS0yNS4zIDBsLTEwMCAzNy41Yy0xNC4xIDUuMy0yMy40IDE4LjctMjMuNCAzMy43VjIxNGwtOTYuNiAzNi4yQzkuMyAyNTUuNSAwIDI2OC45IDAgMjgzLjlWMzk0YzAgMTMuNiA3LjcgMjYuMSAxOS45IDMyLjJsMTAwIDUwYzEwLjEgNS4xIDIyLjEgNS4xIDMyLjIgMGwxMDMuOS01MiAxMDMuOSA1MmMxMC4xIDUuMSAyMi4xIDUuMSAzMi4yIDBsMTAwLTUwYzEyLjItNi4xIDE5LjktMTguNiAxOS45LTMyLjJWMjgzLjljMC0xNS05LjMtMjguNC0yMy40LTMzLjd6TTM1OCAyMTQuOGwtODUgMzEuOXYtNjguMmw4NS0zN3Y3My4zek0xNTQgMTA0LjFsMTAyLTM4LjIgMTAyIDM4LjJ2LjZsLTEwMiA0MS40LTEwMi00MS40di0uNnptODQgMjkxLjFsLTg1IDQyLjV2LTc5LjFsODUtMzguOHY3NS40em0wLTExMmwtMTAyIDQxLjQtMTAyLTQxLjR2LS42bDEwMi0zOC4yIDEwMiAzOC4ydi42em0yNDAgMTEybC04NSA0Mi41di03OS4xbDg1LTM4Ljh2NzUuNHptMC0xMTJsLTEwMiA0MS40LTEwMi00MS40di0uNmwxMDItMzguMiAxMDIgMzguMnYuNnoiPjwvcGF0aD48L3N2Zz4K)](https://docs.rs/mufmt/)

> [!WARNING]
> μfmt is **very unstable**
> 
> The public API is undecided, and the error implementation will probably be refactored.
> Moreover, the template implementation may change without notice.
> It is not recommended to use this crate for anything serious until (at the very least) an initial `0.1.0` release.
>
> On the other hand, a lot of the work is already done and the implementation is quite robust.
> Feel free to try this out, and you are welcome to open an issue with any ideas, recommendations, or problems you have while using this crate.

# μfmt
μfmt (`mufmt`) is a minimal and extensible runtime formatting library.

μfmt allows arbitrary types to define a formatting syntax and compiled template format.
μfmt also provides a number of built-in formats, backed by data stored in collection types like `HashMap` or `Vec`.

Please read the [API docs](https://docs.rs/mufmt/) for more detail.

## In progress
- Improve error messages to include detail about where the error occurred within the template.
- Allow compiling a template from an `io::Write`.
- Add a `json` feature, and decide on an `Ast` which can query a `serde_json::Value`.
- Implement an `Ast` for function call chains (like `{ a().b().c() }`; or maybe using s-expressions?).
