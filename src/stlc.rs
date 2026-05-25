//! Simply Typed Lambda Calculus — λ→, the corner of the lambda cube.
//!
//! Adds to untyped LC: base types (Bool, Int), function types (T -> U),
//! type-annotated lambdas (\x:T. body), a bidirectional type checker, and
//! some primitive ops (+ - * == <) plus if/let to make typing useful.
//!
//! Two key properties of STLC:
//!   1. Strong normalization — every well-typed term terminates.
//!   2. No general recursion — the Y combinator is not typeable.

pub mod ast;
pub mod eval;
pub mod parser;
pub mod typeck;

mod repl;
pub use repl::run as repl;
