//! System F — λ2, the polymorphism corner of the lambda cube.
//!
//! Adds to STLC:
//!   - type variables (T, U) and ∀-types (`forall T. τ`)
//!   - type abstraction `ΛT. e`  (also written `/\T. e`)
//!   - type application `e [τ]`
//!
//! All System F terms are still strongly normalizing — adding polymorphism
//! does not break termination (Girard, 1972). The Y combinator remains
//! unwritable; you cannot encode general recursion in pure System F.

pub mod ast;
pub mod eval;
pub mod parser;
pub mod typeck;

mod repl;
pub use repl::run as repl;
