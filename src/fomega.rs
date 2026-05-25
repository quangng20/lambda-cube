//! System Fω — λω, adds the type-operator axis to System F.
//!
//! Types now have *kinds*: `*` (proper types like Int), `* -> *` (one-arg
//! type operators like List), `* -> * -> *` (Pair), etc. Type operators
//! can be applied at the type level and reduce via type-level β-reduction
//! during type checking.
//!
//! This is the axis Rust's type system does NOT climb: Rust has no
//! higher-kinded types. You cannot abstract over `F: * -> *` and write
//! `Functor F` the way Haskell does.

pub mod ast;
pub mod eval;
pub mod parser;
pub mod typeck;

mod repl;
pub use repl::run as repl;
