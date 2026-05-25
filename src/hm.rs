//! Hindley-Milner — the type system at the core of ML, OCaml, Haskell (rank-1),
//! and Elm. Lives at the rank-1 restriction of System F where ∀-quantifiers
//! never nest inside other types — this is what makes type inference
//! decidable and produces "principal" types.
//!
//! No type annotations required. Polymorphism appears at `let` bindings via
//! generalization; each use site gets a fresh instantiation of the scheme.

pub mod ast;
pub mod eval;
pub mod infer;
pub mod parser;

mod repl;
pub use repl::run as repl;
