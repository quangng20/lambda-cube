//! A small λP fragment — the dependent-types corner of the lambda cube.
//!
//! Types and terms share one syntactic category and one type checker.
//! Π-types let return types depend on argument values. Definitional
//! equality is decided by β-normalization of types.
//!
//! Real-world dependent type systems (Coq, Agda, Lean, Idris, F\*) are
//! orders of magnitude larger and address things this fragment ignores:
//! a universe hierarchy (Type ₀ : Type ₁ : … to avoid Girard's paradox),
//! inductive types, pattern matching, totality checking, universe
//! polymorphism, induction principles, etc. This is a teaching fragment
//! whose job is to show what changes when types can depend on terms.

pub mod ast;
pub mod eval;
pub mod parser;
pub mod typeck;

mod repl;
pub use repl::run as repl;
