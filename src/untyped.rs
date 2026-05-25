//! Untyped lambda calculus — the bottom of the cube (not actually on the cube;
//! it's the calculus the cube is built on top of).
//!
//! Three AST nodes (Var, Abs, App), capture-avoiding substitution,
//! normal-order beta-reduction to normal form.

pub mod ast;
pub mod eval;
pub mod parser;

mod repl;
pub use repl::run as repl;
