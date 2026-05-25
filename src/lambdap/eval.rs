//! CBV small-step evaluation. Reuses the same machinery as type-checking's
//! normalize, but stops at weak-head form (it doesn't reduce under binders).

use crate::lambdap::ast::{BinOp, Term};
use crate::lambdap::typeck::subst;

fn is_value(t: &Term) -> bool {
    matches!(
        t,
        Term::IntLit(_)
            | Term::BoolLit(_)
            | Term::Lambda(_, _, _)
            | Term::Universe
            | Term::Bool
            | Term::Int
            | Term::Pi(_, _, _)
    )
}

pub fn step(t: &Term) -> Option<Term> {
    match t {
        Term::Var(_)
        | Term::Universe
        | Term::Bool
        | Term::Int
        | Term::BoolLit(_)
        | Term::IntLit(_)
        | Term::Lambda(_, _, _)
        | Term::Pi(_, _, _) => None,

        Term::App(f, a) => {
            if !is_value(f) {
                return step(f).map(|f_new| Term::App(Box::new(f_new), a.clone()));
            }
            if !is_value(a) {
                return step(a).map(|a_new| Term::App(f.clone(), Box::new(a_new)));
            }
            if let Term::Lambda(x, _, body) = f.as_ref() {
                Some(subst(body.as_ref().clone(), x, a))
            } else {
                None
            }
        }

        Term::If(c, t1, t2) => {
            if !is_value(c) {
                return step(c).map(|c_new| Term::If(Box::new(c_new), t1.clone(), t2.clone()));
            }
            match c.as_ref() {
                Term::BoolLit(true) => Some(t1.as_ref().clone()),
                Term::BoolLit(false) => Some(t2.as_ref().clone()),
                _ => None,
            }
        }

        Term::BinOp(op, a, b) => {
            if !is_value(a) {
                return step(a).map(|a_new| Term::BinOp(*op, Box::new(a_new), b.clone()));
            }
            if !is_value(b) {
                return step(b).map(|b_new| Term::BinOp(*op, a.clone(), Box::new(b_new)));
            }
            match (a.as_ref(), b.as_ref()) {
                (Term::IntLit(x), Term::IntLit(y)) => Some(match op {
                    BinOp::Add => Term::IntLit(x.wrapping_add(*y)),
                    BinOp::Sub => Term::IntLit(x.wrapping_sub(*y)),
                    BinOp::Mul => Term::IntLit(x.wrapping_mul(*y)),
                    BinOp::Eq => Term::BoolLit(x == y),
                    BinOp::Lt => Term::BoolLit(x < y),
                }),
                _ => None,
            }
        }

        Term::Let(x, e1, e2) => {
            if !is_value(e1) {
                return step(e1).map(|e1_new| Term::Let(x.clone(), Box::new(e1_new), e2.clone()));
            }
            Some(subst(e2.as_ref().clone(), x, e1))
        }
    }
}

pub struct EvalResult {
    pub term: Term,
    pub steps: usize,
}

pub fn eval(mut t: Term, max_steps: usize) -> EvalResult {
    for i in 0..max_steps {
        match step(&t) {
            Some(next) => t = next,
            None => return EvalResult { term: t, steps: i },
        }
    }
    EvalResult {
        term: t,
        steps: max_steps,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lambdap::parser::parse;

    fn run(input: &str) -> Term {
        let t = parse(input).expect("parse");
        eval(t, 10_000).term
    }

    #[test]
    fn polymorphic_id_at_int_evaluates() {
        assert_eq!(run("(\\A: Type. \\x: A. x) Int 42"), Term::IntLit(42));
    }

    #[test]
    fn polymorphic_id_at_bool_evaluates() {
        assert_eq!(run("(\\A: Type. \\x: A. x) Bool true"), Term::BoolLit(true));
    }

    #[test]
    fn dependent_function_at_true_returns_int() {
        // λb. if b then 42 else true  applied to  true  →  42
        assert_eq!(
            run("(\\b: Bool. if b then 42 else true) true"),
            Term::IntLit(42)
        );
    }

    #[test]
    fn dependent_function_at_false_returns_bool() {
        assert_eq!(
            run("(\\b: Bool. if b then 42 else true) false"),
            Term::BoolLit(true)
        );
    }
}
