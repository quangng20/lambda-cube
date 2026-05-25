use std::collections::HashSet;

use crate::systemf::ast::{BinOp, Term};
use crate::systemf::typeck::ty_subst_in_term;

fn is_value(t: &Term) -> bool {
    matches!(
        t,
        Term::IntLit(_) | Term::BoolLit(_) | Term::Abs(_, _, _) | Term::TyAbs(_, _)
    )
}

fn free_vars(t: &Term) -> HashSet<String> {
    let mut acc = HashSet::new();
    fn rec(t: &Term, acc: &mut HashSet<String>) {
        match t {
            Term::Var(x) => {
                acc.insert(x.clone());
            }
            Term::Abs(x, _, body) => {
                let mut inner = HashSet::new();
                rec(body, &mut inner);
                inner.remove(x);
                acc.extend(inner);
            }
            Term::App(f, a) => {
                rec(f, acc);
                rec(a, acc);
            }
            Term::TyAbs(_, body) => rec(body, acc),
            Term::TyApp(f, _) => rec(f, acc),
            Term::If(c, t, e) => {
                rec(c, acc);
                rec(t, acc);
                rec(e, acc);
            }
            Term::BinOp(_, a, b) => {
                rec(a, acc);
                rec(b, acc);
            }
            Term::Let(x, e1, e2) => {
                rec(e1, acc);
                let mut inner = HashSet::new();
                rec(e2, &mut inner);
                inner.remove(x);
                acc.extend(inner);
            }
            Term::IntLit(_) | Term::BoolLit(_) => {}
        }
    }
    rec(t, &mut acc);
    acc
}

fn fresh_name(base: &str, avoid: &HashSet<String>) -> String {
    if !avoid.contains(base) {
        return base.to_string();
    }
    let stem: String = base.chars().take_while(|c| !c.is_ascii_digit()).collect();
    let stem = if stem.is_empty() { base } else { stem.as_str() };
    for i in 1u32.. {
        let candidate = format!("{}{}", stem, i);
        if !avoid.contains(&candidate) {
            return candidate;
        }
    }
    unreachable!()
}

pub fn subst(t: Term, x: &str, s: &Term) -> Term {
    match t {
        Term::Var(y) => {
            if y == x {
                s.clone()
            } else {
                Term::Var(y)
            }
        }
        Term::IntLit(_) | Term::BoolLit(_) => t,
        Term::App(f, a) => Term::App(Box::new(subst(*f, x, s)), Box::new(subst(*a, x, s))),
        Term::If(c, t1, t2) => Term::If(
            Box::new(subst(*c, x, s)),
            Box::new(subst(*t1, x, s)),
            Box::new(subst(*t2, x, s)),
        ),
        Term::BinOp(op, a, b) => {
            Term::BinOp(op, Box::new(subst(*a, x, s)), Box::new(subst(*b, x, s)))
        }
        Term::Abs(y, ty, body) => {
            if y == x {
                Term::Abs(y, ty, body)
            } else {
                let fv_s = free_vars(s);
                if fv_s.contains(&y) {
                    let mut avoid = fv_s;
                    avoid.extend(free_vars(&body));
                    avoid.insert(x.to_string());
                    let new_y = fresh_name(&y, &avoid);
                    let renamed = subst(*body, &y, &Term::Var(new_y.clone()));
                    Term::Abs(new_y, ty, Box::new(subst(renamed, x, s)))
                } else {
                    Term::Abs(y, ty, Box::new(subst(*body, x, s)))
                }
            }
        }
        Term::TyAbs(y, body) => Term::TyAbs(y, Box::new(subst(*body, x, s))),
        Term::TyApp(f, ty) => Term::TyApp(Box::new(subst(*f, x, s)), ty),
        Term::Let(y, e1, e2) => {
            let e1_new = subst(*e1, x, s);
            if y == x {
                Term::Let(y, Box::new(e1_new), e2)
            } else {
                let fv_s = free_vars(s);
                if fv_s.contains(&y) {
                    let mut avoid = fv_s;
                    avoid.extend(free_vars(&e2));
                    avoid.insert(x.to_string());
                    let new_y = fresh_name(&y, &avoid);
                    let renamed = subst(*e2, &y, &Term::Var(new_y.clone()));
                    Term::Let(new_y, Box::new(e1_new), Box::new(subst(renamed, x, s)))
                } else {
                    Term::Let(y, Box::new(e1_new), Box::new(subst(*e2, x, s)))
                }
            }
        }
    }
}

pub fn step(t: &Term) -> Option<Term> {
    match t {
        Term::Var(_)
        | Term::IntLit(_)
        | Term::BoolLit(_)
        | Term::Abs(_, _, _)
        | Term::TyAbs(_, _) => None,

        Term::App(f, a) => {
            if !is_value(f) {
                return step(f).map(|f_new| Term::App(Box::new(f_new), a.clone()));
            }
            if !is_value(a) {
                return step(a).map(|a_new| Term::App(f.clone(), Box::new(a_new)));
            }
            if let Term::Abs(x, _, body) = f.as_ref() {
                Some(subst(body.as_ref().clone(), x, a))
            } else {
                None
            }
        }

        Term::TyApp(f, ty) => {
            if !is_value(f) {
                return step(f).map(|f_new| Term::TyApp(Box::new(f_new), ty.clone()));
            }
            if let Term::TyAbs(x, body) = f.as_ref() {
                Some(ty_subst_in_term(body, x, ty))
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
    use crate::systemf::parser::parse;

    fn run(input: &str) -> Term {
        let t = parse(input).expect("parse");
        eval(t, 10_000).term
    }

    #[test]
    fn polymorphic_identity_at_int() {
        assert_eq!(run("(/\\T. \\x:T. x) [Int] 42"), Term::IntLit(42));
    }

    #[test]
    fn polymorphic_identity_at_bool() {
        assert_eq!(run("(/\\T. \\x:T. x) [Bool] true"), Term::BoolLit(true));
    }

    #[test]
    fn k_combinator_evaluates() {
        // K [Int] [Bool] 5 true = 5
        assert_eq!(
            run("(/\\T. /\\U. \\x:T. \\y:U. x) [Int] [Bool] 5 true"),
            Term::IntLit(5)
        );
    }

    #[test]
    fn polymorphic_identity_used_at_two_types_in_same_expression() {
        // let id = /\T. \x:T. x in (id [Int] 7) + (id [Int] 5)  =  12
        // Note: we have to type-apply each use site separately. True polymorphism!
        assert_eq!(
            run("let id = /\\T. \\x:T. x in id [Int] 7 + id [Int] 5"),
            Term::IntLit(12)
        );
    }
}
