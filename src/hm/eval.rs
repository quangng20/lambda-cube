//! Call-by-value small-step evaluator. Types are erased at runtime, so this
//! looks much like the untyped evaluator — except we have to handle `LetRec`
//! via the standard `fix` reduction rule.

use std::collections::HashSet;

use crate::hm::ast::{BinOp, Term};

fn is_value(t: &Term) -> bool {
    matches!(t, Term::IntLit(_) | Term::BoolLit(_) | Term::Abs(_, _))
}

fn free_vars(t: &Term) -> HashSet<String> {
    let mut acc = HashSet::new();
    fn rec(t: &Term, acc: &mut HashSet<String>) {
        match t {
            Term::Var(x) => {
                acc.insert(x.clone());
            }
            Term::Abs(x, body) => {
                let mut inner = HashSet::new();
                rec(body, &mut inner);
                inner.remove(x);
                acc.extend(inner);
            }
            Term::App(f, a) => {
                rec(f, acc);
                rec(a, acc);
            }
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
            Term::LetRec(x, e1, e2) => {
                let mut inner1 = HashSet::new();
                rec(e1, &mut inner1);
                inner1.remove(x);
                acc.extend(inner1);
                let mut inner2 = HashSet::new();
                rec(e2, &mut inner2);
                inner2.remove(x);
                acc.extend(inner2);
            }
            Term::Fix(inner) => rec(inner, acc),
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
        let candidate = format!("{stem}{i}");
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
        Term::Fix(inner) => Term::Fix(Box::new(subst(*inner, x, s))),
        Term::Abs(y, body) => subst_under_binder(y, body, x, s, Term::Abs),
        Term::Let(y, e1, e2) => {
            let e1_new = subst(*e1, x, s);
            if y == x {
                Term::Let(y, Box::new(e1_new), e2)
            } else {
                let (new_y, new_body) = rename_if_capture(y, *e2, x, s);
                Term::Let(new_y, Box::new(e1_new), Box::new(new_body))
            }
        }
        Term::LetRec(y, e1, e2) => {
            if y == x {
                // Both e1 and e2 are under the binder for y == x: do not substitute.
                Term::LetRec(y, e1, e2)
            } else {
                // Substitute in BOTH e1 and e2 (both have y in scope).
                let fv_s = free_vars(s);
                let mut avoid = fv_s.clone();
                avoid.extend(free_vars(&e1));
                avoid.extend(free_vars(&e2));
                avoid.insert(x.to_string());
                let (new_y, e1_renamed, e2_renamed) = if fv_s.contains(&y) {
                    let new_y = fresh_name(&y, &avoid);
                    let e1r = subst(*e1, &y, &Term::Var(new_y.clone()));
                    let e2r = subst(*e2, &y, &Term::Var(new_y.clone()));
                    (new_y, e1r, e2r)
                } else {
                    (y, *e1, *e2)
                };
                Term::LetRec(
                    new_y,
                    Box::new(subst(e1_renamed, x, s)),
                    Box::new(subst(e2_renamed, x, s)),
                )
            }
        }
    }
}

fn subst_under_binder(
    y: String,
    body: Box<Term>,
    x: &str,
    s: &Term,
    ctor: fn(String, Box<Term>) -> Term,
) -> Term {
    if y == x {
        ctor(y, body)
    } else {
        let (new_y, new_body) = rename_if_capture(y, *body, x, s);
        ctor(new_y, Box::new(new_body))
    }
}

fn rename_if_capture(y: String, body: Term, x: &str, s: &Term) -> (String, Term) {
    let fv_s = free_vars(s);
    if fv_s.contains(&y) {
        let mut avoid = fv_s;
        avoid.extend(free_vars(&body));
        avoid.insert(x.to_string());
        let new_y = fresh_name(&y, &avoid);
        let renamed = subst(body, &y, &Term::Var(new_y.clone()));
        (new_y, subst(renamed, x, s))
    } else {
        (y, subst(body, x, s))
    }
}

pub fn step(t: &Term) -> Option<Term> {
    match t {
        Term::Var(_) | Term::IntLit(_) | Term::BoolLit(_) | Term::Abs(_, _) => None,

        Term::App(f, a) => {
            if !is_value(f) {
                return step(f).map(|f_new| Term::App(Box::new(f_new), a.clone()));
            }
            if !is_value(a) {
                return step(a).map(|a_new| Term::App(f.clone(), Box::new(a_new)));
            }
            if let Term::Abs(x, body) = f.as_ref() {
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

        // let rec f = e1 in e2  ⟶  let f = fix (λf. e1) in e2
        // We desugar at step time rather than at parse time so the type
        // checker can apply the proper recursive typing rule.
        Term::LetRec(x, e1, e2) => Some(Term::Let(
            x.clone(),
            Box::new(Term::Fix(Box::new(Term::Abs(x.clone(), e1.clone())))),
            e2.clone(),
        )),

        // fix (λx. body)  ⟶  body[x := fix (λx. body)]
        // The result is a lambda value iff body is itself a lambda — which is
        // the usual shape for recursive function definitions.
        Term::Fix(inner) => {
            if !is_value(inner) {
                return step(inner).map(|inner_new| Term::Fix(Box::new(inner_new)));
            }
            match inner.as_ref() {
                Term::Abs(x, body) => {
                    let self_ref = Term::Fix(Box::new(Term::Abs(x.clone(), body.clone())));
                    Some(subst(body.as_ref().clone(), x, &self_ref))
                }
                _ => None,
            }
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
    use crate::hm::parser::parse;

    fn run(input: &str) -> Term {
        let t = parse(input).expect("parse");
        eval(t, 100_000).term
    }

    #[test]
    fn arithmetic() {
        assert_eq!(run("1 + 2 * 3"), Term::IntLit(7));
    }

    #[test]
    fn identity_application() {
        assert_eq!(run("(\\x. x) 42"), Term::IntLit(42));
    }

    #[test]
    fn let_binding() {
        assert_eq!(run("let x = 5 in x + x"), Term::IntLit(10));
    }

    #[test]
    fn let_rec_factorial() {
        assert_eq!(
            run("let rec f = \\n. if n == 0 then 1 else n * f (n - 1) in f 5"),
            Term::IntLit(120)
        );
    }

    #[test]
    fn let_rec_fibonacci() {
        assert_eq!(
            run("let rec fib = \\n. if n < 2 then n else fib (n - 1) + fib (n - 2) in fib 10"),
            Term::IntLit(55)
        );
    }

    #[test]
    fn mutual_use_of_polymorphic_id_at_two_types() {
        // let id = \x. x in if id true then id 7 else 0
        assert_eq!(
            run("let id = \\x. x in if id true then id 7 else 0"),
            Term::IntLit(7)
        );
    }
}
