//! Type checking for a small λP fragment.
//!
//! Because types and terms share syntax, "type checking" works on the same
//! `Term` data: we produce a term that represents the type. Type equality
//! is checked up to β-normalization (definitional equality) — this is the
//! key feature that lets `(λA:Type. A) Int` be the same type as `Int`.
//!
//! We allow "dependent if": the two branches may have different types,
//! producing a return type of `if c then T₁ else T₂`. When `c` later
//! normalizes to a literal, the type also normalizes. This is what lets
//! `λb:Bool. if b then 42 else true` have type
//! `Πb:Bool. if b then Int else Bool` — the punchline of this fragment.

use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::lambdap::ast::{BinOp, Term};

#[derive(Debug, Clone)]
pub enum TypeError {
    UnboundVariable(String),
    NotAType { found: Term },
    NotAFunctionType { found: Term },
    TypeMismatch { expected: Term, found: Term },
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeError::UnboundVariable(x) => write!(f, "unbound variable: {x}"),
            TypeError::NotAType { found } => {
                write!(f, "expected a Type, found term of type {found}")
            }
            TypeError::NotAFunctionType { found } => {
                write!(f, "expected a function (Π-type), found {found}")
            }
            TypeError::TypeMismatch { expected, found } => {
                write!(f, "type mismatch: expected {expected}, found {found}")
            }
        }
    }
}

pub type Ctx = HashMap<String, Term>;

// ===== Free vars and substitution =====

pub fn free_vars(t: &Term) -> HashSet<String> {
    let mut acc = HashSet::new();
    fn rec(t: &Term, acc: &mut HashSet<String>) {
        match t {
            Term::Var(x) => {
                acc.insert(x.clone());
            }
            Term::Universe | Term::Bool | Term::Int | Term::BoolLit(_) | Term::IntLit(_) => {}
            Term::Pi(x, a, b) | Term::Lambda(x, a, b) => {
                rec(a, acc);
                let mut inner = HashSet::new();
                rec(b, &mut inner);
                inner.remove(x);
                acc.extend(inner);
            }
            Term::App(f, a) => {
                rec(f, acc);
                rec(a, acc);
            }
            Term::If(c, t1, t2) => {
                rec(c, acc);
                rec(t1, acc);
                rec(t2, acc);
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

// Capture-avoiding substitution [s / x] t.
pub fn subst(t: Term, x: &str, s: &Term) -> Term {
    match t {
        Term::Var(y) => {
            if y == x {
                s.clone()
            } else {
                Term::Var(y)
            }
        }
        Term::Universe | Term::Bool | Term::Int | Term::BoolLit(_) | Term::IntLit(_) => t,
        Term::App(f, a) => Term::App(Box::new(subst(*f, x, s)), Box::new(subst(*a, x, s))),
        Term::If(c, t1, t2) => Term::If(
            Box::new(subst(*c, x, s)),
            Box::new(subst(*t1, x, s)),
            Box::new(subst(*t2, x, s)),
        ),
        Term::BinOp(op, a, b) => {
            Term::BinOp(op, Box::new(subst(*a, x, s)), Box::new(subst(*b, x, s)))
        }
        Term::Pi(y, a, b) => subst_binder(y, *a, *b, x, s, Term::pi),
        Term::Lambda(y, a, body) => subst_binder(y, *a, *body, x, s, Term::lambda),
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

fn subst_binder(
    y: String,
    a: Term,
    b: Term,
    x: &str,
    s: &Term,
    ctor: fn(String, Term, Term) -> Term,
) -> Term {
    // First substitute in the annotation (annotations are in the OUTER scope).
    let a_new = subst(a, x, s);
    if y == x {
        ctor(y, a_new, b)
    } else {
        let fv_s = free_vars(s);
        if fv_s.contains(&y) {
            let mut avoid = fv_s;
            avoid.extend(free_vars(&b));
            avoid.insert(x.to_string());
            let new_y = fresh_name(&y, &avoid);
            let renamed = subst(b, &y, &Term::Var(new_y.clone()));
            ctor(new_y, a_new, subst(renamed, x, s))
        } else {
            ctor(y, a_new, subst(b, x, s))
        }
    }
}

// ===== Normalization (β-reduction to normal form, including under binders) =====
//
// Used to decide definitional equality of types. Since our system is
// inconsistent (Type : Type), some terms will not normalize. We bound
// the work with a step limit to avoid infinite recursion on pathological
// inputs.

const NORMALIZE_BUDGET: usize = 5_000;

pub fn normalize(t: &Term) -> Term {
    let mut budget = NORMALIZE_BUDGET;
    normalize_bounded(t.clone(), &mut budget)
}

fn normalize_bounded(t: Term, budget: &mut usize) -> Term {
    if *budget == 0 {
        return t;
    }
    *budget -= 1;
    match t {
        Term::Var(_)
        | Term::Universe
        | Term::Bool
        | Term::Int
        | Term::BoolLit(_)
        | Term::IntLit(_) => t,
        Term::Pi(x, a, b) => Term::pi(
            x,
            normalize_bounded(*a, budget),
            normalize_bounded(*b, budget),
        ),
        Term::Lambda(x, a, body) => Term::lambda(
            x,
            normalize_bounded(*a, budget),
            normalize_bounded(*body, budget),
        ),
        Term::App(f, a) => {
            let f_n = normalize_bounded(*f, budget);
            let a_n = normalize_bounded(*a, budget);
            if let Term::Lambda(x, _, body) = f_n {
                let substituted = subst(*body, &x, &a_n);
                normalize_bounded(substituted, budget)
            } else {
                Term::app(f_n, a_n)
            }
        }
        Term::If(c, t1, t2) => {
            let c_n = normalize_bounded(*c, budget);
            match c_n {
                Term::BoolLit(true) => normalize_bounded(*t1, budget),
                Term::BoolLit(false) => normalize_bounded(*t2, budget),
                other => Term::if_then_else(
                    other,
                    normalize_bounded(*t1, budget),
                    normalize_bounded(*t2, budget),
                ),
            }
        }
        Term::BinOp(op, a, b) => {
            let a_n = normalize_bounded(*a, budget);
            let b_n = normalize_bounded(*b, budget);
            match (&a_n, &b_n) {
                (Term::IntLit(x), Term::IntLit(y)) => match op {
                    BinOp::Add => Term::IntLit(x.wrapping_add(*y)),
                    BinOp::Sub => Term::IntLit(x.wrapping_sub(*y)),
                    BinOp::Mul => Term::IntLit(x.wrapping_mul(*y)),
                    BinOp::Eq => Term::BoolLit(x == y),
                    BinOp::Lt => Term::BoolLit(x < y),
                },
                _ => Term::binop(op, a_n, b_n),
            }
        }
        Term::Let(x, e1, e2) => {
            let e1_n = normalize_bounded(*e1, budget);
            normalize_bounded(subst(*e2, &x, &e1_n), budget)
        }
    }
}

// Alpha-equivalence on already-normalized terms.
fn alpha_eq(a: &Term, b: &Term) -> bool {
    match (a, b) {
        (Term::Var(x), Term::Var(y)) => x == y,
        (Term::Universe, Term::Universe) | (Term::Bool, Term::Bool) | (Term::Int, Term::Int) => {
            true
        }
        (Term::BoolLit(x), Term::BoolLit(y)) => x == y,
        (Term::IntLit(x), Term::IntLit(y)) => x == y,
        (Term::App(f1, a1), Term::App(f2, a2)) => alpha_eq(f1, f2) && alpha_eq(a1, a2),
        (Term::BinOp(o1, a1, b1), Term::BinOp(o2, a2, b2)) => {
            o1 == o2 && alpha_eq(a1, a2) && alpha_eq(b1, b2)
        }
        (Term::If(c1, t1, e1), Term::If(c2, t2, e2)) => {
            alpha_eq(c1, c2) && alpha_eq(t1, t2) && alpha_eq(e1, e2)
        }
        (Term::Pi(x, a1, b1), Term::Pi(y, a2, b2))
        | (Term::Lambda(x, a1, b1), Term::Lambda(y, a2, b2)) => {
            if !alpha_eq(a1, a2) {
                return false;
            }
            // Rename y to x in b2, then compare.
            let b2_renamed = subst((**b2).clone(), y, &Term::Var(x.clone()));
            alpha_eq(b1, &b2_renamed)
        }
        (Term::Let(x, e11, e12), Term::Let(y, e21, e22)) => {
            if !alpha_eq(e11, e21) {
                return false;
            }
            let e22_renamed = subst((**e22).clone(), y, &Term::Var(x.clone()));
            alpha_eq(e12, &e22_renamed)
        }
        _ => false,
    }
}

pub fn term_eq(a: &Term, b: &Term) -> bool {
    alpha_eq(&normalize(a), &normalize(b))
}

// ===== Type checker =====

pub fn type_of(t: &Term, ctx: &Ctx) -> Result<Term, TypeError> {
    match t {
        Term::Var(x) => ctx
            .get(x)
            .cloned()
            .ok_or_else(|| TypeError::UnboundVariable(x.clone())),

        Term::Universe => Ok(Term::Universe), // Type : Type
        Term::Bool | Term::Int => Ok(Term::Universe),
        Term::BoolLit(_) => Ok(Term::Bool),
        Term::IntLit(_) => Ok(Term::Int),

        Term::Pi(x, a, b) => {
            check_is_type(a, ctx)?;
            let mut ctx2 = ctx.clone();
            ctx2.insert(x.clone(), (**a).clone());
            check_is_type(b, &ctx2)?;
            Ok(Term::Universe)
        }

        Term::Lambda(x, a, body) => {
            check_is_type(a, ctx)?;
            let mut ctx2 = ctx.clone();
            ctx2.insert(x.clone(), (**a).clone());
            let body_ty = type_of(body, &ctx2)?;
            Ok(Term::pi(x.clone(), (**a).clone(), body_ty))
        }

        Term::App(f, a) => {
            let f_ty = normalize(&type_of(f, ctx)?);
            match f_ty {
                Term::Pi(x, param_ty, ret_ty) => {
                    let arg_ty = type_of(a, ctx)?;
                    if !term_eq(&arg_ty, &param_ty) {
                        return Err(TypeError::TypeMismatch {
                            expected: *param_ty,
                            found: arg_ty,
                        });
                    }
                    Ok(subst(*ret_ty, &x, a))
                }
                other => Err(TypeError::NotAFunctionType { found: other }),
            }
        }

        Term::If(c, t1, t2) => {
            let c_ty = type_of(c, ctx)?;
            if !term_eq(&c_ty, &Term::Bool) {
                return Err(TypeError::TypeMismatch {
                    expected: Term::Bool,
                    found: c_ty,
                });
            }
            let t1_ty = type_of(t1, ctx)?;
            let t2_ty = type_of(t2, ctx)?;
            if term_eq(&t1_ty, &t2_ty) {
                Ok(t1_ty)
            } else {
                // Dependent if: the result type itself branches on c.
                Ok(Term::if_then_else((**c).clone(), t1_ty, t2_ty))
            }
        }

        Term::BinOp(op, a, b) => {
            let ta = type_of(a, ctx)?;
            let tb = type_of(b, ctx)?;
            if !term_eq(&ta, &Term::Int) {
                return Err(TypeError::TypeMismatch {
                    expected: Term::Int,
                    found: ta,
                });
            }
            if !term_eq(&tb, &Term::Int) {
                return Err(TypeError::TypeMismatch {
                    expected: Term::Int,
                    found: tb,
                });
            }
            Ok(match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul => Term::Int,
                BinOp::Eq | BinOp::Lt => Term::Bool,
            })
        }

        Term::Let(x, e1, e2) => {
            let e1_ty = type_of(e1, ctx)?;
            let mut ctx2 = ctx.clone();
            ctx2.insert(x.clone(), e1_ty);
            type_of(e2, &ctx2)
        }
    }
}

fn check_is_type(t: &Term, ctx: &Ctx) -> Result<(), TypeError> {
    let ty = type_of(t, ctx)?;
    if term_eq(&ty, &Term::Universe) {
        Ok(())
    } else {
        Err(TypeError::NotAType { found: ty })
    }
}

pub fn type_of_top(t: &Term) -> Result<Term, TypeError> {
    let ty = type_of(t, &Ctx::new())?;
    Ok(normalize(&ty))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lambdap::parser::parse;

    fn typeof_str(input: &str) -> Result<Term, TypeError> {
        let t = parse(input).expect("parse");
        type_of_top(&t)
    }

    #[test]
    fn type_of_int_literal_is_int() {
        let ty = typeof_str("42").unwrap();
        assert!(term_eq(&ty, &Term::Int));
    }

    #[test]
    fn type_of_bool_is_universe() {
        let ty = typeof_str("Bool").unwrap();
        assert!(term_eq(&ty, &Term::Universe));
    }

    #[test]
    fn type_of_universe_is_universe() {
        // Type : Type — pedagogically inconsistent.
        let ty = typeof_str("Type").unwrap();
        assert!(term_eq(&ty, &Term::Universe));
    }

    #[test]
    fn polymorphic_identity_has_pi_type() {
        // λA: Type. λx: A. x   :   ΠA: Type. A -> A
        let ty = typeof_str("\\A: Type. \\x: A. x").unwrap();
        // Expected: Pi A: Type. Pi _: A. A    (the inner Pi prints as arrow)
        let expected = Term::pi(
            "A",
            Term::Universe,
            Term::pi("x", Term::var("A"), Term::var("A")),
        );
        assert!(term_eq(&ty, &expected), "got {ty}, expected {expected}");
    }

    #[test]
    fn polymorphic_id_specializes_at_int() {
        // (λA: Type. λx: A. x) Int 5  :  Int
        let ty = typeof_str("(\\A: Type. \\x: A. x) Int 5").unwrap();
        assert!(term_eq(&ty, &Term::Int));
    }

    #[test]
    fn polymorphic_id_specializes_at_bool() {
        let ty = typeof_str("(\\A: Type. \\x: A. x) Bool true").unwrap();
        assert!(term_eq(&ty, &Term::Bool));
    }

    #[test]
    fn dependent_function_has_dependent_type() {
        // λb: Bool. if b then 42 else true
        // The two branches have different types (Int and Bool), so the
        // function's return type is `if b then Int else Bool`. Whole type:
        // Π b: Bool. (if b then Int else Bool).
        let ty = typeof_str("\\b: Bool. if b then 42 else true").unwrap();
        let expected = Term::pi(
            "b",
            Term::Bool,
            Term::if_then_else(Term::var("b"), Term::Int, Term::Bool),
        );
        assert!(term_eq(&ty, &expected), "got {ty}");
    }

    #[test]
    fn dependent_application_at_true_normalizes_to_int() {
        // (λb: Bool. if b then 42 else true) true  :  Int
        // because  `if true then Int else Bool`  normalizes to  Int.
        let ty = typeof_str("(\\b: Bool. if b then 42 else true) true").unwrap();
        assert!(term_eq(&ty, &Term::Int), "got {ty}");
    }

    #[test]
    fn dependent_application_at_false_normalizes_to_bool() {
        let ty = typeof_str("(\\b: Bool. if b then 42 else true) false").unwrap();
        assert!(term_eq(&ty, &Term::Bool), "got {ty}");
    }

    #[test]
    fn type_level_beta_works() {
        // (λA: Type. A) Int   ≡   Int
        let lhs = parse("(\\A: Type. A) Int").unwrap();
        assert!(term_eq(&lhs, &Term::Int));
    }

    #[test]
    fn pi_type_well_formed() {
        // Pi A: Type. A -> A   :   Type
        let ty = typeof_str("Pi A: Type. A -> A").unwrap();
        assert!(term_eq(&ty, &Term::Universe));
    }

    #[test]
    fn cannot_apply_int_as_function() {
        assert!(typeof_str("5 3").is_err());
    }

    #[test]
    fn type_mismatch_in_application() {
        // (\x: Int. x + 1) true   — Bool where Int expected
        assert!(typeof_str("(\\x: Int. x + 1) true").is_err());
    }

    #[test]
    fn unbound_variable_is_error() {
        assert!(typeof_str("x").is_err());
    }
}
