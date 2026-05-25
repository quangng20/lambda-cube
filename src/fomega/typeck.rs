//! Type and kind checking for System Fω.
//!
//! Two judgments: terms are checked against types (as in System F), and types
//! are checked against kinds. Type equality is up to β-normalization of types,
//! because type-level lambdas can compute.

use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::fomega::ast::{BinOp, Kind, Term, Type};

#[derive(Debug, Clone)]
pub enum TypeError {
    UnboundVariable(String),
    UnboundTypeVariable(String),
    TypeMismatch { expected: Type, found: Type },
    KindMismatch { expected: Kind, found: Kind },
    NotAFunction { found: Type },
    NotPolymorphic { found: Type },
    NotATypeOperator { found: Kind },
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeError::UnboundVariable(x) => write!(f, "unbound variable: {x}"),
            TypeError::UnboundTypeVariable(x) => write!(f, "unbound type variable: {x}"),
            TypeError::TypeMismatch { expected, found } => {
                write!(f, "type mismatch: expected {expected}, found {found}")
            }
            TypeError::KindMismatch { expected, found } => {
                write!(f, "kind mismatch: expected {expected}, found {found}")
            }
            TypeError::NotAFunction { found } => {
                write!(f, "expected a function, found value of type {found}")
            }
            TypeError::NotPolymorphic { found } => {
                write!(f, "type application requires a ∀-type, found {found}")
            }
            TypeError::NotATypeOperator { found } => write!(
                f,
                "expected a type operator (kind κ -> κ'), found kind {found}"
            ),
        }
    }
}

#[derive(Default, Clone)]
pub struct Ctx {
    pub values: HashMap<String, Type>,
    pub kinds: HashMap<String, Kind>,
}

// ===== Free type variables =====

pub fn ftv(t: &Type) -> HashSet<String> {
    let mut acc = HashSet::new();
    fn rec(t: &Type, acc: &mut HashSet<String>) {
        match t {
            Type::Bool | Type::Int => {}
            Type::Var(x) => {
                acc.insert(x.clone());
            }
            Type::Arrow(a, b) | Type::App(a, b) => {
                rec(a, acc);
                rec(b, acc);
            }
            Type::ForAll(x, _, body) | Type::Abs(x, _, body) => {
                let mut inner = HashSet::new();
                rec(body, &mut inner);
                inner.remove(x);
                acc.extend(inner);
            }
        }
    }
    rec(t, &mut acc);
    acc
}

fn fresh_type_name(base: &str, avoid: &HashSet<String>) -> String {
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

// ===== Capture-avoiding type substitution =====

pub fn type_subst(t: &Type, x: &str, s: &Type) -> Type {
    match t {
        Type::Bool => Type::Bool,
        Type::Int => Type::Int,
        Type::Var(y) => {
            if y == x {
                s.clone()
            } else {
                Type::Var(y.clone())
            }
        }
        Type::Arrow(a, b) => Type::arrow(type_subst(a, x, s), type_subst(b, x, s)),
        Type::App(a, b) => Type::app(type_subst(a, x, s), type_subst(b, x, s)),
        Type::ForAll(y, k, body) => subst_binder(y, k, body, x, s, Type::forall),
        Type::Abs(y, k, body) => subst_binder(y, k, body, x, s, Type::abs),
    }
}

fn subst_binder(
    y: &str,
    k: &Kind,
    body: &Type,
    x: &str,
    s: &Type,
    ctor: fn(String, Kind, Type) -> Type,
) -> Type {
    if y == x {
        ctor(y.to_string(), k.clone(), body.clone())
    } else {
        let fv_s = ftv(s);
        if fv_s.contains(y) {
            let mut avoid = fv_s;
            avoid.extend(ftv(body));
            avoid.insert(x.to_string());
            let new_y = fresh_type_name(y, &avoid);
            let renamed = type_subst(body, y, &Type::Var(new_y.clone()));
            ctor(new_y, k.clone(), type_subst(&renamed, x, s))
        } else {
            ctor(y.to_string(), k.clone(), type_subst(body, x, s))
        }
    }
}

// ===== β-normalization of types =====
//
// In well-kinded Fω, type-level β-reduction terminates (the type level is
// essentially STLC-with-kind-* in place of base types). So normalizing
// well-kinded types always finishes.

pub fn normalize(t: &Type) -> Type {
    match t {
        Type::Bool | Type::Int | Type::Var(_) => t.clone(),
        Type::Arrow(a, b) => Type::arrow(normalize(a), normalize(b)),
        Type::ForAll(x, k, body) => Type::forall(x.clone(), k.clone(), normalize(body)),
        Type::Abs(x, k, body) => Type::abs(x.clone(), k.clone(), normalize(body)),
        Type::App(f, a) => {
            let f_n = normalize(f);
            let a_n = normalize(a);
            if let Type::Abs(x, _, body) = f_n {
                // β-redex at the type level
                let substituted = type_subst(&body, &x, &a_n);
                normalize(&substituted)
            } else {
                Type::app(f_n, a_n)
            }
        }
    }
}

// Alpha-equivalence on already-normalized types.
fn alpha_eq(a: &Type, b: &Type) -> bool {
    match (a, b) {
        (Type::Bool, Type::Bool) | (Type::Int, Type::Int) => true,
        (Type::Var(x), Type::Var(y)) => x == y,
        (Type::Arrow(a1, b1), Type::Arrow(a2, b2)) | (Type::App(a1, b1), Type::App(a2, b2)) => {
            alpha_eq(a1, a2) && alpha_eq(b1, b2)
        }
        (Type::ForAll(x, k1, body1), Type::ForAll(y, k2, body2))
        | (Type::Abs(x, k1, body1), Type::Abs(y, k2, body2)) => {
            if k1 != k2 {
                return false;
            }
            // Rename y to x in body2, then compare.
            let body2_renamed = type_subst(body2, y, &Type::Var(x.clone()));
            alpha_eq(body1, &body2_renamed)
        }
        _ => false,
    }
}

pub fn type_eq(t1: &Type, t2: &Type) -> bool {
    alpha_eq(&normalize(t1), &normalize(t2))
}

// ===== Kind checking =====

pub fn kind_of(t: &Type, ctx: &Ctx) -> Result<Kind, TypeError> {
    match t {
        Type::Bool | Type::Int => Ok(Kind::Star),
        Type::Var(x) => ctx
            .kinds
            .get(x)
            .cloned()
            .ok_or_else(|| TypeError::UnboundTypeVariable(x.clone())),
        Type::Arrow(a, b) => {
            check_kind(a, &Kind::Star, ctx)?;
            check_kind(b, &Kind::Star, ctx)?;
            Ok(Kind::Star)
        }
        Type::ForAll(x, k, body) => {
            let mut ctx2 = ctx.clone();
            ctx2.kinds.insert(x.clone(), k.clone());
            check_kind(body, &Kind::Star, &ctx2)?;
            Ok(Kind::Star)
        }
        Type::Abs(x, k, body) => {
            let mut ctx2 = ctx.clone();
            ctx2.kinds.insert(x.clone(), k.clone());
            let body_k = kind_of(body, &ctx2)?;
            Ok(Kind::arrow(k.clone(), body_k))
        }
        Type::App(f, a) => {
            let f_k = kind_of(f, ctx)?;
            match f_k {
                Kind::Arrow(param, ret) => {
                    check_kind(a, &param, ctx)?;
                    Ok(*ret)
                }
                other => Err(TypeError::NotATypeOperator { found: other }),
            }
        }
    }
}

fn check_kind(t: &Type, expected: &Kind, ctx: &Ctx) -> Result<(), TypeError> {
    let found = kind_of(t, ctx)?;
    if &found == expected {
        Ok(())
    } else {
        Err(TypeError::KindMismatch {
            expected: expected.clone(),
            found,
        })
    }
}

// ===== Term type checking =====

pub fn ty_subst_in_term(t: &Term, x: &str, s: &Type) -> Term {
    match t {
        Term::Var(_) | Term::IntLit(_) | Term::BoolLit(_) => t.clone(),
        Term::Abs(y, ty, body) => Term::Abs(
            y.clone(),
            type_subst(ty, x, s),
            Box::new(ty_subst_in_term(body, x, s)),
        ),
        Term::App(f, a) => Term::App(
            Box::new(ty_subst_in_term(f, x, s)),
            Box::new(ty_subst_in_term(a, x, s)),
        ),
        Term::TyAbs(y, k, body) => {
            if y == x {
                Term::TyAbs(y.clone(), k.clone(), body.clone())
            } else {
                let fv_s = ftv(s);
                if fv_s.contains(y) {
                    let mut avoid = fv_s;
                    avoid.extend(free_type_vars_in_term(body));
                    avoid.insert(x.to_string());
                    let new_y = fresh_type_name(y, &avoid);
                    let renamed = ty_subst_in_term(body, y, &Type::Var(new_y.clone()));
                    Term::TyAbs(new_y, k.clone(), Box::new(ty_subst_in_term(&renamed, x, s)))
                } else {
                    Term::TyAbs(y.clone(), k.clone(), Box::new(ty_subst_in_term(body, x, s)))
                }
            }
        }
        Term::TyApp(f, ty) => {
            Term::TyApp(Box::new(ty_subst_in_term(f, x, s)), type_subst(ty, x, s))
        }
        Term::If(c, t1, t2) => Term::If(
            Box::new(ty_subst_in_term(c, x, s)),
            Box::new(ty_subst_in_term(t1, x, s)),
            Box::new(ty_subst_in_term(t2, x, s)),
        ),
        Term::BinOp(op, a, b) => Term::BinOp(
            *op,
            Box::new(ty_subst_in_term(a, x, s)),
            Box::new(ty_subst_in_term(b, x, s)),
        ),
        Term::Let(y, e1, e2) => Term::Let(
            y.clone(),
            Box::new(ty_subst_in_term(e1, x, s)),
            Box::new(ty_subst_in_term(e2, x, s)),
        ),
    }
}

fn free_type_vars_in_term(t: &Term) -> HashSet<String> {
    let mut acc = HashSet::new();
    fn rec(t: &Term, acc: &mut HashSet<String>) {
        match t {
            Term::Var(_) | Term::IntLit(_) | Term::BoolLit(_) => {}
            Term::Abs(_, ty, body) => {
                acc.extend(ftv(ty));
                rec(body, acc);
            }
            Term::App(f, a) => {
                rec(f, acc);
                rec(a, acc);
            }
            Term::TyAbs(x, _, body) => {
                let mut inner = HashSet::new();
                rec(body, &mut inner);
                inner.remove(x);
                acc.extend(inner);
            }
            Term::TyApp(f, ty) => {
                rec(f, acc);
                acc.extend(ftv(ty));
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
            Term::Let(_, e1, e2) => {
                rec(e1, acc);
                rec(e2, acc);
            }
        }
    }
    rec(t, &mut acc);
    acc
}

pub fn infer(t: &Term, ctx: &Ctx) -> Result<Type, TypeError> {
    match t {
        Term::Var(x) => ctx
            .values
            .get(x)
            .cloned()
            .ok_or_else(|| TypeError::UnboundVariable(x.clone())),

        Term::IntLit(_) => Ok(Type::Int),
        Term::BoolLit(_) => Ok(Type::Bool),

        Term::Abs(x, ty, body) => {
            // Parameter type annotations must be proper types (kind *).
            check_kind(ty, &Kind::Star, ctx)?;
            let mut ctx2 = ctx.clone();
            ctx2.values.insert(x.clone(), ty.clone());
            let body_ty = infer(body, &ctx2)?;
            Ok(Type::arrow(ty.clone(), body_ty))
        }

        Term::App(f, a) => {
            let fty = normalize(&infer(f, ctx)?);
            match fty {
                Type::Arrow(param, ret) => {
                    let aty = infer(a, ctx)?;
                    if !type_eq(&aty, &param) {
                        return Err(TypeError::TypeMismatch {
                            expected: *param,
                            found: aty,
                        });
                    }
                    Ok(*ret)
                }
                other => Err(TypeError::NotAFunction { found: other }),
            }
        }

        Term::TyAbs(x, k, body) => {
            let mut ctx2 = ctx.clone();
            ctx2.kinds.insert(x.clone(), k.clone());
            let body_ty = infer(body, &ctx2)?;
            Ok(Type::forall(x.clone(), k.clone(), body_ty))
        }

        Term::TyApp(f, ty_arg) => {
            let arg_k = kind_of(ty_arg, ctx)?;
            let fty = normalize(&infer(f, ctx)?);
            match fty {
                Type::ForAll(x, k, body) => {
                    if k != arg_k {
                        return Err(TypeError::KindMismatch {
                            expected: k,
                            found: arg_k,
                        });
                    }
                    Ok(type_subst(&body, &x, ty_arg))
                }
                other => Err(TypeError::NotPolymorphic { found: other }),
            }
        }

        Term::If(c, t1, t2) => {
            let tc = infer(c, ctx)?;
            if !type_eq(&tc, &Type::Bool) {
                return Err(TypeError::TypeMismatch {
                    expected: Type::Bool,
                    found: tc,
                });
            }
            let tt = infer(t1, ctx)?;
            let te = infer(t2, ctx)?;
            if !type_eq(&tt, &te) {
                return Err(TypeError::TypeMismatch {
                    expected: tt,
                    found: te,
                });
            }
            Ok(tt)
        }

        Term::BinOp(op, a, b) => {
            let ta = infer(a, ctx)?;
            let tb = infer(b, ctx)?;
            if !type_eq(&ta, &Type::Int) {
                return Err(TypeError::TypeMismatch {
                    expected: Type::Int,
                    found: ta,
                });
            }
            if !type_eq(&tb, &Type::Int) {
                return Err(TypeError::TypeMismatch {
                    expected: Type::Int,
                    found: tb,
                });
            }
            Ok(match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul => Type::Int,
                BinOp::Eq | BinOp::Lt => Type::Bool,
            })
        }

        Term::Let(x, e1, e2) => {
            let t1 = infer(e1, ctx)?;
            let mut ctx2 = ctx.clone();
            ctx2.values.insert(x.clone(), t1);
            infer(e2, &ctx2)
        }
    }
}

pub fn type_of(t: &Term) -> Result<Type, TypeError> {
    let ty = infer(t, &Ctx::default())?;
    Ok(normalize(&ty))
}

pub fn kind_of_type(t: &Type) -> Result<Kind, TypeError> {
    kind_of(t, &Ctx::default())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fomega::parser::{parse, parse_type_str};

    fn typeof_str(input: &str) -> Result<Type, TypeError> {
        let t = parse(input).expect("parse term");
        type_of(&t)
    }

    fn kind_of_str(input: &str) -> Result<Kind, TypeError> {
        let t = parse_type_str(input).expect("parse type");
        kind_of_type(&t)
    }

    #[test]
    fn identity_type_operator_has_star_to_star() {
        // λT::*. T  has kind  * -> *
        assert_eq!(
            kind_of_str("\\T::*. T").unwrap(),
            Kind::arrow(Kind::Star, Kind::Star)
        );
    }

    #[test]
    fn pair_constructor_has_kind_star_star_star() {
        // λA::* B::*. ∀C. (A -> B -> C) -> C   :  * -> * -> *
        // (Church-encoded pair as a type operator)
        let k = kind_of_str("\\A::* B::*. forall C. (A -> B -> C) -> C").unwrap();
        assert_eq!(
            k,
            Kind::arrow(Kind::Star, Kind::arrow(Kind::Star, Kind::Star))
        );
    }

    #[test]
    fn applying_id_op_to_int_normalizes_to_int() {
        // (λT::*. T) Int   should be equal to   Int
        let t = parse_type_str("(\\T::*. T) Int").unwrap();
        assert!(type_eq(&t, &Type::Int));
    }

    #[test]
    fn higher_kinded_term_typechecks() {
        // /\F::* -> *. \x:F Int. x   :   ∀F::* -> *. F Int -> F Int
        let ty = typeof_str("/\\F::* -> *. \\x:F Int. x").unwrap();
        let expected = Type::forall(
            "F",
            Kind::arrow(Kind::Star, Kind::Star),
            Type::arrow(
                Type::app(Type::var("F"), Type::Int),
                Type::app(Type::var("F"), Type::Int),
            ),
        );
        assert!(type_eq(&ty, &expected));
    }

    #[test]
    fn instantiating_higher_kinded_function_with_id_op() {
        // (/\F::* -> *. \x:F Int. x) [\T::*. T] 5  :  Int
        // After the type-application, F = λT::*. T, so F Int reduces to Int.
        // So the function has type Int -> Int and 5 :: Int, result is Int.
        let ty = typeof_str("(/\\F::* -> *. \\x:F Int. x) [\\T::*. T] 5").unwrap();
        assert!(type_eq(&ty, &Type::Int));
    }

    #[test]
    fn kind_mismatch_on_type_application() {
        // Trying to apply F (which expects a type operator) to a proper type
        // /\F::* -> *. ...  instantiated with [Int]   should fail kind check.
        let r = typeof_str("(/\\F::* -> *. \\x:F Int. x) [Int]");
        assert!(r.is_err(), "expected kind error, got {r:?}");
    }

    #[test]
    fn cannot_use_type_operator_where_proper_type_expected() {
        // \x: (\T::*. T). x   — the annotation has kind * -> *, not *.
        // This should be rejected.
        assert!(typeof_str("\\x: (\\T::*. T). x").is_err());
    }
}
