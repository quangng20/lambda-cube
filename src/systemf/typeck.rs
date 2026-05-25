use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::systemf::ast::{BinOp, Term, Type};

#[derive(Debug, Clone)]
pub enum TypeError {
    UnboundVariable(String),
    UnboundTypeVariable(String),
    TypeMismatch {
        expected: Type,
        found: Type,
        ctx: String,
    },
    NotAFunction {
        found: Type,
    },
    NotPolymorphic {
        found: Type,
    },
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeError::UnboundVariable(x) => write!(f, "unbound variable: {}", x),
            TypeError::UnboundTypeVariable(x) => write!(f, "unbound type variable: {}", x),
            TypeError::TypeMismatch {
                expected,
                found,
                ctx,
            } => write!(
                f,
                "type mismatch in {}: expected {}, found {}",
                ctx, expected, found
            ),
            TypeError::NotAFunction { found } => {
                write!(f, "expected a function, found value of type {}", found)
            }
            TypeError::NotPolymorphic { found } => {
                write!(f, "type application requires a ∀-type, found {}", found)
            }
        }
    }
}

#[derive(Default, Clone)]
pub struct Ctx {
    pub values: HashMap<String, Type>,
    pub types: HashSet<String>,
}

pub fn free_type_vars(t: &Type) -> HashSet<String> {
    let mut s = HashSet::new();
    fn rec(t: &Type, acc: &mut HashSet<String>) {
        match t {
            Type::Bool | Type::Int => {}
            Type::Var(x) => {
                acc.insert(x.clone());
            }
            Type::Arrow(a, b) => {
                rec(a, acc);
                rec(b, acc);
            }
            Type::ForAll(x, body) => {
                let mut inner = HashSet::new();
                rec(body, &mut inner);
                inner.remove(x);
                acc.extend(inner);
            }
        }
    }
    rec(t, &mut s);
    s
}

fn fresh_type_name(base: &str, avoid: &HashSet<String>) -> String {
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

// Capture-avoiding type-level substitution: [s/x] t.
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
        Type::ForAll(y, body) => {
            if y == x {
                Type::ForAll(y.clone(), body.clone())
            } else {
                let fv_s = free_type_vars(s);
                if fv_s.contains(y) {
                    let mut avoid = fv_s;
                    avoid.extend(free_type_vars(body));
                    avoid.insert(x.to_string());
                    let new_y = fresh_type_name(y, &avoid);
                    let renamed = type_subst(body, y, &Type::Var(new_y.clone()));
                    Type::ForAll(new_y, Box::new(type_subst(&renamed, x, s)))
                } else {
                    Type::ForAll(y.clone(), Box::new(type_subst(body, x, s)))
                }
            }
        }
    }
}

// Alpha-equivalence: forall T. T -> T  ==  forall U. U -> U.
pub fn type_eq(a: &Type, b: &Type) -> bool {
    match (a, b) {
        (Type::Bool, Type::Bool) | (Type::Int, Type::Int) => true,
        (Type::Var(x), Type::Var(y)) => x == y,
        (Type::Arrow(a1, a2), Type::Arrow(b1, b2)) => type_eq(a1, b1) && type_eq(a2, b2),
        (Type::ForAll(x, ax), Type::ForAll(y, by)) => {
            // Rename y to x in by, then compare bodies.
            let by_renamed = type_subst(by, y, &Type::Var(x.clone()));
            type_eq(ax, &by_renamed)
        }
        _ => false,
    }
}

// Type-variable substitution inside a term — used for TyApp reduction at runtime
// and is also useful here for inferred TyApp result types.
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

        Term::TyAbs(y, body) => {
            if y == x {
                Term::TyAbs(y.clone(), body.clone())
            } else {
                let fv_s = free_type_vars(s);
                if fv_s.contains(y) {
                    let mut avoid = fv_s;
                    // free type vars appearing in the body's types
                    avoid.extend(free_type_vars_in_term(body));
                    avoid.insert(x.to_string());
                    let new_y = fresh_type_name(y, &avoid);
                    let renamed = ty_subst_in_term(body, y, &Type::Var(new_y.clone()));
                    Term::TyAbs(new_y, Box::new(ty_subst_in_term(&renamed, x, s)))
                } else {
                    Term::TyAbs(y.clone(), Box::new(ty_subst_in_term(body, x, s)))
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
                acc.extend(free_type_vars(ty));
                rec(body, acc);
            }
            Term::App(f, a) => {
                rec(f, acc);
                rec(a, acc);
            }
            Term::TyAbs(x, body) => {
                let mut inner = HashSet::new();
                rec(body, &mut inner);
                inner.remove(x);
                acc.extend(inner);
            }
            Term::TyApp(f, ty) => {
                rec(f, acc);
                acc.extend(free_type_vars(ty));
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

fn check_type_wellformed(t: &Type, ctx: &Ctx) -> Result<(), TypeError> {
    match t {
        Type::Bool | Type::Int => Ok(()),
        Type::Var(x) => {
            if ctx.types.contains(x) {
                Ok(())
            } else {
                Err(TypeError::UnboundTypeVariable(x.clone()))
            }
        }
        Type::Arrow(a, b) => {
            check_type_wellformed(a, ctx)?;
            check_type_wellformed(b, ctx)
        }
        Type::ForAll(x, body) => {
            let mut ctx2 = ctx.clone();
            ctx2.types.insert(x.clone());
            check_type_wellformed(body, &ctx2)
        }
    }
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
            check_type_wellformed(ty, ctx)?;
            let mut ctx2 = ctx.clone();
            ctx2.values.insert(x.clone(), ty.clone());
            let body_ty = infer(body, &ctx2)?;
            Ok(Type::arrow(ty.clone(), body_ty))
        }

        Term::App(f, a) => {
            let fty = infer(f, ctx)?;
            match fty {
                Type::Arrow(param, ret) => {
                    check(a, &param, ctx)?;
                    Ok(*ret)
                }
                other => Err(TypeError::NotAFunction { found: other }),
            }
        }

        Term::TyAbs(x, body) => {
            let mut ctx2 = ctx.clone();
            ctx2.types.insert(x.clone());
            let body_ty = infer(body, &ctx2)?;
            Ok(Type::forall(x.clone(), body_ty))
        }

        Term::TyApp(f, ty_arg) => {
            check_type_wellformed(ty_arg, ctx)?;
            let fty = infer(f, ctx)?;
            match fty {
                Type::ForAll(x, body) => Ok(type_subst(&body, &x, ty_arg)),
                other => Err(TypeError::NotPolymorphic { found: other }),
            }
        }

        Term::If(c, t1, t2) => {
            check(c, &Type::Bool, ctx)?;
            let ty = infer(t1, ctx)?;
            check(t2, &ty, ctx)?;
            Ok(ty)
        }

        Term::BinOp(op, a, b) => {
            check(a, &Type::Int, ctx)?;
            check(b, &Type::Int, ctx)?;
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

pub fn check(t: &Term, expected: &Type, ctx: &Ctx) -> Result<(), TypeError> {
    let found = infer(t, ctx)?;
    if type_eq(&found, expected) {
        Ok(())
    } else {
        Err(TypeError::TypeMismatch {
            expected: expected.clone(),
            found,
            ctx: describe(t),
        })
    }
}

fn describe(t: &Term) -> String {
    match t {
        Term::Var(x) => format!("variable `{}`", x),
        Term::IntLit(n) => format!("integer literal `{}`", n),
        Term::BoolLit(b) => format!("boolean literal `{}`", b),
        Term::Abs(x, _, _) => format!("abstraction over `{}`", x),
        Term::App(_, _) => "application".to_string(),
        Term::TyAbs(x, _) => format!("type abstraction over `{}`", x),
        Term::TyApp(_, _) => "type application".to_string(),
        Term::If(_, _, _) => "if-expression".to_string(),
        Term::Let(x, _, _) => format!("let-binding of `{}`", x),
        Term::BinOp(op, _, _) => format!("`{}` operator", op.symbol()),
    }
}

pub fn type_of(t: &Term) -> Result<Type, TypeError> {
    infer(t, &Ctx::default())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::systemf::parser::parse;

    fn typeof_str(input: &str) -> Result<Type, TypeError> {
        let t = parse(input).expect("parse");
        type_of(&t)
    }

    #[test]
    fn polymorphic_identity_has_forall_type() {
        let ty = typeof_str("/\\T. \\x:T. x").unwrap();
        assert!(type_eq(
            &ty,
            &Type::forall("T", Type::arrow(Type::var("T"), Type::var("T")))
        ));
    }

    #[test]
    fn alpha_equivalence_of_forall() {
        // forall T. T -> T  is alpha-equivalent to  forall U. U -> U
        let a = Type::forall("T", Type::arrow(Type::var("T"), Type::var("T")));
        let b = Type::forall("U", Type::arrow(Type::var("U"), Type::var("U")));
        assert!(type_eq(&a, &b));
    }

    #[test]
    fn type_application_specializes_polymorphic_id() {
        // (/\T. \x:T. x) [Int]   :  Int -> Int
        let ty = typeof_str("(/\\T. \\x:T. x) [Int]").unwrap();
        assert_eq!(ty, Type::arrow(Type::Int, Type::Int));
    }

    #[test]
    fn polymorphic_identity_applied_at_int_then_to_value() {
        // (/\T. \x:T. x) [Int] 5   :  Int
        let ty = typeof_str("(/\\T. \\x:T. x) [Int] 5").unwrap();
        assert_eq!(ty, Type::Int);
    }

    #[test]
    fn polymorphic_identity_applied_at_bool() {
        let ty = typeof_str("(/\\T. \\x:T. x) [Bool] true").unwrap();
        assert_eq!(ty, Type::Bool);
    }

    #[test]
    fn k_combinator_has_doubly_polymorphic_type() {
        // K = /\T. /\U. \x:T. \y:U. x   :   forall T U. T -> U -> T
        let ty = typeof_str("/\\T. /\\U. \\x:T. \\y:U. x").unwrap();
        let expected = Type::forall(
            "T",
            Type::forall(
                "U",
                Type::arrow(Type::var("T"), Type::arrow(Type::var("U"), Type::var("T"))),
            ),
        );
        assert!(type_eq(&ty, &expected));
    }

    #[test]
    fn cannot_apply_type_to_non_polymorphic_value() {
        // (\x:Int. x) [Int]  -- error: not polymorphic
        assert!(typeof_str("(\\x:Int. x) [Int]").is_err());
    }

    #[test]
    fn unbound_type_variable_is_error() {
        assert!(typeof_str("\\x:T. x").is_err());
    }

    #[test]
    fn impredicative_instantiation_is_allowed() {
        // In System F, we can instantiate ∀ at *any* type — including another ∀-type.
        // (/\T. \x:T. x) [forall S. S -> S]  :  (forall S. S -> S) -> (forall S. S -> S)
        let ty = typeof_str("(/\\T. \\x:T. x) [forall S. S -> S]").unwrap();
        let id_ty = Type::forall("S", Type::arrow(Type::var("S"), Type::var("S")));
        let expected = Type::arrow(id_ty.clone(), id_ty);
        assert!(type_eq(&ty, &expected));
    }
}
