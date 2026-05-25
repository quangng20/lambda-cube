use std::collections::HashMap;
use std::fmt;

use crate::stlc::ast::{BinOp, Term, Type};

#[derive(Debug, Clone)]
pub enum TypeError {
    UnboundVariable(String),
    TypeMismatch {
        expected: Type,
        found: Type,
        ctx: String,
    },
    NotAFunction {
        found: Type,
    },
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeError::UnboundVariable(x) => write!(f, "unbound variable: {}", x),
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
        }
    }
}

pub type Env = HashMap<String, Type>;

// Bidirectional type checker.
//   `infer`  : compute the type of `t` in environment `env`.
//   `check`  : verify `t` has the given type. Falls back to `infer` + equality.
//
// For STLC with required lambda annotations, `infer` is sufficient for every form.
// We expose `check` to keep the bidirectional discipline and to make the path
// to System F / dependent types (where checking is essential) feel natural.

pub fn infer(t: &Term, env: &Env) -> Result<Type, TypeError> {
    match t {
        Term::Var(x) => env
            .get(x)
            .cloned()
            .ok_or_else(|| TypeError::UnboundVariable(x.clone())),

        Term::IntLit(_) => Ok(Type::Int),
        Term::BoolLit(_) => Ok(Type::Bool),

        Term::Abs(x, ty, body) => {
            let mut env2 = env.clone();
            env2.insert(x.clone(), ty.clone());
            let body_ty = infer(body, &env2)?;
            Ok(Type::arrow(ty.clone(), body_ty))
        }

        Term::App(f, a) => {
            let fty = infer(f, env)?;
            match fty {
                Type::Arrow(param, ret) => {
                    check(a, &param, env)?;
                    Ok(*ret)
                }
                other => Err(TypeError::NotAFunction { found: other }),
            }
        }

        Term::If(c, t1, t2) => {
            check(c, &Type::Bool, env)?;
            let ty = infer(t1, env)?;
            check(t2, &ty, env)?;
            Ok(ty)
        }

        Term::BinOp(op, a, b) => {
            check(a, &Type::Int, env)?;
            check(b, &Type::Int, env)?;
            Ok(match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul => Type::Int,
                BinOp::Eq | BinOp::Lt => Type::Bool,
            })
        }

        Term::Let(x, e1, e2) => {
            let t1 = infer(e1, env)?;
            let mut env2 = env.clone();
            env2.insert(x.clone(), t1);
            infer(e2, &env2)
        }
    }
}

pub fn check(t: &Term, expected: &Type, env: &Env) -> Result<(), TypeError> {
    let found = infer(t, env)?;
    if &found == expected {
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
        Term::If(_, _, _) => "if-expression".to_string(),
        Term::Let(x, _, _) => format!("let-binding of `{}`", x),
        Term::BinOp(op, _, _) => format!("`{}` operator", op.symbol()),
    }
}

pub fn type_of(t: &Term) -> Result<Type, TypeError> {
    infer(t, &Env::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stlc::parser::parse;

    fn ok(input: &str, expected: Type) {
        let t = parse(input).expect("parse");
        let ty = type_of(&t).expect("typecheck");
        assert_eq!(ty, expected, "for input {}", input);
    }

    fn err(input: &str) {
        let t = parse(input).expect("parse");
        assert!(type_of(&t).is_err(), "expected type error for {}", input);
    }

    #[test]
    fn int_literal_has_type_int() {
        ok("42", Type::Int);
    }

    #[test]
    fn bool_literal_has_type_bool() {
        ok("true", Type::Bool);
    }

    #[test]
    fn identity_on_int() {
        ok("\\x:Int. x", Type::arrow(Type::Int, Type::Int));
    }

    #[test]
    fn application_int_to_int() {
        ok("(\\x:Int. x + 1) 5", Type::Int);
    }

    #[test]
    fn if_branches_must_agree() {
        err("if true then 1 else false");
    }

    #[test]
    fn if_condition_must_be_bool() {
        err("if 1 then 2 else 3");
    }

    #[test]
    fn cannot_apply_int() {
        err("5 3");
    }

    #[test]
    fn cannot_add_bool() {
        err("true + 1");
    }

    #[test]
    fn let_polymorphism_is_not_available_in_stlc() {
        // In STLC, `let id = \x:Int. x in id` has a fixed type — no polymorphism.
        // This expression typechecks, but `id true` afterwards would not.
        ok("let id = \\x:Int. x in id 5", Type::Int);
        err("let id = \\x:Int. x in id true");
    }

    #[test]
    fn y_combinator_is_not_typeable() {
        // Y = \f. (\x. f (x x)) (\x. f (x x))
        // The self-application (x x) needs x to have a type T = T -> something,
        // which is not expressible in STLC. So you cannot write the Y combinator
        // — this is the famous "STLC is strongly normalizing" property: no
        // unrestricted recursion. Trying any annotation fails to typecheck.
        err("\\f:Int -> Int. (\\x:Int. f (x x)) (\\x:Int. f (x x))");
    }

    #[test]
    fn higher_order_function() {
        // twice : (Int -> Int) -> Int -> Int
        ok(
            "\\f:Int -> Int. \\x:Int. f (f x)",
            Type::arrow(
                Type::arrow(Type::Int, Type::Int),
                Type::arrow(Type::Int, Type::Int),
            ),
        );
    }

    #[test]
    fn unbound_variable_is_error() {
        err("x");
    }
}
