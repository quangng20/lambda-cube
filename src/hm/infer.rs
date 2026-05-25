//! Hindley-Milner type inference — Algorithm W.
//!
//! Given a term, infer its most general (principal) type, with no type
//! annotations required from the user. Polymorphism is introduced at
//! `let` bindings: free type variables not constrained by the surrounding
//! environment are generalized to ∀-quantified type schemes.
//!
//! Rank-1 only: ∀-quantifiers never appear nested inside other types.
//! This is what makes inference decidable. (Going beyond rank-1, as in
//! System F, makes inference undecidable.)

use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::hm::ast::{BinOp, Scheme, Term, Type};

pub type Subst = HashMap<String, Type>;
pub type Env = HashMap<String, Scheme>;

#[derive(Debug, Clone)]
pub enum TypeError {
    UnboundVariable(String),
    Mismatch { t1: Type, t2: Type },
    OccursCheck { var: String, ty: Type },
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeError::UnboundVariable(x) => write!(f, "unbound variable: {x}"),
            TypeError::Mismatch { t1, t2 } => {
                write!(f, "cannot unify types: {t1} and {t2}")
            }
            TypeError::OccursCheck { var, ty } => {
                write!(
                    f,
                    "occurs check failed: {var} would refer to itself in {ty}\n  \
                     (a type cannot contain itself — this rejects terms like \\x. x x)"
                )
            }
        }
    }
}

#[derive(Default)]
pub struct State {
    counter: u32,
}

impl State {
    pub fn fresh(&mut self) -> Type {
        let n = self.counter;
        self.counter += 1;
        Type::Var(format!("t{n}"))
    }
}

// ===== Free type variables =====

pub fn ftv(t: &Type) -> HashSet<String> {
    let mut acc = HashSet::new();
    fn rec(t: &Type, acc: &mut HashSet<String>) {
        match t {
            Type::Int | Type::Bool => {}
            Type::Var(x) => {
                acc.insert(x.clone());
            }
            Type::Arrow(a, b) => {
                rec(a, acc);
                rec(b, acc);
            }
        }
    }
    rec(t, &mut acc);
    acc
}

pub fn ftv_scheme(s: &Scheme) -> HashSet<String> {
    let mut fv = ftv(&s.ty);
    for v in &s.vars {
        fv.remove(v);
    }
    fv
}

pub fn ftv_env(env: &Env) -> HashSet<String> {
    let mut acc = HashSet::new();
    for sch in env.values() {
        acc.extend(ftv_scheme(sch));
    }
    acc
}

// ===== Substitutions =====

pub fn apply_type(s: &Subst, t: &Type) -> Type {
    match t {
        Type::Int => Type::Int,
        Type::Bool => Type::Bool,
        Type::Var(x) => s.get(x).cloned().unwrap_or_else(|| Type::Var(x.clone())),
        Type::Arrow(a, b) => Type::arrow(apply_type(s, a), apply_type(s, b)),
    }
}

pub fn apply_scheme(s: &Subst, sch: &Scheme) -> Scheme {
    // Don't substitute the bound variables.
    let mut s_filtered = s.clone();
    for v in &sch.vars {
        s_filtered.remove(v);
    }
    Scheme {
        vars: sch.vars.clone(),
        ty: apply_type(&s_filtered, &sch.ty),
    }
}

pub fn apply_env(s: &Subst, env: &Env) -> Env {
    env.iter()
        .map(|(k, v)| (k.clone(), apply_scheme(s, v)))
        .collect()
}

// Composition s1 ∘ s2: apply s2 first, then s1. Equivalent to:
//   - For each (k, v) in s2, the result has (k, apply(s1, v)).
//   - Bindings in s1 not shadowed by s2 are added.
pub fn compose(s1: &Subst, s2: &Subst) -> Subst {
    let mut result: Subst = s2
        .iter()
        .map(|(k, v)| (k.clone(), apply_type(s1, v)))
        .collect();
    for (k, v) in s1 {
        result.entry(k.clone()).or_insert_with(|| v.clone());
    }
    result
}

// ===== Unification (Robinson's algorithm) =====

pub fn unify(t1: &Type, t2: &Type) -> Result<Subst, TypeError> {
    match (t1, t2) {
        (Type::Int, Type::Int) | (Type::Bool, Type::Bool) => Ok(Subst::new()),
        (Type::Arrow(a1, b1), Type::Arrow(a2, b2)) => {
            let s1 = unify(a1, a2)?;
            let s2 = unify(&apply_type(&s1, b1), &apply_type(&s1, b2))?;
            Ok(compose(&s2, &s1))
        }
        (Type::Var(a), other) | (other, Type::Var(a)) => {
            if matches!(other, Type::Var(b) if a == b) {
                Ok(Subst::new())
            } else if ftv(other).contains(a) {
                Err(TypeError::OccursCheck {
                    var: a.clone(),
                    ty: other.clone(),
                })
            } else {
                let mut s = Subst::new();
                s.insert(a.clone(), other.clone());
                Ok(s)
            }
        }
        _ => Err(TypeError::Mismatch {
            t1: t1.clone(),
            t2: t2.clone(),
        }),
    }
}

// ===== Generalization / instantiation =====

pub fn generalize(env: &Env, t: &Type) -> Scheme {
    let env_fv = ftv_env(env);
    let mut vars: Vec<String> = ftv(t).difference(&env_fv).cloned().collect();
    vars.sort(); // stable order for tests / display
    Scheme {
        vars,
        ty: t.clone(),
    }
}

pub fn instantiate(sch: &Scheme, st: &mut State) -> Type {
    let s: Subst = sch.vars.iter().map(|v| (v.clone(), st.fresh())).collect();
    apply_type(&s, &sch.ty)
}

// ===== Algorithm W =====

pub fn infer(env: &Env, t: &Term, st: &mut State) -> Result<(Subst, Type), TypeError> {
    match t {
        Term::Var(x) => {
            let sch = env
                .get(x)
                .ok_or_else(|| TypeError::UnboundVariable(x.clone()))?;
            Ok((Subst::new(), instantiate(sch, st)))
        }
        Term::IntLit(_) => Ok((Subst::new(), Type::Int)),
        Term::BoolLit(_) => Ok((Subst::new(), Type::Bool)),

        Term::Abs(x, body) => {
            let beta = st.fresh();
            let mut env2 = env.clone();
            env2.insert(
                x.clone(),
                Scheme {
                    vars: Vec::new(),
                    ty: beta.clone(),
                },
            );
            let (s, body_ty) = infer(&env2, body, st)?;
            Ok((s.clone(), Type::arrow(apply_type(&s, &beta), body_ty)))
        }

        Term::App(f, a) => {
            let (s1, t_f) = infer(env, f, st)?;
            let env2 = apply_env(&s1, env);
            let (s2, t_a) = infer(&env2, a, st)?;
            let beta = st.fresh();
            let s3 = unify(&apply_type(&s2, &t_f), &Type::arrow(t_a, beta.clone()))?;
            let s = compose(&s3, &compose(&s2, &s1));
            Ok((s, apply_type(&s3, &beta)))
        }

        Term::Let(x, e1, e2) => {
            let (s1, t1) = infer(env, e1, st)?;
            let env1 = apply_env(&s1, env);
            let sch = generalize(&env1, &t1);
            let mut env2 = env1.clone();
            env2.insert(x.clone(), sch);
            let (s2, t2) = infer(&env2, e2, st)?;
            Ok((compose(&s2, &s1), t2))
        }

        Term::LetRec(x, e1, e2) => {
            // Introduce a fresh monotype β for the recursive binder.
            let beta = st.fresh();
            let mut env1 = env.clone();
            env1.insert(
                x.clone(),
                Scheme {
                    vars: Vec::new(),
                    ty: beta.clone(),
                },
            );
            let (s1, t1) = infer(&env1, e1, st)?;
            // β must equal the inferred type of e1.
            let s2 = unify(&apply_type(&s1, &beta), &t1)?;
            let s12 = compose(&s2, &s1);
            // Now generalize x's type (β instantiated through the substitutions)
            // over the original environment.
            let env_after = apply_env(&s12, env);
            let final_t1 = apply_type(&s12, &beta);
            let sch = generalize(&env_after, &final_t1);
            let mut env2 = env_after;
            env2.insert(x.clone(), sch);
            let (s3, t2) = infer(&env2, e2, st)?;
            Ok((compose(&s3, &s12), t2))
        }

        Term::If(c, t1, t2) => {
            let (s1, tc) = infer(env, c, st)?;
            let s_c = unify(&tc, &Type::Bool)?;
            let s_so_far = compose(&s_c, &s1);
            let env1 = apply_env(&s_so_far, env);
            let (s2, tt) = infer(&env1, t1, st)?;
            let s_so_far = compose(&s2, &s_so_far);
            let env2 = apply_env(&s_so_far, env);
            let (s3, te) = infer(&env2, t2, st)?;
            let s_so_far = compose(&s3, &s_so_far);
            let s_branches = unify(&apply_type(&s_so_far, &tt), &apply_type(&s_so_far, &te))?;
            let final_subst = compose(&s_branches, &s_so_far);
            Ok((final_subst.clone(), apply_type(&final_subst, &tt)))
        }

        Term::BinOp(op, a, b) => {
            let (s1, ta) = infer(env, a, st)?;
            let s_a = unify(&ta, &Type::Int)?;
            let s_so_far = compose(&s_a, &s1);
            let env1 = apply_env(&s_so_far, env);
            let (s2, tb) = infer(&env1, b, st)?;
            let s_b = unify(&apply_type(&s2, &tb), &Type::Int)?;
            let s_full = compose(&s_b, &compose(&s2, &s_so_far));
            let result_ty = match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul => Type::Int,
                BinOp::Eq | BinOp::Lt => Type::Bool,
            };
            Ok((s_full, result_ty))
        }

        Term::Fix(_) => {
            // Fix is internal — produced by the evaluator from LetRec — and
            // should never be type-checked directly. If we get here, it's a bug.
            unreachable!(
                "Fix terms are not produced by the parser; the type checker should never see one"
            )
        }
    }
}

// Top-level: infer the type and generalize to a closed scheme.
pub fn type_of(t: &Term) -> Result<Scheme, TypeError> {
    let mut st = State::default();
    let (s, ty) = infer(&Env::new(), t, &mut st)?;
    let final_ty = apply_type(&s, &ty);
    Ok(generalize(&Env::new(), &final_ty))
}

// Rename internal type vars (t0, t1, …) to user-friendly a, b, c, …
// for display.
pub fn prettify(sch: &Scheme) -> Scheme {
    let names: Vec<String> = (0..sch.vars.len()).map(pretty_name).collect();
    let s: Subst = sch
        .vars
        .iter()
        .zip(&names)
        .map(|(v, n)| (v.clone(), Type::Var(n.clone())))
        .collect();
    Scheme {
        vars: names,
        ty: apply_type(&s, &sch.ty),
    }
}

fn pretty_name(i: usize) -> String {
    // a, b, …, z, a1, b1, …
    let letter = char::from(b'a' + u8::try_from(i % 26).unwrap_or(0));
    let suffix = i / 26;
    if suffix == 0 {
        letter.to_string()
    } else {
        format!("{letter}{suffix}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hm::parser::parse;

    fn infer_pretty(input: &str) -> Result<String, String> {
        let t = parse(input).map_err(|e| format!("parse: {e}"))?;
        let sch = type_of(&t).map_err(|e| format!("typeck: {e}"))?;
        Ok(format!("{}", prettify(&sch)))
    }

    #[test]
    fn int_literal() {
        assert_eq!(infer_pretty("42").unwrap(), "Int");
    }

    #[test]
    fn bool_literal() {
        assert_eq!(infer_pretty("true").unwrap(), "Bool");
    }

    #[test]
    fn polymorphic_identity_inferred_with_no_annotation() {
        // The famous one. No type annotation; HM infers the most general type.
        assert_eq!(infer_pretty("\\x. x").unwrap(), "∀a. a -> a");
    }

    #[test]
    fn const_function() {
        // \x. \y. x  has type  forall a b. a -> b -> a
        assert_eq!(infer_pretty("\\x. \\y. x").unwrap(), "∀a b. a -> b -> a");
    }

    #[test]
    fn twice() {
        // \f. \x. f (f x)  :  forall a. (a -> a) -> a -> a
        assert_eq!(
            infer_pretty("\\f. \\x. f (f x)").unwrap(),
            "∀a. (a -> a) -> a -> a"
        );
    }

    #[test]
    fn add_one_function() {
        assert_eq!(infer_pretty("\\x. x + 1").unwrap(), "Int -> Int");
    }

    #[test]
    fn application_specializes_polymorphic_id() {
        assert_eq!(infer_pretty("(\\x. x) 5").unwrap(), "Int");
    }

    #[test]
    fn let_polymorphism_used_at_two_types() {
        // The decisive let-polymorphism test: same `id` used at Int AND Bool.
        // Pure System F needs explicit type abstractions for this; HM gets it for free.
        assert_eq!(
            infer_pretty("let id = \\x. x in if id true then id 1 else id 2").unwrap(),
            "Int"
        );
    }

    #[test]
    fn occurs_check_rejects_self_application() {
        // \x. x x  needs  x : a -> b  and  x : a, which forces  a = a -> b.
        // Occurs check catches this.
        assert!(infer_pretty("\\x. x x").is_err());
    }

    #[test]
    fn type_mismatch_arithmetic_on_bool() {
        assert!(infer_pretty("1 + true").is_err());
    }

    #[test]
    fn type_mismatch_if_condition() {
        assert!(infer_pretty("if 1 then 2 else 3").is_err());
    }

    #[test]
    fn type_mismatch_if_branches() {
        assert!(infer_pretty("if true then 1 else false").is_err());
    }

    #[test]
    fn let_rec_factorial_has_int_to_int_type() {
        assert_eq!(
            infer_pretty("let rec fact = \\n. if n == 0 then 1 else n * fact (n - 1) in fact")
                .unwrap(),
            "Int -> Int"
        );
    }

    #[test]
    fn let_rec_with_polymorphic_use_after() {
        // Recursive function infers its type, then is used polymorphically afterward.
        // Here id is monomorphic in its body but we test that a recursive *polymorphic*
        // function gets generalized.
        assert_eq!(
            infer_pretty("let rec loop = \\x. loop x in loop").unwrap(),
            "∀a b. a -> b"
        );
    }

    #[test]
    fn unbound_variable_is_error() {
        assert!(infer_pretty("x").is_err());
    }
}
