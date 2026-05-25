use std::collections::HashSet;

use crate::untyped::ast::Term;

pub fn free_vars(t: &Term) -> HashSet<String> {
    let mut acc = HashSet::new();
    collect_free(t, &mut acc);
    acc
}

fn collect_free(t: &Term, acc: &mut HashSet<String>) {
    match t {
        Term::Var(x) => {
            acc.insert(x.clone());
        }
        Term::Abs(x, body) => {
            let mut inner = HashSet::new();
            collect_free(body, &mut inner);
            inner.remove(x);
            acc.extend(inner);
        }
        Term::App(f, a) => {
            collect_free(f, acc);
            collect_free(a, acc);
        }
    }
}

// Produce a name that is not in `avoid`. Strips trailing digits from `base`
// to use as a stem, then appends 1, 2, 3, ... until a free name is found.
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

// Capture-avoiding substitution: [s/x] t   (replace free `x` in `t` with `s`).
pub fn subst(t: Term, x: &str, s: &Term) -> Term {
    match t {
        Term::Var(y) => {
            if y == x {
                s.clone()
            } else {
                Term::Var(y)
            }
        }
        Term::App(f, a) => Term::App(Box::new(subst(*f, x, s)), Box::new(subst(*a, x, s))),
        Term::Abs(y, body) => {
            if y == x {
                // x is shadowed by the binder; don't substitute inside.
                Term::Abs(y, body)
            } else {
                let fv_s = free_vars(s);
                if fv_s.contains(&y) {
                    // y would capture a free variable of s; alpha-rename.
                    let mut avoid = fv_s;
                    avoid.extend(free_vars(&body));
                    avoid.insert(x.to_string());
                    let new_y = fresh_name(&y, &avoid);
                    let renamed_body = subst(*body, &y, &Term::Var(new_y.clone()));
                    Term::Abs(new_y, Box::new(subst(renamed_body, x, s)))
                } else {
                    Term::Abs(y, Box::new(subst(*body, x, s)))
                }
            }
        }
    }
}

// One step of normal-order beta-reduction: find the leftmost-outermost redex
// (anywhere in the term, including under abstractions) and reduce it.
// Returns None if the term is in normal form.
pub fn reduce_step(t: &Term) -> Option<Term> {
    match t {
        Term::App(f, a) => {
            if let Term::Abs(x, body) = f.as_ref() {
                // The whole app is itself a redex — it's the leftmost-outermost.
                Some(subst(body.as_ref().clone(), x, a))
            } else if let Some(f_new) = reduce_step(f) {
                Some(Term::App(Box::new(f_new), a.clone()))
            } else {
                reduce_step(a).map(|a_new| Term::App(f.clone(), Box::new(a_new)))
            }
        }
        Term::Abs(x, body) => reduce_step(body).map(|b| Term::Abs(x.clone(), Box::new(b))),
        Term::Var(_) => None,
    }
}

pub struct NormalizeResult {
    pub term: Term,
    pub steps: usize,
    pub reached_normal_form: bool,
}

pub fn normalize(mut t: Term, max_steps: usize) -> NormalizeResult {
    for i in 0..max_steps {
        match reduce_step(&t) {
            Some(next) => t = next,
            None => {
                return NormalizeResult {
                    term: t,
                    steps: i,
                    reached_normal_form: true,
                };
            }
        }
    }
    NormalizeResult {
        term: t,
        steps: max_steps,
        reached_normal_form: false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::untyped::parser::parse;

    fn eval_str(s: &str) -> String {
        let t = parse(s).unwrap();
        let r = normalize(t, 1000);
        assert!(r.reached_normal_form, "did not normalize: {}", r.term);
        format!("{}", r.term)
    }

    #[test]
    fn identity_application() {
        assert_eq!(eval_str("(\\x. x) y"), "y");
    }

    #[test]
    fn k_combinator() {
        // K = \x y. x;  K a b = a
        assert_eq!(eval_str("(\\x y. x) a b"), "a");
    }

    #[test]
    fn s_combinator_on_identities() {
        // S K K = I  i.e.  (\x y z. x z (y z)) K K v = v
        assert_eq!(
            eval_str("(\\x y z. x z (y z)) (\\a b. a) (\\a b. a) v"),
            "v"
        );
    }

    #[test]
    fn capture_avoidance_renames() {
        // (\x. \y. x) y  -- inner y must be renamed so the free y is not captured.
        let r = eval_str("(\\x. \\y. x) y");
        assert_ne!(r, "λy. y", "free y was captured by the bound y");
        // result should be \y'. y for some renamed y'
        assert!(r.contains("y") && r.starts_with("λ"));
    }

    #[test]
    fn church_succ_of_two() {
        // succ = \n f x. f (n f x);  2 = \f x. f (f x)
        // succ 2 should reduce to 3 = \f x. f (f (f x))
        let actual = eval_str("(\\n f x. f (n f x)) (\\f x. f (f x))");
        let expected = eval_str("\\f x. f (f (f x))");
        assert_eq!(actual, expected);
    }

    #[test]
    fn church_add_two_three() {
        // add = \m n f x. m f (n f x);  add 2 3 = 5
        let actual = eval_str("(\\m n f x. m f (n f x)) (\\f x. f (f x)) (\\f x. f (f (f x)))");
        let expected = eval_str("\\f x. f (f (f (f (f x))))");
        assert_eq!(actual, expected);
    }

    #[test]
    fn omega_diverges() {
        // Ω = (\x. x x)(\x. x x) has no normal form.
        let t = parse("(\\x. x x) (\\x. x x)").unwrap();
        let r = normalize(t, 100);
        assert!(!r.reached_normal_form);
        assert_eq!(r.steps, 100);
    }

    #[test]
    fn normal_order_skips_diverging_argument() {
        // (\x. y) Ω  --  normal-order discards Ω without evaluating it,
        // so the whole term reduces to y. (Call-by-value would diverge here.)
        assert_eq!(eval_str("(\\x. y) ((\\x. x x) (\\x. x x))"), "y");
    }
}
