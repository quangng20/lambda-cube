//! A small λP fragment. Types and terms share one syntactic category —
//! that is the defining feature of dependent types: types are first-class
//! values, computed and passed around like any other term.
//!
//! For pedagogical simplicity we use the inconsistent rule `Type : Type`.
//! Real systems (Coq, Agda, Lean) use a universe hierarchy
//! `Type 0 : Type 1 : Type 2 : …` to avoid Girard's paradox. Don't try
//! to prove `False` here; the soundness story is intentionally weak.

use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Eq,
    Lt,
}

impl BinOp {
    pub fn symbol(self) -> &'static str {
        match self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Eq => "==",
            BinOp::Lt => "<",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    Var(String),

    // The single universe. `Universe : Universe` — see the file header.
    Universe,

    // Base "types" — really just constants of type Universe.
    Bool,
    Int,

    BoolLit(bool),
    IntLit(i64),

    // Π x : A. B     — dependent function type.
    // If x doesn't appear free in B, this is the non-dependent arrow A → B.
    Pi(String, Box<Term>, Box<Term>),

    // λ x : A. body
    Lambda(String, Box<Term>, Box<Term>),

    App(Box<Term>, Box<Term>),

    If(Box<Term>, Box<Term>, Box<Term>),
    BinOp(BinOp, Box<Term>, Box<Term>),
    Let(String, Box<Term>, Box<Term>),
}

impl Term {
    pub fn var(s: impl Into<String>) -> Term {
        Term::Var(s.into())
    }
    pub fn pi(x: impl Into<String>, a: Term, b: Term) -> Term {
        Term::Pi(x.into(), Box::new(a), Box::new(b))
    }
    pub fn arrow(a: Term, b: Term) -> Term {
        Term::pi("_", a, b)
    }
    pub fn lambda(x: impl Into<String>, a: Term, body: Term) -> Term {
        Term::Lambda(x.into(), Box::new(a), Box::new(body))
    }
    pub fn app(f: Term, a: Term) -> Term {
        Term::App(Box::new(f), Box::new(a))
    }
    pub fn if_then_else(c: Term, t: Term, e: Term) -> Term {
        Term::If(Box::new(c), Box::new(t), Box::new(e))
    }
    pub fn binop(op: BinOp, a: Term, b: Term) -> Term {
        Term::BinOp(op, Box::new(a), Box::new(b))
    }
    pub fn let_(x: impl Into<String>, e1: Term, e2: Term) -> Term {
        Term::Let(x.into(), Box::new(e1), Box::new(e2))
    }
}

// Free-variable check used by Display to choose `A -> B` vs `Π x : A. B`.
pub fn appears_free(name: &str, t: &Term) -> bool {
    match t {
        Term::Var(x) => x == name,
        Term::Universe | Term::Bool | Term::Int | Term::BoolLit(_) | Term::IntLit(_) => false,
        Term::Pi(x, a, b) | Term::Lambda(x, a, b) => {
            appears_free(name, a) || (x != name && appears_free(name, b))
        }
        Term::App(f, a) => appears_free(name, f) || appears_free(name, a),
        Term::If(c, t1, t2) => {
            appears_free(name, c) || appears_free(name, t1) || appears_free(name, t2)
        }
        Term::BinOp(_, a, b) => appears_free(name, a) || appears_free(name, b),
        Term::Let(x, e1, e2) => appears_free(name, e1) || (x != name && appears_free(name, e2)),
    }
}

impl Term {
    // Precedence:
    //   0  top (Pi, λ, let, if extend right)
    //   1  arrow (right-associative)
    //   2  binop comparison
    //   3  binop add/sub
    //   4  binop mul
    //   5  application
    //   6  atom
    fn fmt_prec(&self, f: &mut fmt::Formatter<'_>, prec: u8) -> fmt::Result {
        let parens = |f: &mut fmt::Formatter<'_>,
                      needs: bool,
                      inner: &dyn Fn(&mut fmt::Formatter<'_>) -> fmt::Result|
         -> fmt::Result {
            if needs {
                write!(f, "(")?;
            }
            inner(f)?;
            if needs {
                write!(f, ")")?;
            }
            Ok(())
        };
        match self {
            Term::Var(x) => write!(f, "{x}"),
            Term::Universe => write!(f, "Type"),
            Term::Bool => write!(f, "Bool"),
            Term::Int => write!(f, "Int"),
            Term::BoolLit(b) => write!(f, "{b}"),
            Term::IntLit(n) => write!(f, "{n}"),

            Term::Pi(x, a, b) => {
                if !appears_free(x, b) {
                    // Non-dependent: print as arrow
                    parens(f, prec > 1, &|f| {
                        a.fmt_prec(f, 2)?;
                        write!(f, " -> ")?;
                        b.fmt_prec(f, 1)
                    })
                } else {
                    parens(f, prec > 0, &|f| {
                        write!(f, "Π{x}:")?;
                        a.fmt_prec(f, 1)?;
                        write!(f, ". ")?;
                        b.fmt_prec(f, 0)
                    })
                }
            }

            Term::Lambda(x, a, body) => parens(f, prec > 0, &|f| {
                write!(f, "λ{x}:")?;
                a.fmt_prec(f, 1)?;
                write!(f, ". ")?;
                body.fmt_prec(f, 0)
            }),

            Term::If(c, t, e) => parens(f, prec > 0, &|f| {
                write!(f, "if ")?;
                c.fmt_prec(f, 0)?;
                write!(f, " then ")?;
                t.fmt_prec(f, 0)?;
                write!(f, " else ")?;
                e.fmt_prec(f, 0)
            }),

            Term::Let(x, e1, e2) => parens(f, prec > 0, &|f| {
                write!(f, "let {x} = ")?;
                e1.fmt_prec(f, 0)?;
                write!(f, " in ")?;
                e2.fmt_prec(f, 0)
            }),

            Term::BinOp(op, a, b) => {
                let (op_prec, lp, rp) = match op {
                    BinOp::Eq | BinOp::Lt => (2, 3, 3),
                    BinOp::Add | BinOp::Sub => (3, 3, 4),
                    BinOp::Mul => (4, 4, 5),
                };
                parens(f, prec > op_prec, &|f| {
                    a.fmt_prec(f, lp)?;
                    write!(f, " {} ", op.symbol())?;
                    b.fmt_prec(f, rp)
                })
            }

            Term::App(g, a) => parens(f, prec > 5, &|f| {
                g.fmt_prec(f, 5)?;
                write!(f, " ")?;
                a.fmt_prec(f, 6)
            }),
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_prec(f, 0)
    }
}
