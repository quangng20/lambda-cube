use std::fmt;

// Monotypes (τ). Type variables are unification metavariables introduced
// during inference; the surface syntax has no type annotations at all.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Var(String),
    Int,
    Bool,
    Arrow(Box<Type>, Box<Type>),
}

impl Type {
    #[allow(dead_code)]
    pub fn var(s: impl Into<String>) -> Type {
        Type::Var(s.into())
    }
    pub fn arrow(from: Type, to: Type) -> Type {
        Type::Arrow(Box::new(from), Box::new(to))
    }

    fn fmt_prec(&self, f: &mut fmt::Formatter<'_>, prec: u8) -> fmt::Result {
        match self {
            Type::Var(x) => write!(f, "{x}"),
            Type::Int => write!(f, "Int"),
            Type::Bool => write!(f, "Bool"),
            Type::Arrow(a, b) => {
                let needs = prec > 0;
                if needs {
                    write!(f, "(")?;
                }
                a.fmt_prec(f, 1)?;
                write!(f, " -> ")?;
                b.fmt_prec(f, 0)?;
                if needs {
                    write!(f, ")")?;
                }
                Ok(())
            }
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_prec(f, 0)
    }
}

// A type scheme  ∀α₁ … αₙ. τ. Schemes appear only in the type environment
// (as the type of let-bound names) and at the top level of inference output.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Scheme {
    pub vars: Vec<String>,
    pub ty: Type,
}

impl fmt::Display for Scheme {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.vars.is_empty() {
            write!(f, "{}", self.ty)
        } else {
            write!(f, "∀{}. {}", self.vars.join(" "), self.ty)
        }
    }
}

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
    Abs(String, Box<Term>),
    App(Box<Term>, Box<Term>),

    IntLit(i64),
    BoolLit(bool),
    If(Box<Term>, Box<Term>, Box<Term>),
    BinOp(BinOp, Box<Term>, Box<Term>),
    Let(String, Box<Term>, Box<Term>),
    LetRec(String, Box<Term>, Box<Term>),

    // Internal: never produced by the parser. Used during evaluation to
    // implement `let rec` via the standard `fix` reduction rule.
    Fix(Box<Term>),
}

impl Term {
    pub fn var(s: impl Into<String>) -> Term {
        Term::Var(s.into())
    }
    pub fn abs(x: impl Into<String>, body: Term) -> Term {
        Term::Abs(x.into(), Box::new(body))
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
    pub fn let_rec(x: impl Into<String>, e1: Term, e2: Term) -> Term {
        Term::LetRec(x.into(), Box::new(e1), Box::new(e2))
    }

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
            Term::BoolLit(b) => write!(f, "{b}"),
            Term::IntLit(n) => write!(f, "{n}"),

            Term::Abs(_, _) => parens(f, prec > 0, &|f| {
                let mut cur = self;
                let mut names: Vec<&str> = Vec::new();
                while let Term::Abs(x, body) = cur {
                    names.push(x.as_str());
                    cur = body.as_ref();
                }
                write!(f, "λ{}. ", names.join(" "))?;
                cur.fmt_prec(f, 0)
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

            Term::LetRec(x, e1, e2) => parens(f, prec > 0, &|f| {
                write!(f, "let rec {x} = ")?;
                e1.fmt_prec(f, 0)?;
                write!(f, " in ")?;
                e2.fmt_prec(f, 0)
            }),

            Term::Fix(inner) => parens(f, prec > 4, &|f| {
                write!(f, "fix ")?;
                inner.fmt_prec(f, 5)
            }),

            Term::BinOp(op, a, b) => {
                let (op_prec, lp, rp) = match op {
                    BinOp::Eq | BinOp::Lt => (1, 2, 2),
                    BinOp::Add | BinOp::Sub => (2, 2, 3),
                    BinOp::Mul => (3, 3, 4),
                };
                parens(f, prec > op_prec, &|f| {
                    a.fmt_prec(f, lp)?;
                    write!(f, " {} ", op.symbol())?;
                    b.fmt_prec(f, rp)
                })
            }

            Term::App(g, a) => parens(f, prec > 4, &|f| {
                g.fmt_prec(f, 4)?;
                write!(f, " ")?;
                a.fmt_prec(f, 5)
            }),
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_prec(f, 0)
    }
}
