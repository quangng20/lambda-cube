use std::fmt;

// Kinds: the "types of types". * classifies proper types (Int, Bool, T -> U).
// * -> * classifies one-argument type operators (the kind of List, Maybe, …
// in languages that have HKTs). * -> * -> * classifies two-arg ops (Pair).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Kind {
    Star,
    Arrow(Box<Kind>, Box<Kind>),
}

impl Kind {
    pub fn arrow(a: Kind, b: Kind) -> Kind {
        Kind::Arrow(Box::new(a), Box::new(b))
    }

    fn fmt_prec(&self, f: &mut fmt::Formatter<'_>, prec: u8) -> fmt::Result {
        match self {
            Kind::Star => write!(f, "*"),
            Kind::Arrow(a, b) => {
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

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_prec(f, 0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Var(String),
    Bool,
    Int,
    Arrow(Box<Type>, Box<Type>),
    ForAll(String, Kind, Box<Type>),
    Abs(String, Kind, Box<Type>),
    App(Box<Type>, Box<Type>),
}

impl Type {
    pub fn var(s: impl Into<String>) -> Type {
        Type::Var(s.into())
    }
    pub fn arrow(from: Type, to: Type) -> Type {
        Type::Arrow(Box::new(from), Box::new(to))
    }
    pub fn forall(name: impl Into<String>, kind: Kind, body: Type) -> Type {
        Type::ForAll(name.into(), kind, Box::new(body))
    }
    pub fn abs(name: impl Into<String>, kind: Kind, body: Type) -> Type {
        Type::Abs(name.into(), kind, Box::new(body))
    }
    pub fn app(f: Type, a: Type) -> Type {
        Type::App(Box::new(f), Box::new(a))
    }

    // Precedence levels:
    //   0  top (forall, type-level abs)
    //   1  arrow
    //   2  type-level application
    //   3  atom
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
            Type::Var(x) => write!(f, "{x}"),
            Type::Int => write!(f, "Int"),
            Type::Bool => write!(f, "Bool"),
            Type::Arrow(a, b) => parens(f, prec > 1, &|f| {
                a.fmt_prec(f, 2)?;
                write!(f, " -> ")?;
                b.fmt_prec(f, 1)
            }),
            Type::ForAll(_, _, _) => parens(f, prec > 0, &|f| {
                let mut cur = self;
                write!(f, "∀")?;
                let mut first = true;
                while let Type::ForAll(x, k, body) = cur {
                    if !first {
                        write!(f, " ")?;
                    }
                    write_binding(f, x, k)?;
                    first = false;
                    cur = body.as_ref();
                }
                write!(f, ". ")?;
                cur.fmt_prec(f, 0)
            }),
            Type::Abs(_, _, _) => parens(f, prec > 0, &|f| {
                let mut cur = self;
                write!(f, "λ")?;
                let mut first = true;
                while let Type::Abs(x, k, body) = cur {
                    if !first {
                        write!(f, " ")?;
                    }
                    write_binding(f, x, k)?;
                    first = false;
                    cur = body.as_ref();
                }
                write!(f, ". ")?;
                cur.fmt_prec(f, 0)
            }),
            Type::App(g, a) => parens(f, prec > 2, &|f| {
                g.fmt_prec(f, 2)?;
                write!(f, " ")?;
                a.fmt_prec(f, 3)
            }),
        }
    }
}

fn write_binding(f: &mut fmt::Formatter<'_>, x: &str, k: &Kind) -> fmt::Result {
    if matches!(k, Kind::Star) {
        write!(f, "{x}")
    } else {
        write!(f, "{x}::{k}")
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_prec(f, 0)
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
    Abs(String, Type, Box<Term>),
    App(Box<Term>, Box<Term>),

    TyAbs(String, Kind, Box<Term>),
    TyApp(Box<Term>, Type),

    BoolLit(bool),
    IntLit(i64),
    If(Box<Term>, Box<Term>, Box<Term>),
    BinOp(BinOp, Box<Term>, Box<Term>),
    Let(String, Box<Term>, Box<Term>),
}

impl Term {
    pub fn var(s: impl Into<String>) -> Term {
        Term::Var(s.into())
    }
    pub fn abs(x: impl Into<String>, ty: Type, body: Term) -> Term {
        Term::Abs(x.into(), ty, Box::new(body))
    }
    pub fn app(f: Term, a: Term) -> Term {
        Term::App(Box::new(f), Box::new(a))
    }
    pub fn ty_abs(x: impl Into<String>, kind: Kind, body: Term) -> Term {
        Term::TyAbs(x.into(), kind, Box::new(body))
    }
    pub fn ty_app(f: Term, ty: Type) -> Term {
        Term::TyApp(Box::new(f), ty)
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

            Term::Abs(_, _, _) => parens(f, prec > 0, &|f| {
                let mut cur = self;
                let mut first = true;
                write!(f, "λ")?;
                while let Term::Abs(x, ty, body) = cur {
                    if !first {
                        write!(f, " ")?;
                    }
                    write!(f, "{x}:{ty}")?;
                    first = false;
                    cur = body.as_ref();
                }
                write!(f, ". ")?;
                cur.fmt_prec(f, 0)
            }),

            Term::TyAbs(_, _, _) => parens(f, prec > 0, &|f| {
                let mut cur = self;
                let mut first = true;
                write!(f, "Λ")?;
                while let Term::TyAbs(x, k, body) = cur {
                    if !first {
                        write!(f, " ")?;
                    }
                    write_binding(f, x, k)?;
                    first = false;
                    cur = body.as_ref();
                }
                write!(f, ". ")?;
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

            Term::TyApp(g, ty) => parens(f, prec > 4, &|f| {
                g.fmt_prec(f, 4)?;
                write!(f, " [{ty}]")
            }),
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_prec(f, 0)
    }
}
