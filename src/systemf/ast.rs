use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Var(String),
    Bool,
    Int,
    Arrow(Box<Type>, Box<Type>),
    ForAll(String, Box<Type>),
}

impl Type {
    pub fn var(s: impl Into<String>) -> Type {
        Type::Var(s.into())
    }
    pub fn arrow(from: Type, to: Type) -> Type {
        Type::Arrow(Box::new(from), Box::new(to))
    }
    pub fn forall(name: impl Into<String>, body: Type) -> Type {
        Type::ForAll(name.into(), Box::new(body))
    }

    // Precedence:
    //   0  top
    //   1  inside arrow (left side) / forall body
    //   2  atom
    fn fmt_prec(&self, f: &mut fmt::Formatter<'_>, prec: u8) -> fmt::Result {
        match self {
            Type::Bool => write!(f, "Bool"),
            Type::Int => write!(f, "Int"),
            Type::Var(x) => write!(f, "{}", x),
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
            Type::ForAll(_, _) => {
                let needs = prec > 0;
                if needs {
                    write!(f, "(")?;
                }
                let mut names: Vec<&str> = Vec::new();
                let mut cur = self;
                while let Type::ForAll(n, body) = cur {
                    names.push(n.as_str());
                    cur = body.as_ref();
                }
                write!(f, "∀{}. ", names.join(" "))?;
                cur.fmt_prec(f, 0)?;
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
    Abs(String, Type, Box<Term>), // \x: T. body
    App(Box<Term>, Box<Term>),

    TyAbs(String, Box<Term>), // ΛT. body
    TyApp(Box<Term>, Type),   // e [T]

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
    pub fn ty_abs(x: impl Into<String>, body: Term) -> Term {
        Term::TyAbs(x.into(), Box::new(body))
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
            Term::Var(x) => write!(f, "{}", x),
            Term::BoolLit(b) => write!(f, "{}", b),
            Term::IntLit(n) => write!(f, "{}", n),

            Term::Abs(_, _, _) => parens(f, prec > 0, &|f| {
                let mut cur = self;
                let mut first = true;
                write!(f, "λ")?;
                while let Term::Abs(x, ty, body) = cur {
                    if !first {
                        write!(f, " ")?;
                    }
                    write!(f, "{}:{}", x, ty)?;
                    first = false;
                    cur = body.as_ref();
                }
                write!(f, ". ")?;
                cur.fmt_prec(f, 0)
            }),

            Term::TyAbs(_, _) => parens(f, prec > 0, &|f| {
                let mut cur = self;
                let mut names: Vec<&str> = Vec::new();
                while let Term::TyAbs(n, body) = cur {
                    names.push(n.as_str());
                    cur = body.as_ref();
                }
                write!(f, "Λ{}. ", names.join(" "))?;
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
                write!(f, "let {} = ", x)?;
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
                write!(f, " [{}]", ty)
            }),
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_prec(f, 0)
    }
}
