use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Bool,
    Int,
    Arrow(Box<Type>, Box<Type>),
}

impl Type {
    pub fn arrow(from: Type, to: Type) -> Type {
        Type::Arrow(Box::new(from), Box::new(to))
    }

    fn fmt_prec(&self, f: &mut fmt::Formatter<'_>, prec: u8) -> fmt::Result {
        match self {
            Type::Bool => write!(f, "Bool"),
            Type::Int => write!(f, "Int"),
            // -> is right-associative; parens only needed if we're on the LEFT of an arrow.
            Type::Arrow(a, b) => {
                let needs_parens = prec > 0;
                if needs_parens {
                    write!(f, "(")?;
                }
                a.fmt_prec(f, 1)?;
                write!(f, " -> ")?;
                b.fmt_prec(f, 0)?;
                if needs_parens {
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
    // \x: T. body
    Abs(String, Type, Box<Term>),
    App(Box<Term>, Box<Term>),

    BoolLit(bool),
    IntLit(i64),
    If(Box<Term>, Box<Term>, Box<Term>),
    BinOp(BinOp, Box<Term>, Box<Term>),

    // let x = e1 in e2  (type of x inferred from e1)
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
        // Precedence levels:
        //   0  top-level / inside parens / lambda/if/let body
        //   1  inside binop comparison (== <)
        //   2  inside +/-
        //   3  inside *
        //   4  function position of application
        //   5  argument position of application / atom
        let with_parens = |f: &mut fmt::Formatter<'_>,
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

            Term::Abs(_, _, _) => with_parens(f, prec > 0, &|f| {
                // collapse \x:T. \y:U. body  ->  \x:T y:U. body  (printed)
                let mut current = self;
                let mut first = true;
                write!(f, "λ")?;
                while let Term::Abs(x, ty, body) = current {
                    if !first {
                        write!(f, " ")?;
                    }
                    write!(f, "{}:{}", x, ty)?;
                    first = false;
                    current = body.as_ref();
                }
                write!(f, ". ")?;
                current.fmt_prec(f, 0)
            }),

            Term::If(c, t, e) => with_parens(f, prec > 0, &|f| {
                write!(f, "if ")?;
                c.fmt_prec(f, 0)?;
                write!(f, " then ")?;
                t.fmt_prec(f, 0)?;
                write!(f, " else ")?;
                e.fmt_prec(f, 0)
            }),

            Term::Let(x, e1, e2) => with_parens(f, prec > 0, &|f| {
                write!(f, "let {} = ", x)?;
                e1.fmt_prec(f, 0)?;
                write!(f, " in ")?;
                e2.fmt_prec(f, 0)
            }),

            Term::BinOp(op, a, b) => {
                let (op_prec, lprec, rprec) = match op {
                    BinOp::Eq | BinOp::Lt => (1, 2, 2),
                    BinOp::Add | BinOp::Sub => (2, 2, 3),
                    BinOp::Mul => (3, 3, 4),
                };
                with_parens(f, prec > op_prec, &|f| {
                    a.fmt_prec(f, lprec)?;
                    write!(f, " {} ", op.symbol())?;
                    b.fmt_prec(f, rprec)
                })
            }

            Term::App(g, a) => with_parens(f, prec > 4, &|f| {
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
