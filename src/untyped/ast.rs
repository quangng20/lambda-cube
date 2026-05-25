use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    Var(String),
    Abs(String, Box<Term>),
    App(Box<Term>, Box<Term>),
}

impl Term {
    pub fn var(name: impl Into<String>) -> Term {
        Term::Var(name.into())
    }
    pub fn abs(name: impl Into<String>, body: Term) -> Term {
        Term::Abs(name.into(), Box::new(body))
    }
    pub fn app(f: Term, a: Term) -> Term {
        Term::App(Box::new(f), Box::new(a))
    }

    fn fmt_prec(&self, f: &mut fmt::Formatter<'_>, prec: u8) -> fmt::Result {
        match self {
            Term::Var(x) => write!(f, "{}", x),
            Term::Abs(_, _) => {
                let needs_parens = prec > 0;
                if needs_parens {
                    write!(f, "(")?;
                }
                let mut params: Vec<&str> = Vec::new();
                let mut current = self;
                while let Term::Abs(p, b) = current {
                    params.push(p.as_str());
                    current = b.as_ref();
                }
                write!(f, "λ{}. ", params.join(" "))?;
                current.fmt_prec(f, 0)?;
                if needs_parens {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Term::App(g, a) => {
                let needs_parens = prec > 1;
                if needs_parens {
                    write!(f, "(")?;
                }
                g.fmt_prec(f, 1)?;
                write!(f, " ")?;
                a.fmt_prec(f, 2)?;
                if needs_parens {
                    write!(f, ")")?;
                }
                Ok(())
            }
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_prec(f, 0)
    }
}
