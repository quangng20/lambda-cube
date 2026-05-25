use crate::fomega::ast::{BinOp, Kind, Term, Type};

#[derive(Debug, Clone, PartialEq, Eq)]
enum Tok {
    Lambda,
    BigLambda,
    Dot,
    Colon,
    ColonColon,
    Arrow,
    LParen,
    RParen,
    LBracket,
    RBracket,
    Eq,
    EqEq,
    Lt,
    Plus,
    Minus,
    Star,
    If,
    Then,
    Else,
    Let,
    In,
    True,
    False,
    BoolKw,
    IntKw,
    ForAll,
    Ident(String),
    IntLit(i64),
}

fn tokenize(input: &str) -> Result<Vec<Tok>, String> {
    let mut tokens = Vec::new();
    let mut chars = input.chars().peekable();
    while let Some(&c) = chars.peek() {
        match c {
            ' ' | '\t' | '\n' | '\r' => {
                chars.next();
            }
            'λ' => {
                chars.next();
                tokens.push(Tok::Lambda);
            }
            'Λ' => {
                chars.next();
                tokens.push(Tok::BigLambda);
            }
            '∀' => {
                chars.next();
                tokens.push(Tok::ForAll);
            }
            '\\' => {
                chars.next();
                tokens.push(Tok::Lambda);
            }
            '/' => {
                chars.next();
                if chars.peek() == Some(&'\\') {
                    chars.next();
                    tokens.push(Tok::BigLambda);
                } else {
                    return Err("expected '/\\' for type abstraction".into());
                }
            }
            '.' => {
                chars.next();
                tokens.push(Tok::Dot);
            }
            ':' => {
                chars.next();
                if chars.peek() == Some(&':') {
                    chars.next();
                    tokens.push(Tok::ColonColon);
                } else {
                    tokens.push(Tok::Colon);
                }
            }
            '(' => {
                chars.next();
                tokens.push(Tok::LParen);
            }
            ')' => {
                chars.next();
                tokens.push(Tok::RParen);
            }
            '[' => {
                chars.next();
                tokens.push(Tok::LBracket);
            }
            ']' => {
                chars.next();
                tokens.push(Tok::RBracket);
            }
            '+' => {
                chars.next();
                tokens.push(Tok::Plus);
            }
            '*' => {
                chars.next();
                tokens.push(Tok::Star);
            }
            '<' => {
                chars.next();
                tokens.push(Tok::Lt);
            }
            '-' => {
                chars.next();
                if chars.peek() == Some(&'>') {
                    chars.next();
                    tokens.push(Tok::Arrow);
                } else {
                    tokens.push(Tok::Minus);
                }
            }
            '=' => {
                chars.next();
                if chars.peek() == Some(&'=') {
                    chars.next();
                    tokens.push(Tok::EqEq);
                } else {
                    tokens.push(Tok::Eq);
                }
            }
            c if c.is_ascii_digit() => {
                let mut n: i64 = 0;
                while let Some(&c) = chars.peek() {
                    if let Some(d) = c.to_digit(10) {
                        n = n
                            .checked_mul(10)
                            .and_then(|x| x.checked_add(i64::from(d)))
                            .ok_or_else(|| "integer literal overflow".to_string())?;
                        chars.next();
                    } else {
                        break;
                    }
                }
                tokens.push(Tok::IntLit(n));
            }
            c if c.is_alphabetic() || c == '_' => {
                let mut s = String::new();
                while let Some(&c) = chars.peek() {
                    if c.is_alphanumeric() || c == '_' || c == '\'' {
                        s.push(c);
                        chars.next();
                    } else {
                        break;
                    }
                }
                let tok = match s.as_str() {
                    "if" => Tok::If,
                    "then" => Tok::Then,
                    "else" => Tok::Else,
                    "let" => Tok::Let,
                    "in" => Tok::In,
                    "true" => Tok::True,
                    "false" => Tok::False,
                    "Bool" => Tok::BoolKw,
                    "Int" => Tok::IntKw,
                    "forall" => Tok::ForAll,
                    _ => Tok::Ident(s),
                };
                tokens.push(tok);
            }
            _ => return Err(format!("unexpected character: {c:?}")),
        }
    }
    Ok(tokens)
}

struct Parser {
    tokens: Vec<Tok>,
    pos: usize,
}

impl Parser {
    fn peek(&self) -> Option<&Tok> {
        self.tokens.get(self.pos)
    }
    fn advance(&mut self) -> Option<Tok> {
        let t = self.tokens.get(self.pos).cloned();
        if t.is_some() {
            self.pos += 1;
        }
        t
    }
    fn expect(&mut self, want: &Tok, ctx: &str) -> Result<(), String> {
        match self.advance() {
            Some(t) if &t == want => Ok(()),
            other => Err(format!("expected {want:?} {ctx}, got {other:?}")),
        }
    }

    // ----- KINDS -----
    // K  := atom ("->" K)?    (right-associative)
    fn parse_kind(&mut self) -> Result<Kind, String> {
        let left = self.parse_kind_atom()?;
        if let Some(Tok::Arrow) = self.peek() {
            self.advance();
            let right = self.parse_kind()?;
            Ok(Kind::arrow(left, right))
        } else {
            Ok(left)
        }
    }

    fn parse_kind_atom(&mut self) -> Result<Kind, String> {
        match self.advance() {
            Some(Tok::Star) => Ok(Kind::Star),
            Some(Tok::LParen) => {
                let k = self.parse_kind()?;
                self.expect(&Tok::RParen, "after kind")?;
                Ok(k)
            }
            other => Err(format!("expected kind, got {other:?}")),
        }
    }

    // ----- TYPES -----
    fn parse_type(&mut self) -> Result<Type, String> {
        match self.peek() {
            Some(Tok::ForAll) => self.parse_forall_type(),
            Some(Tok::Lambda) => self.parse_type_abs(),
            _ => self.parse_type_arrow(),
        }
    }

    fn parse_forall_type(&mut self) -> Result<Type, String> {
        self.advance(); // forall
        let bindings = self.parse_kinded_bindings()?;
        self.expect(&Tok::Dot, "after forall binders")?;
        let body = self.parse_type()?;
        Ok(bindings
            .into_iter()
            .rev()
            .fold(body, |acc, (name, k)| Type::forall(name, k, acc)))
    }

    fn parse_type_abs(&mut self) -> Result<Type, String> {
        self.advance(); // \
        let bindings = self.parse_kinded_bindings()?;
        self.expect(&Tok::Dot, "after type-level lambda binders")?;
        let body = self.parse_type()?;
        Ok(bindings
            .into_iter()
            .rev()
            .fold(body, |acc, (name, k)| Type::abs(name, k, acc)))
    }

    // Parse a sequence of "X" or "X::K" bindings, stopping at '.'.
    fn parse_kinded_bindings(&mut self) -> Result<Vec<(String, Kind)>, String> {
        let mut result = Vec::new();
        while let Some(Tok::Ident(_)) = self.peek() {
            let name = match self.advance() {
                Some(Tok::Ident(s)) => s,
                _ => unreachable!(),
            };
            let kind = if let Some(Tok::ColonColon) = self.peek() {
                self.advance();
                self.parse_kind()?
            } else {
                Kind::Star
            };
            result.push((name, kind));
        }
        if result.is_empty() {
            return Err("expected at least one binder".into());
        }
        Ok(result)
    }

    fn parse_type_arrow(&mut self) -> Result<Type, String> {
        let left = self.parse_type_app()?;
        if let Some(Tok::Arrow) = self.peek() {
            self.advance();
            let right = self.parse_type()?;
            Ok(Type::arrow(left, right))
        } else {
            Ok(left)
        }
    }

    fn parse_type_app(&mut self) -> Result<Type, String> {
        let mut left = self.parse_type_atom()?;
        while matches!(
            self.peek(),
            Some(Tok::Ident(_)) | Some(Tok::LParen) | Some(Tok::BoolKw) | Some(Tok::IntKw)
        ) {
            let right = self.parse_type_atom()?;
            left = Type::app(left, right);
        }
        Ok(left)
    }

    fn parse_type_atom(&mut self) -> Result<Type, String> {
        match self.advance() {
            Some(Tok::BoolKw) => Ok(Type::Bool),
            Some(Tok::IntKw) => Ok(Type::Int),
            Some(Tok::Ident(s)) => Ok(Type::var(s)),
            Some(Tok::LParen) => {
                let t = self.parse_type()?;
                self.expect(&Tok::RParen, "after type")?;
                Ok(t)
            }
            other => Err(format!("expected type, got {other:?}")),
        }
    }

    // ----- TERMS -----
    fn parse_expr(&mut self) -> Result<Term, String> {
        match self.peek() {
            Some(Tok::Let) => self.parse_let(),
            Some(Tok::If) => self.parse_if(),
            Some(Tok::Lambda) => self.parse_lambda(),
            Some(Tok::BigLambda) => self.parse_ty_lambda(),
            _ => self.parse_cmp(),
        }
    }

    fn parse_let(&mut self) -> Result<Term, String> {
        self.advance();
        let name = match self.advance() {
            Some(Tok::Ident(s)) => s,
            other => return Err(format!("expected identifier after 'let', got {other:?}")),
        };
        self.expect(&Tok::Eq, "after let-bound name")?;
        let e1 = self.parse_expr()?;
        self.expect(&Tok::In, "after let binding")?;
        let e2 = self.parse_expr()?;
        Ok(Term::let_(name, e1, e2))
    }

    fn parse_if(&mut self) -> Result<Term, String> {
        self.advance();
        let c = self.parse_expr()?;
        self.expect(&Tok::Then, "after if condition")?;
        let t = self.parse_expr()?;
        self.expect(&Tok::Else, "after then-branch")?;
        let e = self.parse_expr()?;
        Ok(Term::if_then_else(c, t, e))
    }

    fn parse_lambda(&mut self) -> Result<Term, String> {
        self.advance();
        let mut bindings: Vec<(String, Type)> = Vec::new();
        loop {
            let name = match self.advance() {
                Some(Tok::Ident(s)) => s,
                other => return Err(format!("expected parameter name, got {other:?}")),
            };
            self.expect(&Tok::Colon, "after parameter name")?;
            let ty = self.parse_type()?;
            bindings.push((name, ty));
            if let Some(Tok::Dot) = self.peek() {
                break;
            }
        }
        self.expect(&Tok::Dot, "after parameter list")?;
        let body = self.parse_expr()?;
        Ok(bindings
            .into_iter()
            .rev()
            .fold(body, |acc, (x, t)| Term::abs(x, t, acc)))
    }

    fn parse_ty_lambda(&mut self) -> Result<Term, String> {
        self.advance(); // /\
        let bindings = self.parse_kinded_bindings()?;
        self.expect(&Tok::Dot, "after type-variable list")?;
        let body = self.parse_expr()?;
        Ok(bindings
            .into_iter()
            .rev()
            .fold(body, |acc, (n, k)| Term::ty_abs(n, k, acc)))
    }

    fn parse_cmp(&mut self) -> Result<Term, String> {
        let left = self.parse_add()?;
        let op = match self.peek() {
            Some(Tok::EqEq) => Some(BinOp::Eq),
            Some(Tok::Lt) => Some(BinOp::Lt),
            _ => None,
        };
        if let Some(op) = op {
            self.advance();
            let right = self.parse_add()?;
            Ok(Term::binop(op, left, right))
        } else {
            Ok(left)
        }
    }

    fn parse_add(&mut self) -> Result<Term, String> {
        let mut left = self.parse_mul()?;
        loop {
            let op = match self.peek() {
                Some(Tok::Plus) => BinOp::Add,
                Some(Tok::Minus) => BinOp::Sub,
                _ => break,
            };
            self.advance();
            let right = self.parse_mul()?;
            left = Term::binop(op, left, right);
        }
        Ok(left)
    }

    fn parse_mul(&mut self) -> Result<Term, String> {
        let mut left = self.parse_app()?;
        while let Some(Tok::Star) = self.peek() {
            self.advance();
            let right = self.parse_app()?;
            left = Term::binop(BinOp::Mul, left, right);
        }
        Ok(left)
    }

    fn parse_app(&mut self) -> Result<Term, String> {
        let mut left = self.parse_atom()?;
        loop {
            match self.peek() {
                Some(Tok::LBracket) => {
                    self.advance();
                    let ty = self.parse_type()?;
                    self.expect(&Tok::RBracket, "after type argument")?;
                    left = Term::ty_app(left, ty);
                }
                Some(Tok::Ident(_)) | Some(Tok::LParen) | Some(Tok::True) | Some(Tok::False)
                | Some(Tok::IntLit(_)) => {
                    let right = self.parse_atom()?;
                    left = Term::app(left, right);
                }
                _ => break,
            }
        }
        Ok(left)
    }

    fn parse_atom(&mut self) -> Result<Term, String> {
        match self.advance() {
            Some(Tok::Ident(s)) => Ok(Term::var(s)),
            Some(Tok::True) => Ok(Term::BoolLit(true)),
            Some(Tok::False) => Ok(Term::BoolLit(false)),
            Some(Tok::IntLit(n)) => Ok(Term::IntLit(n)),
            Some(Tok::LParen) => {
                let e = self.parse_expr()?;
                self.expect(&Tok::RParen, "after expression")?;
                Ok(e)
            }
            other => Err(format!("unexpected token: {other:?}")),
        }
    }
}

pub fn parse(input: &str) -> Result<Term, String> {
    let tokens = tokenize(input)?;
    let mut p = Parser { tokens, pos: 0 };
    let t = p.parse_expr()?;
    if p.pos < p.tokens.len() {
        return Err(format!(
            "unexpected token after expression: {:?}",
            p.tokens.get(p.pos)
        ));
    }
    Ok(t)
}

pub fn parse_type_str(input: &str) -> Result<Type, String> {
    let tokens = tokenize(input)?;
    let mut p = Parser { tokens, pos: 0 };
    let t = p.parse_type()?;
    if p.pos < p.tokens.len() {
        return Err(format!(
            "unexpected token after type: {:?}",
            p.tokens.get(p.pos)
        ));
    }
    Ok(t)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_identity_type_operator() {
        // \T::*. T   — should parse as type-level lambda
        let t = parse_type_str("\\T::*. T").unwrap();
        assert_eq!(t, Type::abs("T", Kind::Star, Type::var("T")));
    }

    #[test]
    fn parse_higher_kinded_forall() {
        // forall F::* -> *. F Int
        let t = parse_type_str("forall F::* -> *. F Int").unwrap();
        assert_eq!(
            t,
            Type::forall(
                "F",
                Kind::arrow(Kind::Star, Kind::Star),
                Type::app(Type::var("F"), Type::Int)
            )
        );
    }

    #[test]
    fn parse_kinded_type_abstraction_in_term() {
        // /\F::* -> *. \x:F Int. x
        let t = parse("/\\F::* -> *. \\x:F Int. x").unwrap();
        let expected = Term::ty_abs(
            "F",
            Kind::arrow(Kind::Star, Kind::Star),
            Term::abs("x", Type::app(Type::var("F"), Type::Int), Term::var("x")),
        );
        assert_eq!(t, expected);
    }
}
