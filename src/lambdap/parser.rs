use crate::lambdap::ast::{BinOp, Term};

#[derive(Debug, Clone, PartialEq, Eq)]
enum Tok {
    Lambda,
    Pi,
    TypeKw,
    Dot,
    Colon,
    Arrow,
    LParen,
    RParen,
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
            'λ' | '\\' => {
                chars.next();
                tokens.push(Tok::Lambda);
            }
            'Π' => {
                chars.next();
                tokens.push(Tok::Pi);
            }
            '.' => {
                chars.next();
                tokens.push(Tok::Dot);
            }
            ':' => {
                chars.next();
                tokens.push(Tok::Colon);
            }
            '(' => {
                chars.next();
                tokens.push(Tok::LParen);
            }
            ')' => {
                chars.next();
                tokens.push(Tok::RParen);
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
                    "Pi" => Tok::Pi,
                    "Type" => Tok::TypeKw,
                    "if" => Tok::If,
                    "then" => Tok::Then,
                    "else" => Tok::Else,
                    "let" => Tok::Let,
                    "in" => Tok::In,
                    "true" => Tok::True,
                    "false" => Tok::False,
                    "Bool" => Tok::BoolKw,
                    "Int" => Tok::IntKw,
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

    fn parse_expr(&mut self) -> Result<Term, String> {
        match self.peek() {
            Some(Tok::Let) => self.parse_let(),
            Some(Tok::If) => self.parse_if(),
            Some(Tok::Lambda) => self.parse_lambda(),
            Some(Tok::Pi) => self.parse_pi(),
            _ => self.parse_arrow(),
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

    // λ x : A . body
    fn parse_lambda(&mut self) -> Result<Term, String> {
        self.advance();
        let name = match self.advance() {
            Some(Tok::Ident(s)) => s,
            other => return Err(format!("expected parameter name, got {other:?}")),
        };
        self.expect(&Tok::Colon, "after parameter name")?;
        let a = self.parse_arrow()?; // annotation can be any expr except let/if/lambda/pi unparenthesized
        self.expect(&Tok::Dot, "after parameter annotation")?;
        let body = self.parse_expr()?;
        Ok(Term::lambda(name, a, body))
    }

    // Π x : A . B
    fn parse_pi(&mut self) -> Result<Term, String> {
        self.advance();
        let name = match self.advance() {
            Some(Tok::Ident(s)) => s,
            other => return Err(format!("expected parameter name, got {other:?}")),
        };
        self.expect(&Tok::Colon, "after Pi-parameter name")?;
        let a = self.parse_arrow()?;
        self.expect(&Tok::Dot, "after Pi-parameter annotation")?;
        let body = self.parse_expr()?;
        Ok(Term::pi(name, a, body))
    }

    // A -> B   (sugar for  Π _ : A. B), right-associative
    fn parse_arrow(&mut self) -> Result<Term, String> {
        let left = self.parse_cmp()?;
        if let Some(Tok::Arrow) = self.peek() {
            self.advance();
            let right = self.parse_expr()?; // right side may be Pi, λ, etc.
            Ok(Term::arrow(left, right))
        } else {
            Ok(left)
        }
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
        while matches!(
            self.peek(),
            Some(Tok::Ident(_))
                | Some(Tok::LParen)
                | Some(Tok::True)
                | Some(Tok::False)
                | Some(Tok::IntLit(_))
                | Some(Tok::TypeKw)
                | Some(Tok::BoolKw)
                | Some(Tok::IntKw)
        ) {
            let right = self.parse_atom()?;
            left = Term::app(left, right);
        }
        Ok(left)
    }

    fn parse_atom(&mut self) -> Result<Term, String> {
        match self.advance() {
            Some(Tok::Ident(s)) => Ok(Term::var(s)),
            Some(Tok::True) => Ok(Term::BoolLit(true)),
            Some(Tok::False) => Ok(Term::BoolLit(false)),
            Some(Tok::IntLit(n)) => Ok(Term::IntLit(n)),
            Some(Tok::TypeKw) => Ok(Term::Universe),
            Some(Tok::BoolKw) => Ok(Term::Bool),
            Some(Tok::IntKw) => Ok(Term::Int),
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_polymorphic_id() {
        let t = parse("\\A: Type. \\x: A. x").unwrap();
        assert_eq!(
            t,
            Term::lambda(
                "A",
                Term::Universe,
                Term::lambda("x", Term::var("A"), Term::var("x"))
            )
        );
    }

    #[test]
    fn parse_pi_type() {
        let t = parse("Pi A: Type. A -> A").unwrap();
        assert_eq!(
            t,
            Term::pi(
                "A",
                Term::Universe,
                Term::arrow(Term::var("A"), Term::var("A"))
            )
        );
    }

    #[test]
    fn parse_arrow_desugars_to_pi() {
        // Int -> Bool  parses as  Pi _: Int. Bool
        let t = parse("Int -> Bool").unwrap();
        assert_eq!(t, Term::pi("_", Term::Int, Term::Bool));
    }

    #[test]
    fn parse_dependent_function() {
        // \b: Bool. if b then 42 else true
        let t = parse("\\b: Bool. if b then 42 else true").unwrap();
        assert_eq!(
            t,
            Term::lambda(
                "b",
                Term::Bool,
                Term::if_then_else(Term::var("b"), Term::IntLit(42), Term::BoolLit(true))
            )
        );
    }
}
