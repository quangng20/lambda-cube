use crate::hm::ast::{BinOp, Term};

#[derive(Debug, Clone, PartialEq, Eq)]
enum Tok {
    Lambda,
    Dot,
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
    Rec,
    In,
    True,
    False,
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
            '\\' | 'λ' => {
                chars.next();
                tokens.push(Tok::Lambda);
            }
            '.' => {
                chars.next();
                tokens.push(Tok::Dot);
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
            '-' => {
                chars.next();
                tokens.push(Tok::Minus);
            }
            '*' => {
                chars.next();
                tokens.push(Tok::Star);
            }
            '<' => {
                chars.next();
                tokens.push(Tok::Lt);
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
                    "rec" => Tok::Rec,
                    "in" => Tok::In,
                    "true" => Tok::True,
                    "false" => Tok::False,
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
            _ => self.parse_cmp(),
        }
    }

    fn parse_let(&mut self) -> Result<Term, String> {
        self.advance(); // let
        let is_rec = matches!(self.peek(), Some(Tok::Rec));
        if is_rec {
            self.advance();
        }
        let name = match self.advance() {
            Some(Tok::Ident(s)) => s,
            other => return Err(format!("expected identifier after 'let', got {other:?}")),
        };
        self.expect(&Tok::Eq, "after let-bound name")?;
        let e1 = self.parse_expr()?;
        self.expect(&Tok::In, "after let binding")?;
        let e2 = self.parse_expr()?;
        if is_rec {
            Ok(Term::let_rec(name, e1, e2))
        } else {
            Ok(Term::let_(name, e1, e2))
        }
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
        self.advance(); // \
        let mut params: Vec<String> = Vec::new();
        loop {
            let name = match self.advance() {
                Some(Tok::Ident(s)) => s,
                other => return Err(format!("expected parameter name, got {other:?}")),
            };
            params.push(name);
            if let Some(Tok::Dot) = self.peek() {
                break;
            }
        }
        self.expect(&Tok::Dot, "after parameter list")?;
        let body = self.parse_expr()?;
        Ok(params
            .into_iter()
            .rev()
            .fold(body, |acc, p| Term::abs(p, acc)))
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
    fn parse_identity_no_annotation() {
        let t = parse("\\x. x").unwrap();
        assert_eq!(t, Term::abs("x", Term::var("x")));
    }

    #[test]
    fn parse_let_rec() {
        let t = parse("let rec f = \\n. f n in f 5").unwrap();
        assert_eq!(
            t,
            Term::let_rec(
                "f",
                Term::abs("n", Term::app(Term::var("f"), Term::var("n"))),
                Term::app(Term::var("f"), Term::IntLit(5)),
            )
        );
    }

    #[test]
    fn parse_arith() {
        let t = parse("1 + 2 * 3").unwrap();
        assert_eq!(
            t,
            Term::binop(
                BinOp::Add,
                Term::IntLit(1),
                Term::binop(BinOp::Mul, Term::IntLit(2), Term::IntLit(3))
            )
        );
    }
}
