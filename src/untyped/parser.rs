use crate::untyped::ast::Term;

#[derive(Debug, Clone, PartialEq, Eq)]
enum Tok {
    Lambda,
    Dot,
    LParen,
    RParen,
    Ident(String),
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
                tokens.push(Tok::Ident(s));
            }
            _ => return Err(format!("unexpected character: {:?}", c)),
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

    // expr := lambda | app
    fn parse_expr(&mut self) -> Result<Term, String> {
        if let Some(Tok::Lambda) = self.peek() {
            self.parse_lambda()
        } else {
            self.parse_app()
        }
    }

    // lambda := ('\' | 'λ') IDENT+ '.' expr
    // body extends as far right as possible (it's an expr, which may itself
    // be another lambda or an application).
    fn parse_lambda(&mut self) -> Result<Term, String> {
        self.advance(); // consume the Lambda token
        let mut params: Vec<String> = Vec::new();
        while let Some(Tok::Ident(_)) = self.peek() {
            if let Some(Tok::Ident(name)) = self.advance() {
                params.push(name);
            }
        }
        if params.is_empty() {
            return Err("expected at least one parameter after λ".to_string());
        }
        match self.advance() {
            Some(Tok::Dot) => {}
            other => return Err(format!("expected '.', got {:?}", other)),
        }
        let body = self.parse_expr()?;
        // \x y z. body  ==>  \x. \y. \z. body
        let term = params
            .into_iter()
            .rev()
            .fold(body, |acc, p| Term::abs(p, acc));
        Ok(term)
    }

    // app := atom atom*   (left-associative)
    fn parse_app(&mut self) -> Result<Term, String> {
        let mut left = self.parse_atom()?;
        while matches!(self.peek(), Some(Tok::Ident(_)) | Some(Tok::LParen)) {
            let right = self.parse_atom()?;
            left = Term::app(left, right);
        }
        Ok(left)
    }

    // atom := IDENT | '(' expr ')'
    fn parse_atom(&mut self) -> Result<Term, String> {
        match self.advance() {
            Some(Tok::Ident(name)) => Ok(Term::var(name)),
            Some(Tok::LParen) => {
                let e = self.parse_expr()?;
                match self.advance() {
                    Some(Tok::RParen) => Ok(e),
                    other => Err(format!("expected ')', got {:?}", other)),
                }
            }
            other => Err(format!("unexpected token: {:?}", other)),
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
    fn parse_var() {
        assert_eq!(parse("x").unwrap(), Term::var("x"));
    }

    #[test]
    fn parse_identity() {
        assert_eq!(parse("\\x. x").unwrap(), Term::abs("x", Term::var("x")));
    }

    #[test]
    fn parse_lambda_unicode() {
        assert_eq!(parse("λx. x").unwrap(), Term::abs("x", Term::var("x")));
    }

    #[test]
    fn parse_app_left_assoc() {
        // f x y == (f x) y
        assert_eq!(
            parse("f x y").unwrap(),
            Term::app(Term::app(Term::var("f"), Term::var("x")), Term::var("y"))
        );
    }

    #[test]
    fn parse_multi_arg_lambda() {
        // \x y. x  ==  \x. \y. x
        assert_eq!(
            parse("\\x y. x").unwrap(),
            Term::abs("x", Term::abs("y", Term::var("x")))
        );
    }

    #[test]
    fn parse_lambda_body_extends_right() {
        // \x. f x y == \x. ((f x) y)
        assert_eq!(
            parse("\\x. f x y").unwrap(),
            Term::abs(
                "x",
                Term::app(Term::app(Term::var("f"), Term::var("x")), Term::var("y"))
            )
        );
    }

    #[test]
    fn parse_paren_lambda_as_function() {
        // (\x. x) y
        assert_eq!(
            parse("(\\x. x) y").unwrap(),
            Term::app(Term::abs("x", Term::var("x")), Term::var("y"))
        );
    }
}
