use std::io::{self, BufRead, Write};

use crate::untyped::{ast::Term, eval, parser};

const MAX_STEPS: usize = 10_000;
const TRACE_MAX: usize = 100;

pub fn run() {
    println!("untyped lambda calculus  (λ)");
    println!("type :help for syntax, :quit to exit");
    println!();

    let stdin = io::stdin();
    let mut stdout = io::stdout();
    let mut handle = stdin.lock();
    let mut line = String::new();

    loop {
        print!("λ> ");
        stdout.flush().ok();

        line.clear();
        match handle.read_line(&mut line) {
            Ok(0) => {
                println!();
                break;
            }
            Ok(_) => {}
            Err(e) => {
                eprintln!("read error: {e}");
                break;
            }
        }
        let input = line.trim();
        if input.is_empty() {
            continue;
        }

        match input {
            ":quit" | ":q" => break,
            ":help" | ":h" => {
                print_help();
                continue;
            }
            _ => {}
        }

        if let Some(rest) = input
            .strip_prefix(":trace ")
            .or_else(|| input.strip_prefix(":tr "))
        {
            match parser::parse(rest) {
                Ok(term) => trace(term),
                Err(e) => eprintln!("parse error: {e}"),
            }
            continue;
        }

        match parser::parse(input) {
            Ok(term) => {
                let result = eval::normalize(term, MAX_STEPS);
                println!("{}", result.term);
                if !result.reached_normal_form {
                    eprintln!(
                        "(stopped after {} steps — term may have no normal form)",
                        result.steps
                    );
                } else if result.steps > 0 {
                    eprintln!(
                        "({} reduction{})",
                        result.steps,
                        if result.steps == 1 { "" } else { "s" }
                    );
                }
            }
            Err(e) => eprintln!("parse error: {e}"),
        }
    }
}

fn trace(mut t: Term) {
    println!("   {t}");
    let mut count = 0;
    while let Some(next) = eval::reduce_step(&t) {
        t = next;
        count += 1;
        println!(" → {t}");
        if count >= TRACE_MAX {
            eprintln!("(reached {TRACE_MAX}-step trace limit)");
            return;
        }
    }
    eprintln!(
        "({count} reduction{})",
        if count == 1 { "" } else { "s" }
    );
}

fn print_help() {
    println!("syntax:");
    println!("  variables:    x, y, foo, _bar, x'");
    println!("  abstraction:  \\x. body     or   λx. body");
    println!("                \\x y z. body   (sugar for \\x. \\y. \\z. body)");
    println!("  application:  f x y         (left-associative)");
    println!("  grouping:     (...)");
    println!();
    println!("evaluation: normal-order beta-reduction to normal form");
    println!("            (capture-avoiding substitution with alpha-renaming)");
    println!();
    println!("examples:");
    println!("  (\\x. x) y                                -- identity applied to y");
    println!("  (\\x y. x) a b                            -- K combinator");
    println!("  (\\n f x. f (n f x)) (\\f x. f (f x))      -- successor of Church 2");
    println!();
    println!("commands:");
    println!("  :trace <expr>  :tr <expr>  show each reduction step");
    println!("  :help          :h          this help");
    println!("  :quit          :q          exit");
}
