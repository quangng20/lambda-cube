use std::io::{self, BufRead, Write};

use crate::fomega::{ast::Term, eval, parser, typeck};

const MAX_STEPS: usize = 10_000;
const TRACE_MAX: usize = 100;

pub fn run() {
    println!("System Fω  (λω — polymorphism + type operators)");
    println!("type :help for syntax, :quit to exit");
    println!();

    let stdin = io::stdin();
    let mut stdout = io::stdout();
    let mut handle = stdin.lock();
    let mut line = String::new();

    loop {
        print!("λω> ");
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
        if matches!(input, ":quit" | ":q") {
            break;
        }
        if matches!(input, ":help" | ":h") {
            print_help();
            continue;
        }

        if let Some(rest) = input
            .strip_prefix(":t ")
            .or_else(|| input.strip_prefix(":type "))
        {
            match parser::parse(rest) {
                Ok(term) => match typeck::type_of(&term) {
                    Ok(ty) => println!("{term} : {ty}"),
                    Err(e) => eprintln!("type error: {e}"),
                },
                Err(e) => eprintln!("parse error: {e}"),
            }
            continue;
        }

        if let Some(rest) = input
            .strip_prefix(":k ")
            .or_else(|| input.strip_prefix(":kind "))
        {
            match parser::parse_type_str(rest) {
                Ok(ty) => match typeck::kind_of_type(&ty) {
                    Ok(k) => println!("{ty} :: {k}"),
                    Err(e) => eprintln!("kind error: {e}"),
                },
                Err(e) => eprintln!("parse error: {e}"),
            }
            continue;
        }

        if let Some(rest) = input
            .strip_prefix(":trace ")
            .or_else(|| input.strip_prefix(":tr "))
        {
            match parser::parse(rest) {
                Ok(term) => match typeck::type_of(&term) {
                    Ok(ty) => trace(term, &ty.to_string()),
                    Err(e) => eprintln!("type error: {e}"),
                },
                Err(e) => eprintln!("parse error: {e}"),
            }
            continue;
        }

        match parser::parse(input) {
            Ok(term) => match typeck::type_of(&term) {
                Ok(ty) => {
                    let result = eval::eval(term, MAX_STEPS);
                    println!("{} : {ty}", result.term);
                    if result.steps > 0 {
                        eprintln!(
                            "({} step{})",
                            result.steps,
                            if result.steps == 1 { "" } else { "s" }
                        );
                    }
                }
                Err(e) => eprintln!("type error: {e}"),
            },
            Err(e) => eprintln!("parse error: {e}"),
        }
    }
}

fn trace(mut t: Term, ty_str: &str) {
    println!("   {t} : {ty_str}");
    let mut count = 0;
    while let Some(next) = eval::step(&t) {
        t = next;
        count += 1;
        println!(" → {t}");
        if count >= TRACE_MAX {
            eprintln!("(reached {TRACE_MAX}-step trace limit)");
            return;
        }
    }
    eprintln!("({count} step{})", if count == 1 { "" } else { "s" });
}

fn print_help() {
    println!("syntax (Fω = System F + type operators):");
    println!("  term abstraction:     \\x:T. body");
    println!("  term application:     f x");
    println!("  type abstraction:     /\\T::κ. body    (or  ΛT::κ. body  — κ defaults to *)");
    println!("  type application:     f [T]");
    println!("  type-level lambda:    \\T::κ. T'        (used inside type expressions)");
    println!();
    println!("kinds:");
    println!("  *               proper type");
    println!("  * -> *          one-arg type operator (Rust lacks this)");
    println!("  * -> * -> *     two-arg type operator");
    println!();
    println!("types:");
    println!("  Int, Bool, T -> U,  ∀T::κ. τ,  λT::κ. τ,  F A");
    println!();
    println!("examples:");
    println!("  /\\F::* -> *. \\x:F Int. x          -- function over a type operator");
    println!("  (/\\F::* -> *. \\x:F Int. x) [\\T::*. T] 42");
    println!();
    println!("commands:");
    println!("  :t     <expr>  show inferred type");
    println!("  :k     <type>  show inferred kind");
    println!("  :trace <expr>  :tr <expr>  show each evaluation step");
    println!("  :help :h");
    println!("  :quit :q");
}
