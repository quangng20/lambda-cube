use std::io::{self, BufRead, Write};

use crate::systemf::{ast::Term, eval, parser, typeck};

const MAX_STEPS: usize = 10_000;
const TRACE_MAX: usize = 100;

pub fn run() {
    println!("System F  (λ2 — polymorphic lambda calculus)");
    println!("type :help for syntax, :quit to exit");
    println!();

    let stdin = io::stdin();
    let mut stdout = io::stdout();
    let mut handle = stdin.lock();
    let mut line = String::new();

    loop {
        print!("λ2> ");
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
    println!("syntax (System F = STLC + polymorphism):");
    println!("  term abstraction:  \\x:T. body          or  λx:T. body");
    println!("  type abstraction:  /\\T. body           or  ΛT. body");
    println!("  term application:  f x                   (left-associative)");
    println!("  type application:  f [T]                 (specialize a polymorphic term)");
    println!("  values:            42, true, false");
    println!("  arithmetic:        a + b, a - b, a * b, a == b, a < b");
    println!("  conditional:       if c then t else e");
    println!("  binding:           let x = e1 in e2");
    println!();
    println!("types:");
    println!("  Int, Bool, T -> U, ∀T. τ  (or  forall T. τ)");
    println!();
    println!("examples:");
    println!("  /\\T. \\x:T. x                                -- polymorphic identity");
    println!("  (/\\T. \\x:T. x) [Int] 5                     -- specialize and apply");
    println!("  /\\T. /\\U. \\x:T. \\y:U. x                  -- K combinator");
    println!("  let id = /\\T. \\x:T. x in id [Int] 7      -- bind a polymorphic value");
    println!();
    println!("commands:");
    println!("  :t     <expr>  :type  <expr>  show type without evaluating");
    println!("  :trace <expr>  :tr    <expr>  show each evaluation step");
    println!("  :help          :h             this help");
    println!("  :quit          :q             exit");
}
