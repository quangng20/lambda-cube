use std::io::{self, BufRead, Write};

use crate::stlc::{ast::Term, eval, parser, typeck};

const MAX_STEPS: usize = 10_000;
const TRACE_MAX: usize = 100;

pub fn run() {
    println!("Simply Typed Lambda Calculus  (λ→)");
    println!("type :help for syntax, :quit to exit");
    println!();

    let stdin = io::stdin();
    let mut stdout = io::stdout();
    let mut handle = stdin.lock();
    let mut line = String::new();

    loop {
        print!("λ→> ");
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
    println!("syntax:");
    println!("  values:       42, true, false");
    println!("  variables:    x, y, foo");
    println!("  abstraction:  \\x:Int. body     or   λx:Int. body");
    println!("                \\x:Int y:Bool. body   (multi-arg sugar)");
    println!("  application:  f x y               (left-associative)");
    println!("  arithmetic:   a + b, a - b, a * b");
    println!("  comparison:   a == b, a < b   (Int -> Int -> Bool)");
    println!("  conditional:  if c then t else e");
    println!("  binding:      let x = e1 in e2   (x's type inferred from e1)");
    println!();
    println!("types:");
    println!("  Int, Bool, T -> U    (-> is right-associative)");
    println!();
    println!("evaluation: call-by-value to normal form (STLC is strongly normalizing)");
    println!();
    println!("examples:");
    println!("  (\\x:Int. x + 1) 5");
    println!("  if 1 < 2 then 10 else 20");
    println!("  let id = \\x:Int. x in id 42");
    println!("  \\f:Int -> Int. \\x:Int. f (f x)        -- twice");
    println!();
    println!("commands:");
    println!("  :t     <expr>  :type  <expr>  show type without evaluating");
    println!("  :trace <expr>  :tr    <expr>  show each evaluation step");
    println!("  :help          :h             this help");
    println!("  :quit          :q             exit");
}
