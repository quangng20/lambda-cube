use std::io::{self, BufRead, Write};

use crate::lambdap::{ast::Term, eval, parser, typeck};

const MAX_STEPS: usize = 10_000;
const TRACE_MAX: usize = 100;

pub fn run() {
    println!("λP (small dependent-types fragment)");
    println!("  note: Type : Type — pedagogically inconsistent on purpose");
    println!("  type :help for syntax, :quit to exit");
    println!();

    let stdin = io::stdin();
    let mut stdout = io::stdout();
    let mut handle = stdin.lock();
    let mut line = String::new();

    loop {
        print!("λP> ");
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
                Ok(term) => match typeck::type_of_top(&term) {
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
                Ok(term) => match typeck::type_of_top(&term) {
                    Ok(ty) => trace(term, &ty.to_string()),
                    Err(e) => eprintln!("type error: {e}"),
                },
                Err(e) => eprintln!("parse error: {e}"),
            }
            continue;
        }

        match parser::parse(input) {
            Ok(term) => match typeck::type_of_top(&term) {
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
    println!("syntax (types and terms share one grammar — that's the point):");
    println!("  values:        42, true, false");
    println!("  type values:   Int, Bool, Type");
    println!("  abstraction:   \\x: A. body         (also λx: A. body)");
    println!("  Π-type:        Pi x: A. B           (also Πx: A. B)");
    println!("  arrow sugar:   A -> B               (Π _ : A. B)");
    println!("  application:   f x                  (left-associative)");
    println!("  arithmetic:    a + b, a - b, a * b, a == b, a < b");
    println!("  conditional:   if c then t else e   (may yield a *dependent* type)");
    println!("  binding:       let x = e1 in e2");
    println!();
    println!("examples:");
    println!("  \\A: Type. \\x: A. x                          -- polymorphic identity");
    println!("  :t \\A: Type. \\x: A. x                       -- ΠA: Type. A -> A");
    println!("  (\\A: Type. \\x: A. x) Int 5                  -- specialize and apply");
    println!("  \\b: Bool. if b then 42 else true             -- dependent function");
    println!("  :t \\b: Bool. if b then 42 else true         -- Πb: Bool. if b then Int else Bool");
    println!();
    println!("commands:");
    println!("  :t     <expr>  show the inferred type (normalized)");
    println!("  :trace <expr>  :tr <expr>  show each evaluation step");
    println!("  :help :h");
    println!("  :quit :q");
}
