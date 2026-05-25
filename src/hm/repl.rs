use std::io::{self, BufRead, Write};

use crate::hm::{ast::Term, eval, infer, parser};

const MAX_STEPS: usize = 100_000;
const TRACE_MAX: usize = 200;

pub fn run() {
    println!("Hindley-Milner (ML-style inference)");
    println!("type :help for syntax, :quit to exit");
    println!();

    let stdin = io::stdin();
    let mut stdout = io::stdout();
    let mut handle = stdin.lock();
    let mut line = String::new();

    loop {
        print!("hm> ");
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
                Ok(term) => match infer::type_of(&term) {
                    Ok(sch) => println!("{term} : {}", infer::prettify(&sch)),
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
                Ok(term) => match infer::type_of(&term) {
                    Ok(sch) => trace(term, &format!("{}", infer::prettify(&sch))),
                    Err(e) => eprintln!("type error: {e}"),
                },
                Err(e) => eprintln!("parse error: {e}"),
            }
            continue;
        }

        match parser::parse(input) {
            Ok(term) => match infer::type_of(&term) {
                Ok(sch) => {
                    let pretty = infer::prettify(&sch);
                    let result = eval::eval(term, MAX_STEPS);
                    println!("{} : {pretty}", result.term);
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
    println!("syntax (ML-style — no type annotations needed):");
    println!("  abstraction:  \\x. body      \\x y z. body");
    println!("  application:  f x y         (left-associative)");
    println!("  arithmetic:   a + b, a - b, a * b, a == b, a < b");
    println!("  conditional:  if c then t else e");
    println!("  binding:      let x = e1 in e2");
    println!("  recursion:    let rec f = \\x. ... in ...");
    println!();
    println!("types are inferred automatically; \\x. x  has type  ∀a. a -> a.");
    println!();
    println!("examples:");
    println!("  \\x. x                                         -- polymorphic id");
    println!("  \\f. \\x. f (f x)                              -- twice");
    println!("  let id = \\x. x in if id true then id 1 else 0");
    println!("  let rec fact = \\n. if n == 0 then 1 else n * fact (n - 1) in fact 5");
    println!();
    println!("commands:");
    println!("  :t     <expr>  :type  <expr>  show inferred type");
    println!("  :trace <expr>  :tr    <expr>  show each evaluation step");
    println!("  :help          :h             this help");
    println!("  :quit          :q             exit");
}
