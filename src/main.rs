//! Climbing the Lambda Cube: an interpreter family in Rust.
//!
//! Each calculus has its own module with parser, type checker (where applicable),
//! evaluator, and REPL. Dispatch happens on the first CLI argument.

mod fomega;
mod hm;
mod lambdap;
mod stlc;
mod systemf;
mod untyped;

use std::env;
use std::process::ExitCode;

fn main() -> ExitCode {
    let mode = env::args().nth(1).unwrap_or_default();
    match mode.as_str() {
        "untyped" | "lc" => {
            untyped::repl();
            ExitCode::SUCCESS
        }
        "stlc" | "lambda-arrow" => {
            stlc::repl();
            ExitCode::SUCCESS
        }
        "systemf" | "f" | "lambda2" => {
            systemf::repl();
            ExitCode::SUCCESS
        }
        "hm" | "ml" => {
            hm::repl();
            ExitCode::SUCCESS
        }
        "fomega" | "fw" | "lambdaomega" => {
            fomega::repl();
            ExitCode::SUCCESS
        }
        "lambdap" | "lp" | "dep" => {
            lambdap::repl();
            ExitCode::SUCCESS
        }
        "help" | "--help" | "-h" => {
            print_usage();
            ExitCode::SUCCESS
        }
        "" => {
            print_usage();
            ExitCode::SUCCESS
        }
        other => {
            eprintln!("unknown calculus: {:?}", other);
            print_usage();
            ExitCode::FAILURE
        }
    }
}

fn print_usage() {
    println!("Climbing the Lambda Cube");
    println!();
    println!("usage:  lambda-cube <calculus>");
    println!();
    println!("available calculi:");
    println!("  untyped   λ      untyped lambda calculus");
    println!("  stlc      λ→     simply typed lambda calculus");
    println!("  systemf   λ2     System F (polymorphic lambda calculus)");
    println!("  hm        —      Hindley-Milner inference (ML-style)");
    println!("  fomega    λω     System Fω (polymorphism + type operators)");
    println!("  lambdap   λP     dependent types (teaching fragment)");
}
