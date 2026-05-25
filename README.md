# Climbing the Lambda Cube

Six typed lambda calculi in Rust, with Lean 4 type-safety proofs for STLC.

```
                       λω ──────────── λC
                      /│              /│
                     / │             / │
                   λ2 ──┼─────── λP2  │
                   │  λω̲ ────────┼─ λPω̲
                   │  /            │  /
                   │ /             │ /
                   λ→ ──────────── λP
```

## What's here

| Name           | Symbol | Module          | Tests |
| -------------- | ------ | --------------- | ----- |
| Untyped        | λ      | `src/untyped/`  | 15    |
| Simply Typed   | λ→     | `src/stlc/`     | 25    |
| System F       | λ2     | `src/systemf/`  | 18    |
| Hindley-Milner | —      | `src/hm/`       | 24    |
| System Fω      | λω     | `src/fomega/`   | 12    |
| Dependent (λP) | λP     | `src/lambdap/`  | 22    |

116 tests pass. `cargo clippy --all-targets` and `cargo fmt` clean.

Lean 4: `progress` proved (uses only `propext`); `preservation` proved
modulo the substitution lemma, which is the codebase's only `sorry`.

## Run

```sh
cargo run -- untyped
cargo run -- stlc
cargo run -- systemf
cargo run -- hm
cargo run -- fomega
cargo run -- lambdap

cargo test
cargo clippy
```

REPL commands: `:t <expr>`, `:trace <expr>`, `:help`, `:quit`. Fω also has
`:k <type>` for kinds.

## Identity function at each level

```
λ→>  :t \x:Int. x
λx:Int. x : Int -> Int

λ2>  :t /\T. \x:T. x
ΛT. λx:T. x : ∀T. T -> T
λ2>  (/\T. \x:T. x) [Int] 42
42 : Int

hm>  :t \x. x
λx. x : ∀a. a -> a
hm>  let id = \x. x in if id true then id 1 else 0
1 : Int

λω>  :t /\F::* -> *. \x:F Int. x
ΛF::* -> *. λx:F Int. x : ∀F::* -> *. F Int -> F Int

λP>  :t \b: Bool. if b then 42 else true
λb:Bool. if b then 42 else true : Πb:Bool. if b then Int else Bool
λP>  (\b: Bool. if b then 42 else true) true
42 : Int
```

The λP example shows dependent typing: the return type depends on the
runtime value of `b`.

## Layout

```
src/
  main.rs              CLI dispatcher
  untyped/             β-reduction, capture-avoiding substitution
  stlc/                bidirectional type checking, CBV small-step
  systemf/             ∀-types, ΛT, type application, α-equivalence
  hm/                  Algorithm W, unification, let-poly, let-rec
  fomega/              kinds, type-level lambdas, β-equality on types
  lambdap/             unified term/type syntax, dependent if

proofs/
  Stlc.lean            progress and preservation in Lean 4
  README.md
```

Each calculus is a standalone module with its own AST, parser, type
checker, and evaluator. No shared code.

## Notes

Named variables, not de Bruijn. Substitution-based small-step evaluation
throughout. Bidirectional type checking in STLC, System F, Fω.

λP uses `Type : Type`, which is inconsistent (Girard's paradox). Real
systems use a universe hierarchy. This is a teaching fragment.

## License

MIT
