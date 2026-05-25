# Lean 4 proofs of STLC type safety

Companion to the Rust implementation in `../src/stlc/`. Mechanically checks
the classical theorems for the Simply Typed Lambda Calculus:

- `progress`     — every well-typed closed term is a value or steps
- `preservation` — reduction preserves typing
- `type_safety`  — packaged combination of the two

## Run

```sh
lean Stlc.lean
```

(Requires Lean 4 — see `lean-toolchain` for the pinned version. Install via
[elan](https://github.com/leanprover/elan).)

Expected output: a single warning that `subst_preserves` (the substitution
lemma) uses `sorry`, followed by the axiom dependency report:

```
Stlc.lean:NNN: warning: declaration uses `sorry`
'Stlc.canonical_bool'   : [propext]
'Stlc.canonical_arrow'  : [propext]
'Stlc.progress'         : [propext]
'Stlc.preservation'     : [propext, sorryAx]
'Stlc.type_safety'      : [propext, sorryAx]
```

## What's verified

The proof is fully checked except for one auxiliary lemma:

| Theorem            | Axioms used         | Status  |
| ------------------ | ------------------- | ------- |
| `canonical_bool`   | `propext`           | ✅ closed |
| `canonical_arrow`  | `propext`           | ✅ closed |
| `progress`         | `propext`           | ✅ closed |
| `subst_preserves`  | —                   | ❌ `sorry` (substitution lemma) |
| `preservation`     | `propext, sorryAx`  | ⚠ structural proof complete; depends on subst_preserves |
| `type_safety`      | `propext, sorryAx`  | ⚠ inherits from preservation |

`propext` (propositional extensionality) is one of Lean 4's standard
axioms; it is not "cheating". `sorryAx` is the placeholder marker.

## Why one `sorry`?

The substitution lemma is the well-known textbook result (Pierce,
*Types and Programming Languages*, Ch. 9). Proving it with de Bruijn
indices requires several auxiliary lemmas about `shift` — weakening,
commutativity of shift and subst, etc. — about 150 more lines of careful
Lean engineering. The proof structure of `preservation` *on top of* the
substitution lemma is fully checked here.

A future revision would:
1. Generalize substitution to arbitrary depth (`subst_general`).
2. Prove weakening: typing is preserved under inserting a binder.
3. Conclude the substitution lemma from the general form.
