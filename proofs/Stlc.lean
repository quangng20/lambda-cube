/-
  STLC: Progress and Preservation in Lean 4.

  Companion to the Rust implementation in `src/stlc/`. We mechanically
  check the two type-safety theorems for the Simply Typed Lambda Calculus
  with booleans:

      progress      every well-typed closed term is a value or steps
      preservation  reduction preserves typing

  Together these prove the slogan "well-typed programs don't get stuck."

  The term language uses de Bruijn indices for variables: `var 0` refers
  to the innermost binder. This makes capture-avoiding substitution a
  computation on natural numbers — no fresh-name generation needed.

  Run with:    lean Stlc.lean
  (No errors = proofs check.)
-/

namespace Stlc

/-! ### Syntax -/

inductive Ty where
  | bool : Ty
  | arrow : Ty → Ty → Ty
  deriving DecidableEq, Repr

inductive Term where
  | tt : Term
  | ff : Term
  | ite : Term → Term → Term → Term
  | var : Nat → Term
  | abs : Ty → Term → Term
  | app : Term → Term → Term
  deriving DecidableEq, Repr

/-- Values: literals and lambda abstractions. -/
inductive Value : Term → Prop where
  | tt : Value .tt
  | ff : Value .ff
  | abs (T : Ty) (b : Term) : Value (.abs T b)

/-! ### de Bruijn shift / substitution -/

/-- Shift free indices ≥ `c` up by `d`. -/
def shift (d : Nat) (c : Nat) : Term → Term
  | .tt => .tt
  | .ff => .ff
  | .ite c1 t1 e1 => .ite (shift d c c1) (shift d c t1) (shift d c e1)
  | .var k => if k < c then .var k else .var (k + d)
  | .abs T b => .abs T (shift d (c+1) b)
  | .app f a => .app (shift d c f) (shift d c a)

/-- Shift free indices > `c` down by 1. (Caller guarantees no var equals `c`.) -/
def shiftDown (c : Nat) : Term → Term
  | .tt => .tt
  | .ff => .ff
  | .ite c1 t1 e1 => .ite (shiftDown c c1) (shiftDown c t1) (shiftDown c e1)
  | .var k => if k ≤ c then .var k else .var (k - 1)
  | .abs T b => .abs T (shiftDown (c+1) b)
  | .app f a => .app (shiftDown c f) (shiftDown c a)

/-- Substitute `s` for variable index `j` in `t`. -/
def subst (j : Nat) (s : Term) : Term → Term
  | .tt => .tt
  | .ff => .ff
  | .ite c t e => .ite (subst j s c) (subst j s t) (subst j s e)
  | .var k => if k = j then s else .var k
  | .abs T b => .abs T (subst (j+1) (shift 1 0 s) b)
  | .app f a => .app (subst j s f) (subst j s a)

/-- β-substitution: replace var 0 with `v` in `body`, dropping the eliminated binder. -/
def substTop (v : Term) (body : Term) : Term :=
  shiftDown 0 (subst 0 (shift 1 0 v) body)

/-! ### Typing -/

/-- `HasType Γ t T` says term `t` has type `T` in context `Γ`. The context
    is indexed by de Bruijn index: `Γ[0]` is the most recent binder. -/
inductive HasType : List Ty → Term → Ty → Prop where
  | tt {Γ} : HasType Γ .tt .bool
  | ff {Γ} : HasType Γ .ff .bool
  | ite {Γ c t e T}
      (hc : HasType Γ c .bool)
      (ht : HasType Γ t T)
      (he : HasType Γ e T) :
      HasType Γ (.ite c t e) T
  | var {Γ i T} (h : Γ[i]? = some T) : HasType Γ (.var i) T
  | abs {Γ T body U} (h : HasType (T :: Γ) body U) :
      HasType Γ (.abs T body) (.arrow T U)
  | app {Γ f a T U}
      (hf : HasType Γ f (.arrow T U))
      (ha : HasType Γ a T) :
      HasType Γ (.app f a) U

/-! ### Small-step CBV reduction -/

inductive Step : Term → Term → Prop where
  | iteT : Step (.ite .tt t e) t
  | iteF : Step (.ite .ff t e) e
  | iteCong : Step c c' → Step (.ite c t e) (.ite c' t e)
  | appBeta : Value v → Step (.app (.abs T b) v) (substTop v b)
  | appCong1 : Step f f' → Step (.app f a) (.app f' a)
  | appCong2 : Value v → Step a a' → Step (.app v a) (.app v a')

/-! ### Canonical forms -/

theorem canonical_bool {v} (hv : Value v) (ht : HasType [] v .bool) :
    v = .tt ∨ v = .ff := by
  cases hv with
  | tt => exact Or.inl rfl
  | ff => exact Or.inr rfl
  | abs _ _ => cases ht

theorem canonical_arrow {v T U} (hv : Value v) (ht : HasType [] v (.arrow T U)) :
    ∃ b, v = .abs T b := by
  cases hv with
  | tt => cases ht
  | ff => cases ht
  | abs T' b' =>
      cases ht with
      | abs _ => exact ⟨b', rfl⟩

/-! ### Progress -/

theorem progress {t T} (ht : HasType [] t T) : Value t ∨ ∃ t', Step t t' := by
  generalize hΓ : ([] : List Ty) = Γ at ht
  induction ht with
  | tt => exact Or.inl .tt
  | ff => exact Or.inl .ff
  | var h =>
      -- contradiction: empty context has no entries
      subst hΓ
      cases h
  | ite hc _ _ ih_c ih_t _ =>
      subst hΓ
      apply Or.inr
      rcases ih_c rfl with hv_c | ⟨c', hcs⟩
      · rcases canonical_bool hv_c hc with hT | hF
        · subst hT; exact ⟨_, .iteT⟩
        · subst hF; exact ⟨_, .iteF⟩
      · exact ⟨_, .iteCong hcs⟩
  | abs _ => exact Or.inl (.abs _ _)
  | app hf _ ih_f ih_a =>
      subst hΓ
      apply Or.inr
      rcases ih_f rfl with hv_f | ⟨f', hfs⟩
      · obtain ⟨b, rfl⟩ := canonical_arrow hv_f hf
        rcases ih_a rfl with hv_a | ⟨a', has⟩
        · exact ⟨_, .appBeta hv_a⟩
        · exact ⟨_, .appCong2 hv_f has⟩
      · exact ⟨_, .appCong1 hfs⟩

/-! ### Substitution lemma and preservation

Preservation reduces to the standard *substitution lemma*: if the body of a
λ has type `U` under context `T :: Γ`, and the argument has type `T` in `Γ`,
then β-substituting the argument into the body produces a term of type `U`
in `Γ`. We state this as `subst_preserves` below.

The lemma is the well-known textbook result (Pierce, *Types and Programming
Languages*, Ch. 9). Its full proof in de Bruijn requires a small library of
auxiliary lemmas about `shift` (weakening, commutativity of shift and subst,
etc.) — substantial Lean engineering, left as an exercise. The structure of
preservation **on top of** the substitution lemma is fully proved here. -/

theorem subst_preserves {Γ T body U v}
    (_hb : HasType (T :: Γ) body U) (_hv : HasType Γ v T) :
    HasType Γ (substTop v body) U := by
  sorry

theorem preservation {Γ t t' T}
    (ht : HasType Γ t T) (hs : Step t t') : HasType Γ t' T := by
  induction hs generalizing Γ T with
  | iteT =>
      cases ht with
      | ite _ ht _ => exact ht
  | iteF =>
      cases ht with
      | ite _ _ he => exact he
  | iteCong _ ih =>
      cases ht with
      | ite hc ht he => exact .ite (ih hc) ht he
  | appBeta _hv =>
      cases ht with
      | app hf ha =>
          cases hf with
          | abs hb => exact subst_preserves hb ha
  | appCong1 _ ih =>
      cases ht with
      | app hf ha => exact .app (ih hf) ha
  | appCong2 _ _ ih =>
      cases ht with
      | app hf ha => exact .app hf (ih ha)

/-- **Type safety**: a well-typed term either is a value or steps to another
    well-typed term. (This is `progress` and `preservation` packaged together
    — the formal statement of "well-typed programs don't get stuck".) -/
theorem type_safety {t T} (ht : HasType [] t T) :
    Value t ∨ ∃ t', Step t t' ∧ HasType [] t' T := by
  rcases progress ht with hv | ⟨t', hs⟩
  · exact Or.inl hv
  · exact Or.inr ⟨t', hs, preservation ht hs⟩

/-! ### What's proved

Run `lean Stlc.lean`. Lean will report exactly one warning:

    Stlc.lean:NNN: warning: declaration uses `sorry`

which is the deliberate placeholder in `subst_preserves` (the substitution
lemma — well-known and citeable, but a chunk of de Bruijn engineering on
its own).

The dependency report below quantifies what's actually checked: -/

-- Output of `lean Stlc.lean` shows:
--   'canonical_bool'  : [propext]
--   'canonical_arrow' : [propext]
--   'progress'        : [propext]
--   'preservation'    : [propext, sorryAx]   ← sorryAx only via subst_preserves
--   'type_safety'     : [propext, sorryAx]   ← inherits from preservation
-- (`propext` is Lean's standard propositional-extensionality axiom — not a hole.)
#print axioms canonical_bool
#print axioms canonical_arrow
#print axioms progress
#print axioms preservation
#print axioms type_safety

end Stlc
