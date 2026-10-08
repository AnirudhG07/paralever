import Paralever.Pragma.ArrRef
import Paralever.Lib.Compose

/-! # User-facing notation and vocabulary

`∥≡` for `ParSeqEq`, `Array[start, end]` for `ArrRef`, `doₚ` blocks for `ParM.bind`,
`Independent` bundling `WellFormed + Indep`.
These are pure syntax and a thin wrapper — nothing new is proved; the finer-grained API
(`WellFormed`, `Indep`, `accesses`, `FootprintWithin`) remains fully accessible.

Rationale: `docs/theory.md` §10 — user-facing layer. -/

namespace Paralever

-- ref: Apt & Olderog §3.2 — independence as a single user-visible obligation

/-! ### `∥≡` — "parallel equals sequential" -/

/-- `p ∥≡ q from σ` is `ParSeqEq p q σ`: from `σ`, `p` and `q` reach exactly the same
`(result, final-state)` pairs. -/
notation:50 p " ∥≡ " q " from " σ => ParSeqEq p q σ

/-! ### `Array[start, end]` — the half-open range `[start, end)`

`ArrRef` stores a base and a length, but at a use site the two *endpoints* are what the reader knows:
`Array[n, 2*n]` is the block from `n` up to but not including `2*n`. -/

/-- `Array[s, e]` is the `ArrRef` covering `[s, e)`, i.e. `ArrRef.mk s (e - s)`. The second argument
is the *end* location, not a length. -/
notation "Array[" s ", " e "]" => ArrRef.mk s (e - s)

/-! ### `∥` and `;;` — the two pair combinators, infix

`∥` is Concurrent Kleene Algebra's parallel composition; `;;` is spelled to read as sequencing.
Pure notation: both expand to the constructors, so a program written with them is the same term as
one written by hand, and `∥≡` still lexes as a single token.
-- ref: papers.md §4.3 (Hoare, Möller, Struth, Wehrman) -/

@[inherit_doc ParM.parPair] infixl:65 " ∥ " => ParM.parPair
@[inherit_doc ParM.seqPair] infixl:65 " ;; " => ParM.seqPair

/-! ### `doₚ` — a `do`-shaped block that is literally `ParM.bind`

`do` works and is `rfl`-equal, but it desugars to `Bind.bind`, so a `simp`/`rw` lemma stated about
`ParM.bind` never fires: the goal still shows `do let v ← …` and the `Monad` instance is in the way.
That is why `Examples/SumArray.lean` was written in raw constructors.

A `doₚ` block has the same shape as `do` and expands to `ParM.bind` *literally*, so it reads like
ordinary imperative code while keeping the proof behaviour of the hand-written form. The last line of
a block is its result. -/

-- One step of a `doₚ` block: either a binding or a statement whose value is discarded.
declare_syntax_cat doPStep

/-- `let x ← p` — run `p` and bind its result to `x` in the rest of the block. -/
syntax "let " ident " ← " term : doPStep

/-- `let (x, y) ← p` — bind a pair result, as a `par`/`seq` join produces. -/
syntax "let " "(" ident ", " ident ")" " ← " term : doPStep

/-- A bare `ParM` term — run it for its effect, or, as the last step, for its result. -/
syntax term : doPStep

/-- A block of `doPStep`s, one per line, aligned by `colGe` as in a `do` block. -/
syntax "doₚ" withPosition((colGe doPStep)+) : term

open Lean in
/-- Fold a list of `doₚ` steps into nested `ParM.bind` applications, right to left: the last step
becomes the innermost term and is the block's result. Errors on an empty block and on a block ending
in `let`, which would have no result to return. -/
partial def expandDoP : List (TSyntax `doPStep) → MacroM (TSyntax `term)
  | [] => Macro.throwError "doₚ: empty block"
  | [s] => match s with
      | `(doPStep| let $_ ← $_) =>
          Macro.throwError "doₚ: a block cannot end with `let` — the last line is the result"
      | `(doPStep| let ($_, $_) ← $_) =>
          Macro.throwError "doₚ: a block cannot end with `let` — the last line is the result"
      | `(doPStep| $e:term) => return e
      | _ => Macro.throwUnsupported
  | s :: rest => do
      let body ← expandDoP rest
      match s with
      | `(doPStep| let $x ← $p) => `(ParM.bind $p (fun $x => $body))
      | `(doPStep| let ($x, $y) ← $p) => `(ParM.bind $p (fun r => (fun $x $y => $body) r.1 r.2))
      | `(doPStep| $e:term)     => `(ParM.bind $e (fun _ => $body))
      | _ => Macro.throwUnsupported

-- Expansion of `doₚ`. A macro rather than an elaborator, so the result is literally `ParM.bind`.
macro_rules
  | `(doₚ $steps:doPStep*) => expandDoP steps.toList

/-! ### `Independent` — the one obligation the user must discharge -/

/-- `p` and `q` may be run in parallel from `σ`: each is internally well-formed and their footprints
are Bernstein-independent. The three fields are exactly the hypotheses of `WellFormed_par_intro`,
bundled so a user proves one thing — via a smart constructor below — and reads off `∥≡` with
`.par_seq_eq`. `q`'s side is measured from `(runSeq p σ).2`, matching `accesses`' asymmetry in the
`par` case. -/
structure Independent {α β : Type} (p : ParM α) (q : ParM β) (σ : State) : Prop where
  wf_left  : WellFormed p σ
  wf_right : WellFormed q (runSeq p σ).2
  indep    : Indep (accesses p σ) (accesses q (runSeq p σ).2)

/-- **Independence gives parallel-equals-sequential**: from `Independent p q σ`, `parPair p q` and
`seqPair p q` reach the same outcomes. The user-facing form of `par_seq_eq`. -/
@[simp, grind .]
theorem Independent.par_seq_eq {α β : Type} {p : ParM α} {q : ParM β} {σ : State}
    (h : Independent p q σ) :
    ParM.parPair p q ∥≡ ParM.seqPair p q from σ :=
  Paralever.par_seq_eq p q σ (WellFormed_par_intro h.indep h.wf_left h.wf_right)

/-! ### Smart constructors

Two routes to `Independent`, covering the cases that come up: disjoint arrays, and no writes at all.
Each takes the two well-formedness proofs plus whatever discharges Bernstein. -/

/-- `Independent` from confinement to two `ArrRef`s whose ranges do not overlap. The disjointness
premise is arithmetic in the four endpoint constants, so `omega` closes it. -/
@[simp, grind .]
theorem Independent.of_disjoint_arrays {α β : Type} (a b : ArrRef) (p : ParM α) (q : ParM β)
    (σ : State)
    (hp_wf : WellFormed p σ) (hq_wf : WellFormed q (runSeq p σ).2)
    (hp : FootprintWithin (accesses p σ) a.InRange)
    (hq : FootprintWithin (accesses q (runSeq p σ).2) b.InRange)
    (hdisj : a.base + a.len ≤ b.base ∨ b.base + b.len ≤ a.base) :
    Independent p q σ :=
  ⟨hp_wf, hq_wf, indep_of_footprint_within hp hq (ArrRef.disjoint_of_range hdisj)⟩

/-- `Independent` for two read-only programs, whatever they read — no range argument needed. -/
@[simp, grind .]
theorem Independent.of_no_writes {α β : Type} (p : ParM α) (q : ParM β) (σ : State)
    (hp_wf : WellFormed p σ) (hq_wf : WellFormed q (runSeq p σ).2)
    (hp : (accesses p σ).writes = []) (hq : (accesses q (runSeq p σ).2).writes = []) :
    Independent p q σ :=
  ⟨hp_wf, hq_wf, indep_of_no_writes _ _ hp hq⟩

end Paralever
