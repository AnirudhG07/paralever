import Paralever

/-! # Spike: a genuinely N-ary `par`, next to the derived one

Not a library module. This is the comparison for the design question "should `par` be N-ary?", kept
where it typechecks so the trade-off is measured rather than argued.

`CLAUDE.md` says `List (ParM α)` is an illegal nested inductive. That verdict is right but the reason
is narrower: Lean rejects

    | parN {α β : Type} : List (ParM α) → (List α → ParM β) → ParM β

with *"nested inductive datatypes parameters cannot contain local variables"* — the obstacle is the
`α` bound by the constructor, not the nesting. Two routes get around it:

* fix the child type, `List (ParM Unit)` — legal, but children can only return `Unit`;
* hand-roll the spine as a mutual inductive, `Kids α` below — legal and fully general.

`ParN` takes the second route, so the question is settled: an N-ary constructor is definable. What
follows is what it costs. -/

namespace Paralever.Test.NArySpike
open Paralever

/-! ### The N-ary program type -/

mutual

/-- Like `ParM`, but `parN` forks a whole list of children at once. -/
inductive ParN : Type → Type 1 where
  | pure  {α : Type}   : α → ParN α
  | read  {α : Type}   : Loc → (Val → ParN α) → ParN α
  | write {α : Type}   : Loc → Val → (Unit → ParN α) → ParN α
  | parN  {α β : Type} : Kids α → (List α → ParN β) → ParN β

/-- The spine of `parN`'s children. A hand-rolled `List (ParN α)`: writing it as `List` is what the
kernel refuses, and writing it this way is what forces every function below to be mutual. -/
inductive Kids : Type → Type 1 where
  | nil  {α : Type} : Kids α
  | cons {α : Type} : ParN α → Kids α → Kids α

end

/-! ### Interpreters — each one now comes in a pair -/

mutual

def runSeqN {τ : Type} : ParN τ → State → τ × State
  | .pure a,      σ => (a, σ)
  | .read l k,    σ => runSeqN (k (σ l)) σ
  | .write l v k, σ => runSeqN (k ()) (σ.update l v)
  | .parN ps k,   σ => let r := runKids ps σ; runSeqN (k r.1) r.2

def runKids {α : Type} : Kids α → State → List α × State
  | .nil,       σ => ([], σ)
  | .cons p ps, σ => let r := runSeqN p σ
                     let r' := runKids ps r.2
                     (r.1 :: r'.1, r'.2)

end

mutual

def accessesN {τ : Type} : ParN τ → State → Footprint
  | .pure _,      _ => .empty
  | .read l k,    σ => Footprint.union ⟨[l], []⟩ (accessesN (k (σ l)) σ)
  | .write l v k, σ => Footprint.union ⟨[], [l]⟩ (accessesN (k ()) (σ.update l v))
  | .parN ps k,   σ => let r := runKids ps σ
                       Footprint.union (accessesKids ps σ) (accessesN (k r.1) r.2)

def accessesKids {α : Type} : Kids α → State → Footprint
  | .nil,       _ => .empty
  | .cons p ps, σ => Footprint.union (accessesN p σ) (accessesKids ps (runSeqN p σ).2)

end

/-- Each child's footprint separately, measured along the canonical run. What the N-ary
independence check needs, and the thing the binary design never has to name. -/
def kidFootprints {α : Type} : Kids α → State → List Footprint
  | .nil,       _ => []
  | .cons p ps, σ => accessesN p σ :: kidFootprints ps (runSeqN p σ).2

/-! ### The difference that matters: the independence obligation

Binary `par` states one `Indep` per node and lets nesting cover the pairs. N-ary `parN` has to say
"all pairs" itself. -/

/-- Bernstein between every pair in the list. -/
def IndepAll : List Footprint → Prop
  | []      => True
  | f :: fs => (∀ g ∈ fs, Indep f g) ∧ IndepAll fs

def indepAllB : List Footprint → Bool
  | []      => true
  | f :: fs => fs.all (fun g => indepB f g) && indepAllB fs

theorem indepAllB_iff (fs : List Footprint) : indepAllB fs = true ↔ IndepAll fs := by
  induction fs with
  | nil => simp [indepAllB, IndepAll]
  | cons f fs ih =>
      simp only [indepAllB, IndepAll, Bool.and_eq_true, List.all_eq_true, ih, indepB_iff]

mutual

def WellFormedN {τ : Type} : ParN τ → State → Prop
  | .pure _,      _ => True
  | .read l k,    σ => WellFormedN (k (σ l)) σ
  | .write l v k, σ => WellFormedN (k ()) (σ.update l v)
  | .parN ps k,   σ =>
      let r := runKids ps σ
      IndepAll (kidFootprints ps σ) ∧ WellFormedKids ps σ ∧ WellFormedN (k r.1) r.2

def WellFormedKids {α : Type} : Kids α → State → Prop
  | .nil,       _ => True
  | .cons p ps, σ => WellFormedN p σ ∧ WellFormedKids ps (runSeqN p σ).2

end

/-! ### Semantics — the all-pairs race check becomes explicit -/

inductive ConfN (α : Type) : Type 1 where
  | run   : ParN α → State → ConfN α
  | wrong : ConfN α

mutual

def nextAccsN {τ : Type} : ParN τ → List Label
  | .pure _      => []
  | .read l _    => [.read l]
  | .write l _ _ => [.write l]
  | .parN ps _   => (nextAccsKids ps).flatten

/-- One label list per live child, so the check below can be stated over pairs. The binary design
flattens at this point instead, and the nesting recovers the pairs. -/
def nextAccsKids {α : Type} : Kids α → List (List Label)
  | .nil       => []
  | .cons p ps => nextAccsN p :: nextAccsKids ps

end

/-- Any two distinct children conflicting. Explicit here; implicit in the binary nesting. -/
def racingAll : List (List Label) → Bool
  | []          => false
  | hd :: rest  => rest.any (fun other => racing hd other) || racingAll rest

/-- All children finished, with their values. -/
def allPure {α : Type} : Kids α → Option (List α)
  | .nil            => some []
  | .cons (.pure a) ps => (allPure ps).map (a :: ·)
  | .cons _ _       => none

mutual

def stepN {α : Type} : ParN α → State → List (ConfN α)
  | .pure _,      _ => []
  | .read l k,    σ => [.run (k (σ l)) σ]
  | .write l v k, σ => [.run (k ()) (σ.update l v)]
  | .parN ps k,   σ =>
      if racingAll (nextAccsKids ps) then [.wrong]
      else match allPure ps with
        | some vs => [.run (k vs) σ]
        | none    => (stepKids ps σ).map fun r =>
            match r with
            | some (ps', σ') => .run (.parN ps' k) σ'
            | none           => .wrong

/-- Step any one child, rebuilding the spine around it. `none` is that child aborting. -/
def stepKids {α : Type} : Kids α → State → List (Option (Kids α × State))
  | .nil,       _ => []
  | .cons p ps, σ =>
      ((stepN p σ).map fun c => match c with
        | .run p' σ' => some (Kids.cons p' ps, σ')
        | .wrong     => none)
      ++ (stepKids ps σ).map fun r => r.map fun x => (Kids.cons p x.1, x.2)

end

/-! ### The same program, both ways -/

def wN (l : Loc) : ParN Unit := .write l (.int 1) .pure
def wB (l : Loc) : ParM Unit := .write l (.int 1) .pure

def kids3 : Kids Unit := .cons (wN 1) (.cons (wN 2) (.cons (wN 3) .nil))
def bad3  : Kids Unit := .cons (wN 1) (.cons (wN 2) (.cons (wN 1) .nil))

def forkN (ks : Kids Unit) : ParN (List Unit) := .parN ks .pure
def forkB (ps : List (ParM Unit)) : ParM (List Unit) := ParM.parAll ps

def σ0 : State := fun _ => .int 0

-- N-ary: one node, three footprints, one all-pairs check.
#guard (kidFootprints kids3 σ0).map Footprint.writes == [[1], [2], [3]]
#guard indepAllB (kidFootprints kids3 σ0) == true
#guard indepAllB (kidFootprints bad3 σ0) == false

-- Binary: the same verdicts, via nesting. Non-adjacent conflict (positions 1 and 3) included.
#guard wellFormedB (forkB [wB 1, wB 2, wB 3]) σ0 == true
#guard wellFormedB (forkB [wB 1, wB 2, wB 1]) σ0 == false

-- Both semantics agree on the canonical result and on detecting the race.
#guard (runSeqN (forkN kids3) σ0).2 1 == .int 1
#guard (runSeqN (forkN kids3) σ0).2 3 == .int 1
#guard (stepN (forkN bad3) σ0).length == 1
#guard racingAll (nextAccsKids bad3) == true
#guard racingAll (nextAccsKids kids3) == false

-- Three children can move, as in the binary version.
#guard (stepN (forkN kids3) σ0).length == 3

end Paralever.Test.NArySpike
