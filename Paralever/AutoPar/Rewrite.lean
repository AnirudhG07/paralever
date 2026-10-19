import Paralever.AutoPar.Sound
import Paralever.AutoPar.Dag
import Paralever.Lang.Notation

/-! # The rewrite, end to end

`paralever { … }` → `ParProg` → a scheduled `ParProg` → surface text again. The round trip is
closed: `surface` emits what `paralever { … }` parses, so a rewritten program can be pasted back
into the language it came from. -- ref: docs/autopar-algorithm.md § Round trip -/

namespace Paralever.AutoPar
open Paralever Paralever.Lang Paralever.Lang.ParProg

/-! ## Units

The scheduling unit is a register-closed segment, not a statement: a load and the store consuming
its register are one unit and are never split across a fork.
-- ref: Paralever/Lang/Analysis.lean `atoms`, docs/autopar.md -/

/-- The chain's units, in order. -/
def units (p : ParProg) : List ParProg := (atoms (flatten p)).map block

/-- **The units run like the program.** Three regroupings, one lemma each. -/
theorem units_faithful (p : ParProg) (ρ : Regs) (σ : State) :
    runSeq (execSeq (block (units p)) ρ) σ = runSeq (execSeq p ρ) σ := by
  show runSeq (execSeq (block ((atoms (flatten p)).map block)) ρ) σ = _
  rw [runSeq_block_map, atoms_flatten, runSeq_flatten]

/-! ## The rewrite -/

/-- The plan for a program. -/
def planOf (p : ParProg) : Plan := plan (units p)

/-- Whether the plan may be committed: no register flows between threads, and the emitted program
passes the independence check. Both are what the soundness theorems need, so a plan that fails
either is simply not used. -/
def rewriteOk (p : ParProg) : Bool :=
  noRegFlow (threads (planOf p)) && wfB (emit (planOf p))

/-- **The rewrite.** The analysis is untrusted; `rewriteOk` is the proved gate, and a program whose
plan does not pass it is returned unchanged. -/
def rewrite (p : ParProg) : ParProg := if rewriteOk p then emit (planOf p) else p

/-- **`seq = par` for the rewrite, unconditionally.** The rewritten program, read in parallel,
leaves exactly the heap the original leaves read sequentially — for every program, with no
hypothesis, because the gate is checked inside `rewrite`. -/
theorem rewrite_sound (p : ParProg) (ρ : Regs) (σ : State) :
    (runSeq (execPar (rewrite p) ρ) σ).2 = (runSeq (execSeq p ρ) σ).2 := by
  unfold rewrite
  by_cases h : rewriteOk p = true
  · simp only [h, ite_true]
    have hflow : noRegFlow (threads (plan (units p))) = true :=
      (Bool.and_eq_true _ _ ▸ h : _ ∧ _).1
    exact rewrite_heap p (units p) (plan_units (units p)) (units_faithful p) hflow ρ σ
  · simp only [h, ite_false, Bool.false_eq_true]
    exact execPar_runSeq_all.1 p ρ σ ▸ rfl

/-- **The rewrite stays well-formed.** So `par_seq_eq` applies to the result, lifting
`rewrite_sound` from one schedule to every schedule. -/
theorem rewrite_wf (p : ParProg) (hp : wfB p = true) : wfB (rewrite p) = true := by
  unfold rewrite
  by_cases h : rewriteOk p = true
  · simp only [h, ite_true]
    exact (Bool.and_eq_true _ _ ▸ h : _ ∧ _).2
  · simp only [h, ite_false, Bool.false_eq_true]; exact hp

/-- **Every schedule of the rewrite agrees with the original.** `rewrite_wf` feeds `par_seq_eq`,
which is the project's metatheorem; `rewrite_sound` ties its sequential side back to `p`. -/
theorem rewrite_parSeqEq (p : ParProg) (hp : wfB p = true) (ρ : Regs) (σ : State) :
    ParSeqEq (execPar (rewrite p) ρ) (execSeq (rewrite p) ρ) σ :=
  ParProg.par_seq_eq (rewrite_wf p hp) ρ σ

/-! ## Quality

`critical` is a lower bound for *any* schedule of the units, so `depth (rewrite p) = critical` is a
certificate that the plan is optimal — and when it is larger, the difference is the price of the
fork–join shape. -- ref: docs/autopar-algorithm.md § The bound -/

/-- The plan's depth, the critical path, and the sequential depth. -/
def quality (p : ParProg) : Nat × Nat × Nat :=
  (depth (rewrite p), critical (units p), depth p)

/-- Whether the plan attains the lower bound. -/
def optimalB (p : ParProg) : Bool := depth (rewrite p) == critical (units p)

/-! ## Back to the language

`surface` prints what `paralever { … }` parses. `loadAt`/`storeAt` have no surface form, so they
print as a marker rather than as something that would silently fail to parse. -/

/-- An expression as a term the surface syntax accepts. -/
def sexp : AExp → String
  | .lit n   => if n < 0 then "AExp.lit (" ++ toString n ++ ")" else toString n
  | .reg r   => "R " ++ toString r
  | .add a b => "(" ++ sexp a ++ " + " ++ sexp b ++ ")"
  | .sub a b => "(" ++ sexp a ++ " - " ++ sexp b ++ ")"
  | .mul a b => "(" ++ sexp a ++ " * " ++ sexp b ++ ")"
  | .min a b => "AExp.min (" ++ sexp a ++ ") (" ++ sexp b ++ ")"
  | .max a b => "AExp.max (" ++ sexp a ++ ") (" ++ sexp b ++ ")"
  | .div a b => "AExp.div (" ++ sexp a ++ ") (" ++ sexp b ++ ")"

mutual

/-- The statements of one program, as surface statements. -/
def sstmts : ParProg → List String
  | .load r l      => ["%" ++ toString r ++ " := [" ++ toString l ++ "]"]
  | .store l e     => ["[" ++ toString l ++ "] := " ++ sexp e]
  | .set r e       => ["%" ++ toString r ++ " := " ++ sexp e]
  | .seq a b       => sstmts a ++ sstmts b
  | .par ss        => ["parallel " ++ String.intercalate " | " (sthreads ss)]
  | .label nm s    => sstmts s ++ ["-- " ++ nm]
  | .loadAt r a e  => ["/- loadAt %" ++ toString r ++ " A" ++ toString a.base
                        ++ "[" ++ sexp e ++ "] : no surface form -/"]
  | .storeAt a e v => ["/- storeAt A" ++ toString a.base ++ "[" ++ sexp e ++ "] := "
                        ++ sexp v ++ " : no surface form -/"]
  | .ifElse c t e  => ["if (" ++ sexp c ++ ") { " ++ String.intercalate "; " (sstmts t)
                        ++ " } else { " ++ String.intercalate "; " (sstmts e) ++ " }"]

/-- Each thread of a fork, braced. -/
def sthreads : List ParProg → List String
  | []      => []
  | s :: ss => ("{ " ++ String.intercalate "; " (sstmts s) ++ " }") :: sthreads ss

end

/-- **A program as surface text**, ready to paste back into `paralever { … }`. -/
def surface (p : ParProg) : String :=
  "paralever {\n  " ++ String.intercalate ";\n  " (sstmts p) ++ "\n}"

/-- **The round trip.** `paralever { … }` in, `paralever { … }` out, with the plan's numbers. -/
def report (p : ParProg) : String :=
  let (d, l, s) := quality p
  surface (rewrite p)
    ++ "\n-- units      " ++ toString (units p).length
    ++ "\n-- stages     " ++ toString (planOf p).length
    ++ "\n-- threads    " ++ toString (threads (planOf p)).length
    ++ "\n-- depth      " ++ toString d ++ "  (sequential " ++ toString s
                          ++ ", lower bound " ++ toString l ++ ")"
    ++ "\n-- optimal    " ++ toString (optimalB p)
    ++ "\n-- committed  " ++ toString (rewriteOk p)

end Paralever.AutoPar
