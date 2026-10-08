import Paralever.Lib.Notation

/-! # Example: one parallel region inside an ordinary sequential program

The realistic shape. A program runs sequentially, reaches a part whose two halves do not interfere,
runs those together, joins, and carries on sequentially:

    mark start  ;  ( sum  ∥  product )  ;  mark done

Cells `0` and `1` hold the two inputs. The sum lands in `2`, the product in `3`. **Both halves read
both inputs** — that is the shared-reads case Bernstein allows and `∗`-disjointness does not — and
they write different cells, so they are independent.

Two things are demonstrated:

* `par_seq_eq_region` — replacing the region by its parallel version leaves the whole program's
  outcomes unchanged, and only the *region* carries an independence obligation.
* `Computes` — the pure (`pure = seq`) proofs compose along the program, and the parallel
  substitution is invisible to them.

Rationale: `docs/decomposition.md`, `docs/pure-bridge.md`. -/

namespace Paralever.Examples.Region
open Paralever

/-! ### Layout -/

def x : Loc := 0        -- first input
def y : Loc := 1        -- second input
def sumOut : Loc := 2
def prodOut : Loc := 3
def startFlag : Loc := 8
def doneFlag : Loc := 9

/-- The `Int` in a cell, `0` for anything else. -/
def ival : Val → Int
  | .int n => n
  | _      => 0

/-! ### pure — four ordinary state transformers, no monad -/

def markStartPure (σ : State) : State := σ.update startFlag (.int 1)
def sumPure       (σ : State) : State := σ.update sumOut  (.int (ival (σ x) + ival (σ y)))
def prodPure      (σ : State) : State := σ.update prodOut (.int (ival (σ x) * ival (σ y)))
def markDonePure  (σ : State) : State := σ.update doneFlag (.int 1)

/-- The whole program, purely: four updates, left to right. -/
def wholePure (σ : State) : State :=
  markDonePure (prodPure (sumPure (markStartPure σ)))

/-! ### The four pieces as `ParM` programs -/

def markStart : ParM Unit := ParM.wr startFlag (.int 1)
def markDone  : ParM Unit := ParM.wr doneFlag (.int 1)

def sumInto  : ParM Unit :=
  .read x (fun a => .read y (fun b => .write sumOut  (.int (ival a + ival b)) (fun _ => .pure ())))

def prodInto : ParM Unit :=
  .read x (fun a => .read y (fun b => .write prodOut (.int (ival a * ival b)) (fun _ => .pure ())))

/-! ### seq and par — one character apart -/

def wholeSeq : ParM Unit :=
  doₚ
    markStart
    let (_s, _p) ← sumInto ;; prodInto
    markDone

def wholePar : ParM Unit :=
  doₚ
    markStart
    let (_s, _p) ← sumInto ∥ prodInto
    markDone

/-! ### pure = seq, piece by piece, then composed

Each piece's `Computes` fact is `rfl`. `Computes.bind` chains them; `Computes.parPair` says the
parallel region computes the same thing as the sequential one, so the composition is identical. -/

theorem markStart_computes : Computes markStart (fun _ => ()) markStartPure := fun _ => rfl
theorem markDone_computes  : Computes markDone  (fun _ => ()) markDonePure  := fun _ => rfl
theorem sumInto_computes   : Computes sumInto   (fun _ => ()) sumPure       := fun _ => rfl
theorem prodInto_computes  : Computes prodInto  (fun _ => ()) prodPure      := fun _ => rfl

/-- **`pure = seq` for the whole program**, assembled from the four pieces. -/
theorem seq_computes : Computes wholeSeq (fun _ => ()) wholePure :=
  (markStart_computes.bind (fun _ =>
    (sumInto_computes.seqPair prodInto_computes).bind (fun _ => markDone_computes)))

/-- **The parallel program computes the same pure function.** Identical proof, with
`Computes.parPair` in place of `Computes.seqPair` — no independence hypothesis is needed here,
because this is a statement about the canonical run. -/
theorem par_computes : Computes wholePar (fun _ => ()) wholePure :=
  (markStart_computes.bind (fun _ =>
    (sumInto_computes.parPair prodInto_computes).bind (fun _ => markDone_computes)))

theorem pure_eq_seq (σ : State) : (runSeq wholeSeq σ).2 = wholePure σ := seq_computes.state σ

/-! ### seq = par — the obligation is the region's, and nothing else's

The prefix and suffix are single writes, so their well-formedness is `trivial`. -/

/-- Neither half branches on a value it reads, so its footprint is the same in every state. -/
theorem sumInto_accesses  (σ : State) : accesses sumInto  σ = ⟨[x, y], [sumOut]⟩  := rfl
theorem prodInto_accesses (σ : State) : accesses prodInto σ = ⟨[x, y], [prodOut]⟩ := rfl

/-- The two halves share **both reads** and write different cells: independent by Bernstein,
rejected by `∗`-disjointness. -/
theorem region_indep (σ : State) :
    Indep (accesses sumInto σ) (accesses prodInto (runSeq sumInto σ).2) := by
  rw [sumInto_accesses, prodInto_accesses]
  exact (indepB_iff _ _).mp (by decide)

theorem whole_wellformed (σ : State) : WellFormed wholePar σ := by
  show WellFormed (ParM.bind markStart (fun _ =>
    ParM.bind (ParM.parPair sumInto prodInto) (fun r => (fun _ _ => markDone) r.1 r.2))) σ
  rw [WellFormed_bind]
  refine ⟨trivial, ?_⟩
  rw [WellFormed_bind]
  exact ⟨WellFormed_par_intro (region_indep _) trivial trivial, trivial⟩

/-- **Parallelise the middle only.** The surrounding sequential code is untouched. -/
theorem seq_eq_par (σ : State) : ParSeqEq wholePar wholeSeq σ :=
  par_seq_eq_region markStart sumInto prodInto _ σ (whole_wellformed σ)

/-! ### A concrete run: inputs 6 and 7 -/

def σ0 : State
  | 0 => .int 6
  | 1 => .int 7
  | _ => .int 0

/-- info: [(0, 6), (1, 7), (2, 13), (3, 42), (8, 1), (9, 1)] -/
#guard_msgs in
#eval ([x, y, sumOut, prodOut, startFlag, doneFlag].map
  (fun l => (l, ival ((runSeq wholePar σ0).2 l))))

end Paralever.Examples.Region
