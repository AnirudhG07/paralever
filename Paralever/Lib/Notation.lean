import Paralever.Pragma.ArrRef
import Paralever.Lib.Compose

/-! # User-facing notation and vocabulary

`∥≡` for `ParSeqEq`, `Array[]` for `ArrRef`, `Independent` bundling `WellFormed + Indep`.
These are pure syntax and a thin wrapper — nothing new is proved; the finer-grained API
(`WellFormed`, `Indep`, `accesses`, `FootprintWithin`) remains fully accessible.

Rationale: `docs/theory.md` §10 — user-facing layer. -/

namespace Paralever

-- ref: Apt & Olderog §3.2 — independence as a single user-visible obligation

/-! ### `∥≡` — "parallel equals sequential" -/

notation:50 p " ∥≡ " q " from " σ => ParSeqEq p q σ

/-! ### `Array[base, len]` — sugar over `ArrRef.mk` -/

notation "Array[" b ", " n "]" => ArrRef.mk b n

/-! ### `Independent` — the one obligation the user must discharge -/

/-- Bundles `WellFormed p σ`, `WellFormed q (runSeq p σ).2`, and `Indep` into a single predicate.
The user proves `Independent p q σ` (via a smart constructor) and gets `∥≡` from `.par_seq_eq`. -/
structure Independent {α β : Type} (p : ParM α) (q : ParM β) (σ : State) : Prop where
  wf_left  : WellFormed p σ
  wf_right : WellFormed q (runSeq p σ).2
  indep    : Indep (accesses p σ) (accesses q (runSeq p σ).2)

@[simp, grind .]
theorem Independent.par_seq_eq {α β : Type} {p : ParM α} {q : ParM β} {σ : State}
    (h : Independent p q σ) :
    ParM.parPair p q ∥≡ ParM.seqPair p q from σ :=
  Paralever.par_seq_eq p q σ (WellFormed_par_intro h.indep h.wf_left h.wf_right)

/-! ### Smart constructors -/

@[simp, grind .]
theorem Independent.of_disjoint_arrays {α β : Type} (a b : ArrRef) (p : ParM α) (q : ParM β)
    (σ : State)
    (hp_wf : WellFormed p σ) (hq_wf : WellFormed q (runSeq p σ).2)
    (hp : FootprintWithin (accesses p σ) a.InRange)
    (hq : FootprintWithin (accesses q (runSeq p σ).2) b.InRange)
    (hdisj : a.base + a.len ≤ b.base ∨ b.base + b.len ≤ a.base) :
    Independent p q σ :=
  ⟨hp_wf, hq_wf, indep_of_footprint_within hp hq (ArrRef.disjoint_of_range hdisj)⟩

@[simp, grind .]
theorem Independent.of_no_writes {α β : Type} (p : ParM α) (q : ParM β) (σ : State)
    (hp_wf : WellFormed p σ) (hq_wf : WellFormed q (runSeq p σ).2)
    (hp : (accesses p σ).writes = []) (hq : (accesses q (runSeq p σ).2).writes = []) :
    Independent p q σ :=
  ⟨hp_wf, hq_wf, indep_of_no_writes _ _ hp hq⟩

end Paralever
