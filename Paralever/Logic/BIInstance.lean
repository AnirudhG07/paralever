import Paralever.Core.ParM
import Iris.Instances.Classical.Instance
import Iris.ProofMode

/-! # The BI spike — Milestone 0, `PLAN.md`

Confirms the single largest risk flagged when choosing to depend on iris-lean: that instantiating
`Iris.BI` at our own model would demand step-indexing (`▷`) infrastructure too heavy to satisfy
cheaply, forcing the ~2-week hand-rolled-BI fallback.

**Result: no new proof burden at all.** iris-lean already ships a fully-proved, non-step-indexed
`BI` instance for exactly this shape of model —
`Iris.Instances.Classical.Instance : BI (HeapProp Val)`, where
`HeapProp Val := (Nat → StateResult Val) → Prop` and `StateResult` is a three-valued
(`unknown`/`result x`/`conflict`) partial map. Its `▷ := id` (the non-step-indexed case,
`Iris.Instances.Classical.Instance` line ~29) and `COFE (HeapProp Val) := COFE.ofDiscrete _`
(the discrete-COFE trick) are exactly the fallback-avoiding moves `PLAN.md` anticipated —
already done, upstream, for any `Val`. Since `Loc := Nat` (`Core/ParM.lean`), `HeapProp Paralever.Val`
*is* the assertion type `PLAN.md` called `ParaProp`, with zero new algebra to prove: `∗` is
already commutative and associative, `-∗` already right-adjoint to it, etc. — we only import.

**What this does *not* yet settle** (the real remaining design question before Tier-2 can start):
`Instances.Classical`'s `∗` is standard exclusive separation — `P ∗ Q` means the state splits into
*disjoint-domain* sub-heaps, one per side. That is strictly narrower than this project's own
independence notion (`Core/Access.lean`'s `Indep`, Bernstein's conditions) which explicitly
*allows shared reads*. Modelling that needs fractional/read permissions (`Iris/Algebra/DFrac`,
already anticipated in `PLAN.md`) layered on top of this base — not yet built. Also note
`HeapProp`'s carrier (`Nat → StateResult Val`, a genuine partial map) is a different type from
`Core.State` (`Loc → Val`, total) — Tier-2's Hoare triples will need a restriction/embedding
between the two, not a direct reuse of `Core.State` as the assertion carrier.
-/

namespace Paralever.Logic

open Iris.Instances.Classical
open Iris.BI Iris.ProofMode

/-- The Tier-2 assertion type: `PLAN.md`'s `ParaProp`, concretely. Exclusive-ownership separation
only, for now — see the file header. -/
abbrev Assertion := HeapProp Val

/-- Sanity check: `∗` is commutative, using the actual imported proof mode (`iintro`/`isplitl`/
`iexact`), not hand-unfolded definitions. If this ever stops compiling, the BI instance broke. -/
example (P Q : Assertion) : P ∗ Q ⊢ Q ∗ P := by
  iintro ⟨HP, HQ⟩
  isplitl [HQ]
  · iexact HQ
  · iexact HP

/-- Sanity check: `∗` is associative. -/
example (P Q R : Assertion) : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R) := by
  iintro ⟨⟨HP, HQ⟩, HR⟩
  isplitl [HP]
  · iexact HP
  · isplitl [HQ]
    · iexact HQ
    · iexact HR

end Paralever.Logic
