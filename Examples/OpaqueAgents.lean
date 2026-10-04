import Paralever.Lib.OpaqueOp

/-! # Example: two agents whose bodies we never read

The case `docs/opaque-ops.md` exists for: "I have two complicated things running on disjoint data
and no intention of proving anything about their internals." Each agent is an `opaqueOp` — a
declared read set, a declared write set, and a *universally quantified* pure body. The equivalence
proof is three `Disjoint` facts about the declared lists.

Note what is **not** assumed: the footprints are derived (`opaqueOp_accesses`), not axiomatized.
The bodies are quantified, so the theorem holds for every possible implementation of them. -/

namespace Paralever.Examples.OpaqueAgents
open Paralever

/-! ### Two agents on disjoint regions

`agentA` reads `[0,1,2]` and writes `[10,11]`; `agentB` reads `[3,4,5]` and writes `[12,13]`.
`bodyA`/`bodyB` are arbitrary — a solver, a learned model, 400 lines of anything. -/

def regionA : List Loc := [0, 1, 2]
def outA    : List Loc := [10, 11]
def regionB : List Loc := [3, 4, 5]
def outB    : List Loc := [12, 13]

def agentA (bodyA : List Val → List Val) : ParM Unit := opaqueOp regionA outA bodyA
def agentB (bodyB : List Val → List Val) : ParM Unit := opaqueOp regionB outB bodyB

/-- **The payoff**: holds for *every* pair of bodies. Nobody reads `bodyA` or `bodyB`. -/
theorem agents_par_seq_eq (bodyA bodyB : List Val → List Val) (σ : State) :
    ParM.parPair (agentA bodyA) (agentB bodyB)
      ∥≡ ParM.seqPair (agentA bodyA) (agentB bodyB) from σ :=
  opaqueOp_par_seq_eq regionA outA regionB outB bodyA bodyB σ
    (by simp [Disjoint, outA, outB]) (by simp [Disjoint, outA, regionB])
    (by simp [Disjoint, outB, regionA])

/-! ### Shared reads are still fine — Bernstein, not `∗`

Both agents read the *same* region `[0,1,2]`, writing to their own outputs. Independence still
holds: only writes are ever checked against anything. -/

theorem shared_reads_par_seq_eq (bodyA bodyB : List Val → List Val) (σ : State) :
    ParM.parPair (opaqueOp regionA outA bodyA) (opaqueOp regionA outB bodyB)
      ∥≡ ParM.seqPair (opaqueOp regionA outA bodyA) (opaqueOp regionA outB bodyB) from σ :=
  opaqueOp_par_seq_eq regionA outA regionA outB bodyA bodyB σ
    (by simp [Disjoint, outA, outB]) (by simp [Disjoint, outA, regionA])
    (by simp [Disjoint, outB, regionA])

/-! ### Anti-vacuity: declaring overlapping writes makes the obligation unprovable

`agentC` writes `[11, 12]`, overlapping `agentA`'s `[10,11]`. The `Disjoint W₁ W₂` premise of
`opaqueOp_par_seq_eq` is then *false*, so the recipe does not apply — and the footprints really do
conflict, confirming the hypothesis is load-bearing rather than decorative. -/

def outC : List Loc := [11, 12]

def σ0 : State := fun _ => .int 0

/-- The write sets genuinely overlap at location `11` — not a proof-engineering gap. -/
example : ¬ Disjoint outA outC := by
  intro h; exact h 11 (by simp [outA]) (by simp [outC])

/-- And the computed footprints are really not Bernstein-independent, for a concrete pair of
bodies — so no amount of cleverness would discharge the premise. -/
example :
    indepB (accesses (opaqueOp regionA outA (fun _ => [.int 1, .int 2])) σ0)
           (accesses (opaqueOp regionA outC (fun _ => [.int 3, .int 4])) σ0) = false := rfl

end Paralever.Examples.OpaqueAgents
