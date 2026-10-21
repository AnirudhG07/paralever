import Paralever.Lib.Cost
import Paralever.Lib.Pure


namespace Paralever.Examples.OpaqueAgents
open Paralever

/-- `agentA` reads `[0,1,2]` and writes `[10,11]`; `agentB` reads `[3,4,5]` and writes `[12,13]`. -/
def regionA : List Loc := [0, 1, 2]
def outA    : List Loc := [10, 11]
def regionB : List Loc := [3, 4, 5]
def outB    : List Loc := [12, 13]

def σ0 : State := fun _ => .int 0

/-! ### pure

`opaquePure` (`Lib/OpaqueOp.lean`) is the generic counterpart: gather the declared cells, apply the
body, land the results on the declared outputs. -/

def agentsPure (bodyA bodyB : List Val → List Val) (σ : State) : State :=
  opaquePure regionB outB bodyB (opaquePure regionA outA bodyA σ)

/-! ### seq -/

def agentA (bodyA : List Val → List Val) : ParM Unit := opaqueOp regionA outA bodyA
def agentB (bodyB : List Val → List Val) : ParM Unit := opaqueOp regionB outB bodyB

def agentsSeq (bodyA bodyB : List Val → List Val) : ParM (Unit × Unit) :=
  ParM.seqPair (agentA bodyA) (agentB bodyB)

/-! ### par -/

def agentsPar (bodyA bodyB : List Val → List Val) : ParM (Unit × Unit) :=
  ParM.parPair (agentA bodyA) (agentB bodyB)

/-! ### pure = seq -/

theorem pure_eq_seq (bodyA bodyB : List Val → List Val) (σ : State) :
    (runSeq (agentsSeq bodyA bodyB) σ).2 = agentsPure bodyA bodyB σ := by
  simp only [agentsSeq, agentA, agentB, ParM.seqPair, runSeq_bind, runSeq]
  rw [opaqueOp_runSeq regionA outA bodyA σ, opaqueOp_runSeq regionB outB bodyB]
  rfl

/-- With constant bodies at `σ0`: each agent's outputs hold its own results and nothing else moves. -/
example : (agentsPure (fun _ => [.int 1, .int 2]) (fun _ => [.int 3, .int 4]) σ0 10,
           agentsPure (fun _ => [.int 1, .int 2]) (fun _ => [.int 3, .int 4]) σ0 13)
    = (.int 1, .int 4) := rfl

/-! ### seq = par

Three `Disjoint` facts about the declared lists, and nothing else. -/

private theorem wf (bodyA bodyB : List Val → List Val) (σ : State) :
    WellFormed (agentsPar bodyA bodyB) σ :=
  let h := Independent.of_declared_footprint regionA outA regionB outB bodyA bodyB σ
    (by simp [Disjoint, outA, outB]) (by simp [Disjoint, outA, regionB])
    (by simp [Disjoint, outB, regionA])
  WellFormed_par_intro h.indep h.wf_left h.wf_right

theorem seq_eq_par (bodyA bodyB : List Val → List Val) (σ : State) :
    agentsPar bodyA bodyB ∥≡ agentsSeq bodyA bodyB from σ :=
  par_seq_eq _ _ σ (wf bodyA bodyB σ)

/-- **Bernstein, not `∗`**: both agents reading the *same* region is still independent, because only
writes are ever checked against anything. -/
theorem shared_reads_par_seq_eq (bodyA bodyB : List Val → List Val) (σ : State) :
    ParM.parPair (opaqueOp regionA outA bodyA) (opaqueOp regionA outB bodyB)
      ∥≡ ParM.seqPair (opaqueOp regionA outA bodyA) (opaqueOp regionA outB bodyB) from σ :=
  opaqueOp_par_seq_eq regionA outA regionA outB bodyA bodyB σ
    (by simp [Disjoint, outA, outB]) (by simp [Disjoint, outA, regionA])
    (by simp [Disjoint, outB, regionA])

/-! ### time par < time seq -/

/-- `max` is derived from the parallel-round semantics, not written into it (`docs/cost.md`). -/
theorem time_eq_max (bodyA bodyB : List Val → List Val) (σ : State) :
    time (agentsPar bodyA bodyB) σ = max (time (agentA bodyA) σ) (time (agentB bodyB) σ) :=
  time_parPair_eq_max _ _ σ (wf bodyA bodyB σ)

theorem time_lt (bodyA bodyB : List Val → List Val) (σ : State) :
    time (agentsPar bodyA bodyB) σ < time (agentsSeq bodyA bodyB) σ :=
  time_par_lt_seq _ _ σ (wf bodyA bodyB σ)
    (opaqueOp_time_pos _ _ outA bodyA σ) (opaqueOp_time_pos _ _ outB bodyB σ)

/-- Same operation count either way, with no hypothesis at all — only the rounds shrink. -/
theorem work_eq (bodyA bodyB : List Val → List Val) (σ : State) :
    work (agentsPar bodyA bodyB) σ = work (agentsSeq bodyA bodyB) σ := work_par_eq_seq _ _ σ

/-! ### Anti-vacuity

`outC` overlaps `outA` at location `11`, so `opaqueOp_par_seq_eq`'s `Disjoint W₁ W₂` premise is
false — and the computed footprints really do conflict, for concrete bodies. No amount of cleverness
would discharge the premise. -/

def outC : List Loc := [11, 12]

example :
    indepB (accesses (opaqueOp regionA outA (fun _ => [.int 1, .int 2])) σ0)
           (accesses (opaqueOp regionA outC (fun _ => [.int 3, .int 4])) σ0) = false := rfl

end Paralever.Examples.OpaqueAgents
