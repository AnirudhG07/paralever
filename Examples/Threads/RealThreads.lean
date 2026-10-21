import Paralever.Compile.Exec
import Paralever.Lib.Notation
import Paralever.Lib.Loop


namespace Paralever.Examples.RealThreads
open Paralever

/-! ### pure -/

def x : Loc := 0
def y : Loc := 1
def sumOut : Loc := 2
def prodOut : Loc := 3

def ival : Val → Int
  | .int n => n
  | _      => 0

def wholePure (σ : State) : State :=
  (σ.update sumOut (.int (ival (σ x) + ival (σ y)))).update prodOut
    (.int (ival (σ x) * ival (σ y)))

/-! ### seq and par -/

def sumInto : ParM Unit :=
  .read x (fun a => .read y (fun b => .write sumOut (.int (ival a + ival b)) (fun _ => .pure ())))

def prodInto : ParM Unit :=
  .read x (fun a => .read y (fun b => .write prodOut (.int (ival a * ival b)) (fun _ => .pure ())))

def wholeSeq : ParM (Unit × Unit) := sumInto ;; prodInto
def wholePar : ParM (Unit × Unit) := sumInto ∥ prodInto

/-! ### pure = seq -/

theorem pure_eq_seq (σ : State) : (runSeq wholeSeq σ).2 = wholePure σ := rfl

/-! ### seq = par -/

theorem sumInto_accesses (σ : State) : accesses sumInto σ = ⟨[x, y], [sumOut]⟩ := rfl
theorem prodInto_accesses (σ : State) : accesses prodInto σ = ⟨[x, y], [prodOut]⟩ := rfl

theorem wellformed (σ : State) : WellFormed wholePar σ := by
  refine WellFormed_par_intro ?_ trivial trivial
  rw [sumInto_accesses, prodInto_accesses]
  exact (indepB_iff _ _).mp (by decide)

theorem seq_eq_par (σ : State) : ParSeqEq wholePar wholeSeq σ := par_seq_eq _ _ σ (wellformed σ)

/-! ### …and the threaded run computes it -/

/-- What the two threads produce is `wholePure`. -/
theorem exec_eq (σ : State) : runPar wholePar σ = wholePure σ := by
  rw [runPar_eq _ σ (wellformed σ), ← pure_eq_seq σ]
  unfold wholePar wholeSeq
  rw [runSeq_parPair_eq_seqPair]

/-! ### A real run -/

def σ0 : State := State.ofList [(x, .int 6), (y, .int 7)]

/-- info: [(0, Paralever.Val.int 6), (1, Paralever.Val.int 7), (2, Paralever.Val.int 13), (3, Paralever.Val.int 42)] -/
#guard_msgs in
#eval runParWindow wholePar σ0 0 4

/-! ### N-ary: three writers, forked together

`parAll` nests binary `par`, so `runParAll` forks three ways and `execTask_parAll_get` is the
corollary — no new interpreter. -/

def bump (l : Loc) : ParM Unit :=
  .read l (fun v => .write l (.int (ival v + 1)) (fun _ => .pure ()))

theorem bump_accesses (l : Loc) (σ : State) : accesses (bump l) σ = ⟨[l], [l]⟩ := rfl

def idxs : List Nat := [4, 5, 6]
def writers : List (ParM Unit) := idxs.map bump

theorem writers_wellformed (σ : State) : WellFormed (ParM.parAll writers) σ :=
  (Loop.parAll_wellformed_of_indexed_rw idxs bump
    (fun i l => l = i) (fun i l => l = i)
    (by decide) (fun _ _ _ => trivial)
    (fun i _ σ => by rw [bump_accesses]; intro l hl; simp_all)
    (fun i _ σ => by rw [bump_accesses]; intro l hl; simp_all)
    (by grind) (by grind) σ).1

/-- info: [(4, Paralever.Val.int 1), (5, Paralever.Val.int 1), (6, Paralever.Val.int 1)] -/
#guard_msgs in
#eval (runParAll writers σ0).window 4 7

/-! ### Independent programs, each wanted for its own answer

No heap is merged here, so no independence obligation arises between them. -/

/-- info: [((), [(0, Paralever.Val.int 6), (1, Paralever.Val.int 7), (2, Paralever.Val.int 13)]),
 ((), [(0, Paralever.Val.int 6), (1, Paralever.Val.int 7), (2, Paralever.Val.int 0)])] -/
#guard_msgs in
#eval (execEach [sumInto, prodInto] σ0).get.map (fun r => (r.1, r.2.window 0 3))

end Paralever.Examples.RealThreads
