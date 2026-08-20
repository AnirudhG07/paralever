import Paralever.Core.ParM

/-! # State and small-step semantics

Total heap, nondeterministic successor function, races abort to `Conf.wrong`. The freer
representation means the head of the tree is the next action, so no evaluation contexts are
needed. Rationale: `docs/semantics.md`.
-/

namespace Paralever

/-! ### State -/

abbrev State := Loc → Val

namespace State

def update (σ : State) (l : Loc) (v : Val) : State :=
  fun k => if k = l then v else σ k

@[simp, grind .] theorem update_same (σ : State) (l : Loc) (v : Val) :
    σ.update l v l = v := by simp [update]

@[simp, grind .] theorem update_other (σ : State) {l k : Loc} (v : Val) (h : k ≠ l) :
    σ.update l v k = σ k := by simp [update, h]

/-- Writes to disjoint locations commute — the state-level core of the theorem. -/
theorem update_comm (σ : State) {l₁ l₂ : Loc} (v₁ v₂ : Val) (h : l₁ ≠ l₂) :
    (σ.update l₁ v₁).update l₂ v₂ = (σ.update l₂ v₂).update l₁ v₁ := by grind only [update_other, update_same]

end State

/-! ### Memory actions -/

inductive Label where
  | read  : Loc → Label
  | write : Loc → Label
  deriving DecidableEq, Repr

namespace Label

def loc : Label → Loc
  | .read l | .write l => l

def isWrite : Label → Bool
  | .write _ => true
  | .read _  => false

/-- Same location, at least one write. Bernstein's criterion for a single step. -/
def conflicts (a b : Label) : Bool :=
  a.loc == b.loc && (a.isWrite || b.isWrite)

end Label

/-- Head actions: the ones that could happen next. Recurses through nested `par`, so every pair of
concurrent threads is compared. -- ref: Vafeiadis MFPS'11 -/
@[simp, grind .]
def nextAccs {α : Type} : ParM α → List Label
  | .pure _      => []
  | .read l _    => [.read l]
  | .write l _ _ => [.write l]
  | .par p q _   => nextAccs p ++ nextAccs q

@[simp, grind .]
def racing (as bs : List Label) : Bool :=
  as.any fun a => bs.any fun b => a.conflicts b

/-! ### Configurations and stepping -/

/-- `wrong` is terminal and absorbing. -/
@[grind]
inductive Conf (α : Type) : Type 1 where
  | run   : ParM α → State → Conf α
  | wrong : Conf α

namespace Conf

/-- Rebuild a `par` node around a stepped left branch. -/
@[simp, grind .]
def inL {α β γ : Type} (q : ParM β) (k : α × β → ParM γ) : Conf α → Conf γ
  | .run p σ => .run (.par p q k) σ
  | .wrong   => .wrong

/-- Rebuild a `par` node around a stepped right branch. -/
@[simp, grind .]
def inR {α β γ : Type} (p : ParM α) (k : α × β → ParM γ) : Conf β → Conf γ
  | .run q σ => .run (.par p q k) σ
  | .wrong   => .wrong

end Conf

/-- Successors of a program in a state. Empty means terminal. -/
@[simp, grind .]
def step {α : Type} : ParM α → State → List (Conf α)
  | .pure _,      _ => []
  | .read l k,    σ => [.run (k (σ l)) σ]
  | .write l v k, σ => [.run (k ()) (σ.update l v)]
  | .par p q k,   σ =>
      if racing (nextAccs p) (nextAccs q) then [.wrong]
      else match p, q with
        | .pure a, .pure b => [.run (k (a, b)) σ]
        | _, _ => (step p σ).map (Conf.inL q k) ++ (step q σ).map (Conf.inR p k)

@[simp, grind .]
def stepC {α : Type} : Conf α → List (Conf α)
  | .run p σ => step p σ
  | .wrong   => []

/-- Reflexive-transitive closure of `stepC`. -/
@[grind]
inductive Reaches {α : Type} : Conf α → Conf α → Prop where
  | refl {c} : Reaches c c
  | tail {c c' c''} : Reaches c c' → c'' ∈ stepC c' → Reaches c c''

/-- No execution races. This is the metatheorem's hypothesis. -/
@[simp]
def Safe {α : Type} (c : Conf α) : Prop := ¬ Reaches c .wrong

namespace Reaches

theorem single {α : Type} {c c' : Conf α} (h : c' ∈ stepC c) : Reaches c c' :=
  .tail .refl h

theorem trans {α : Type} {a b c : Conf α} (hab : Reaches a b) (hbc : Reaches b c) :
    Reaches a c := by
  induction hbc with
  | refl => exact hab
  | tail _ hmem ih => exact .tail ih hmem

/-- A configuration with no successors can only reach itself. -/
@[grind .]
theorem terminal {α : Type} {c c' : Conf α} (hstep : stepC c = []) (h : Reaches c c') :
    c' = c := by
  induction h with
  | refl => rfl
  | tail _ hmem ih => rw [ih, hstep] at hmem; simp at hmem

/-- With exactly one successor, `Reaches` either stops immediately or continues through it.
Used for `read`/`write`, whose steps are deterministic. -/
theorem single_step {α : Type} {c c₀ c' : Conf α} (hstep : stepC c = [c₀])
    (h : Reaches c c') : c' = c ∨ Reaches c₀ c' := by
  induction h with
  | refl => left; rfl
  | tail _ hmem ih =>
      rcases ih with heq | hr
      · right; rw [heq, hstep] at hmem; simp at hmem; rw [hmem]; exact Reaches.refl
      · right; exact hr.tail hmem

end Reaches

end Paralever
