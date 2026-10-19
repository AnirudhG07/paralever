import Paralever.Core.ParM

/-! # State and small-step semantics

Total heap, nondeterministic successor function, races abort to `Conf.wrong`. The freer
representation means the head of the tree is the next action, so no evaluation contexts are
needed. Rationale: `docs/semantics.md`.
-/

namespace Paralever

/-! ### State -/

/-- The heap: a total map from location to value. Total on purpose — there is no allocation and no
partiality, so every read succeeds and `accesses` never has to reason about definedness. Ownership
is expressed by footprints (`Core/Access.lean`), not by the heap's domain. -/
abbrev State := Loc → Val

namespace State

/-- `σ` with location `l` set to `v`. -/
def update (σ : State) (l : Loc) (v : Val) : State :=
  fun k => if k = l then v else σ k

/-- Reading back the location just written. -/
@[simp, grind .] theorem update_same (σ : State) (l : Loc) (v : Val) :
    σ.update l v l = v := by simp [update]

/-- A write is invisible at every other location — the frame property, at one cell. -/
@[simp, grind .] theorem update_other (σ : State) {l k : Loc} (v : Val) (h : k ≠ l) :
    σ.update l v k = σ k := by simp [update, h]

/-- Writes to distinct locations commute. This is the whole sequentialization theorem in miniature:
everything else is bookkeeping that lifts this one fact to whole programs. -/
theorem update_comm (σ : State) {l₁ l₂ : Loc} (v₁ v₂ : Val) (h : l₁ ≠ l₂) :
    (σ.update l₁ v₁).update l₂ v₂ = (σ.update l₂ v₂).update l₁ v₁ := by grind only [update_other, update_same]

/-- The `(location, value)` pairs over `[lo, hi)`. -/
def window (σ : State) (lo hi : Nat) : List (Loc × Val) :=
  (List.range' lo (hi - lo)).map (fun l => (l, σ l))

end State

def stateReprWidth : Nat := 16

/-- `#eval σ` prints the first `stateReprWidth` cells as `(location, value)` pairs. A heap is a
function, so no `Repr` can be exhaustive; use `State.window` for any other range. -/
instance : Repr State where
  reprPrec σ _ := repr (σ.window 0 stateReprWidth)

/-! ### Memory actions -/

/-- One memory action, stripped to what the race check needs: which location, and read or write.
Values are irrelevant to races, so they are not recorded. -/
inductive Label where
  | read  : Loc → Label
  | write : Loc → Label
  deriving DecidableEq, Repr

namespace Label

/-- The location the action touches. -/
def loc : Label → Loc
  | .read l | .write l => l

/-- Whether the action is a write. -/
def isWrite : Label → Bool
  | .write _ => true
  | .read _  => false

/-- Two actions conflict when they hit the same location and at least one writes. Bernstein's
criterion at the granularity of a single step; read/read never conflicts. -/
@[simp, grind .]
def conflicts (a b : Label) : Bool :=
  a.loc == b.loc && (a.isWrite || b.isWrite)

end Label

mutual

/-- The actions `p` could perform *next* — one per live thread. Recurses through nested `par`, so a
deeply forked program contributes every one of its ready heads and no pair is missed.
-- ref: Vafeiadis MFPS'11 -/
@[simp, grind .]
def nextAccs {α : Type} : ParM α → List Label
  | .pure _      => []
  | .read l _    => [.read l]
  | .write l _ _ => [.write l]
  | .par cs _    => (nextAccsChilds cs).flatten

/-- One label list *per child*, kept separate so the race check below can range over pairs. -/
@[simp, grind .]
def nextAccsChilds {αs : List Type} : Childs ParM αs → List (List Label)
  | .nil       => []
  | .cons p ps => nextAccs p :: nextAccsChilds ps

end

/-- Whether any action on one side conflicts with any on the other. -/
@[simp, grind .]
def racing (as bs : List Label) : Bool :=
  as.any fun a => bs.any fun b => a.conflicts b

/-- Whether any *two distinct children* conflict. `step` re-evaluates this at every `par` node on
every step, which is why a run that never reaches `wrong` is race-free at every instant rather than
only at the start. With one N-ary node all pairs are checked at once, rather than spread over
nesting levels. -/
@[simp, grind .]
def racingAll : List (List Label) → Bool
  | []         => false
  | hd :: rest => rest.any (fun other => racing hd other) || racingAll rest

/-! ### Configurations and stepping -/

/-- An execution state: either a program paired with a heap, or `wrong`. `wrong` is where a detected
race lands, and it is terminal and absorbing — per Reynolds' grainless semantics, racy programs are
*excluded* rather than assigned a behaviour, which is what makes the atomic grain irrelevant. -/
@[grind]
inductive Conf (α : Type) : Type 1 where
  | run   : ParM α → State → Conf α
  | wrong : Conf α

/-- Every child has finished, with its tuple of results. `none` means at least one is still running,
so the fork cannot join yet. -/
@[simp, grind .]
def allPure {αs : List Type} : Childs ParM αs → Option (Results αs)
  | .nil               => some ()
  | .cons (.pure a) ps => (allPure ps).map (fun vs => (a, vs))
  | .cons _ _          => none

mutual

/-- One small step: every configuration the program could move to from this heap. The list is the
nondeterminism — a `par` node offers *every* ready child, so all interleavings are covered. Empty
means terminal; a singleton `[wrong]` means this step detected a race. -/
@[simp, grind .]
def step {α : Type} : ParM α → State → List (Conf α)
  | .pure _,      _ => []
  | .read l k,    σ => [.run (k (σ l)) σ]
  | .write l v k, σ => [.run (k ()) (σ.update l v)]
  | .par cs k,    σ =>
      if racingAll (nextAccsChilds cs) then [.wrong]
      else match allPure cs with
        | some vs => [.run (k vs) σ]
        | none    => (stepChilds cs σ).map fun r =>
            match r with
            | some x => .run (.par x.1 k) x.2
            | none   => .wrong

/-- Step any one child, rebuilding the spine around it. Type-preserving: `Childs ParM αs` in,
`Childs ParM αs` out. `none` is that child aborting, which the whole fork inherits. -/
@[simp, grind .]
def stepChilds {αs : List Type} : Childs ParM αs → State →
    List (Option (Childs ParM αs × State))
  | .nil,       _ => []
  | .cons p ps, σ =>
      ((step p σ).map fun c => match c with
        | .run p' σ' => some (Childs.cons p' ps, σ')
        | .wrong     => none)
      ++ (stepChilds ps σ).map fun r => r.map fun x => (Childs.cons p x.1, x.2)

end

/-- `step`, lifted to configurations. `wrong` has no successors, hence it is absorbing. -/
@[simp, grind .]
def stepC {α : Type} : Conf α → List (Conf α)
  | .run p σ => step p σ
  | .wrong   => []

/-- Reflexive-transitive closure of `stepC`: "`c` can execute to `c'` under some schedule." Every statement about *all* interleavings is a statement about this relation. -/
@[grind]
inductive Reaches {α : Type} : Conf α → Conf α → Prop where
  | refl {c} : Reaches c c
  | tail {c c' c''} : Reaches c c' → c'' ∈ stepC c' → Reaches c c''

/-- Reflexive-transitive closure of `stepChilds`: "these children can collectively move to that configuration, nobody having aborted". The children-level analogue of `Reaches`, and what replaces the old left/right branch lemmas — with N children there is no left and right, only "some child moved". -/
inductive ReachesChilds {αs : List Type} :
    Childs ParM αs → State → Childs ParM αs → State → Prop where
  | refl {cs σ} : ReachesChilds cs σ cs σ
  | tail {cs σ cs' σ' cs'' σ''} : ReachesChilds cs σ cs' σ' →
      some (cs'', σ'') ∈ stepChilds cs' σ' → ReachesChilds cs σ cs'' σ''

namespace ReachesChilds

theorem trans {αs : List Type} {a a' a'' : Childs ParM αs} {σ σ' σ'' : State}
    (h1 : ReachesChilds a σ a' σ') (h2 : ReachesChilds a' σ' a'' σ'') :
    ReachesChilds a σ a'' σ'' := by
  induction h2 with
  | refl => exact h1
  | tail _ hmem ih => exact ih.tail hmem

end ReachesChilds

/-- A fork whose children have all finished has nothing left to step — so a `stepChilds` move and a
join are mutually exclusive, which is what lets `step`'s `par` case be read as a trichotomy. -/
theorem stepChilds_eq_nil_of_allPure {αs : List Type} :
    ∀ (cs : Childs ParM αs) (σ : State), (allPure cs).isSome = true → stepChilds cs σ = [] := by
  intro cs σ h
  induction cs with
  | nil => rfl
  | cons p ps ih =>
      match p, h with
      | .pure a, h =>
          have hps : (allPure ps).isSome = true := by
            revert h
            simp only [allPure]
            cases allPure ps <;> simp [Option.map]
          simp only [stepChilds, step, ih hps]
          rfl

/-- No schedule reaches `wrong`, i.e. the program is race-free under every interleaving. -/
@[simp]
def Safe {α : Type} (c : Conf α) : Prop := ¬ Reaches c .wrong

namespace Reaches

/-- One step is a run. -/
theorem single {α : Type} {c c' : Conf α} (h : c' ∈ stepC c) : Reaches c c' :=
  .tail .refl h

/-- Runs compose. -/
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
