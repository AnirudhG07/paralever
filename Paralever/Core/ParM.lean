/-! # `ParM` — programs as data

A freer monad over `read`/`write`/`par`. Interpreters (`run`, `accesses`, `compile`) give it
meaning; `do`-notation builds it. No `iter`/unbounded loops — see `docs/program-model.md`; every
flagship example is structural recursion or fuel-bounded, so `ParM` values are finite trees and
every interpreter below is a plain total structural recursion.

Rationale: `docs/program-model.md`.
-/

namespace Paralever

/-- Heap addresses. `Nat` so region arithmetic is `omega`-friendly. -/
abbrev Loc := Nat

inductive Val where
  | int  : Int → Val
  | bool : Bool → Val
  | unit : Val
  deriving DecidableEq, Repr, Inhabited

/-- Effect nodes carry their continuation, so the head of the tree is the next action.
`bind` is defined, not a constructor; there is no `parN`. See `docs/program-model.md`. -/
inductive ParM : Type → Type 1 where
  | pure  {α : Type}     : α → ParM α
  | read  {α : Type}     : Loc → (Val → ParM α) → ParM α
  | write {α : Type}     : Loc → Val → (Unit → ParM α) → ParM α
  /-- The only constructor whose meaning is not forced: `run` interprets it by interleaving. -/
  | par   {α β γ : Type} : ParM α → ParM β → (α × β → ParM γ) → ParM γ

namespace ParM

variable {α β γ : Type}

/-- Graft `f` onto every leaf of `p`. -/
def bind : ParM α → (α → ParM β) → ParM β
  | .pure a,      f => f a
  | .read l k,    f => .read l (fun v => bind (k v) f)
  | .write l v k, f => .write l v (fun u => bind (k u) f)
  | .par p q k,   f => .par p q (fun r => bind (k r) f)

instance : Monad ParM where
  pure := ParM.pure
  bind := ParM.bind

def rd (l : Loc) : ParM Val := .read l .pure

def wr (l : Loc) (v : Val) : ParM Unit := .write l v .pure

def parPair (p : ParM α) (q : ParM β) : ParM (α × β) := .par p q .pure

/-- Sequential counterpart of `parPair`: the right-hand side of the sequentialization theorem. -/
def seqPair (p : ParM α) (q : ParM β) : ParM (α × β) :=
  bind p (fun a => bind q (fun b => .pure (a, b)))

/-- N-ary parallelism, derived from binary `par` — the nesting fixes an association, not a
serialization, so this is genuinely k-way parallel. -/
def parAll : List (ParM α) → ParM (List α)
  | []      => .pure []
  | p :: ps => bind (parPair p (parAll ps)) (fun r => .pure (r.1 :: r.2))

def seqAll : List (ParM α) → ParM (List α)
  | []      => .pure []
  | p :: ps => bind (seqPair p (seqAll ps)) (fun r => .pure (r.1 :: r.2))

/-- Target of the `#parallel for` pragma. -/
def parFor (n : Nat) (f : Fin n → ParM α) : ParM (List α) := parAll (List.ofFn f)

def seqFor (n : Nat) (f : Fin n → ParM α) : ParM (List α) := seqAll (List.ofFn f)

/-! ### Monad laws

Equalities of trees, not merely up to `run`. If one fails to hold on the nose, the representation
is wrong — do not weaken it to hold only under `run`. -/

@[simp] theorem bind_pure_left (a : α) (f : α → ParM β) :
    bind (.pure a) f = f a := rfl

@[simp] theorem bind_pure_right (p : ParM α) : bind p .pure = p := by
  induction p with
  | pure a => rfl
  | read l k ih => exact congrArg (ParM.read l) (funext ih)
  | write l v k ih => exact congrArg (ParM.write l v) (funext ih)
  | par p q k _ _ ih => exact congrArg (ParM.par p q) (funext ih)

theorem bind_assoc (p : ParM α) (f : α → ParM β) (g : β → ParM γ) :
    bind (bind p f) g = bind p (fun a => bind (f a) g) := by
  induction p with
  | pure a => rfl
  | read l k ih => exact congrArg (ParM.read l) (funext fun v => ih v f)
  | write l v k ih => exact congrArg (ParM.write l v) (funext fun u => ih u f)
  | par p q k _ _ ih => exact congrArg (ParM.par p q) (funext fun r => ih r f)

end ParM

end Paralever
