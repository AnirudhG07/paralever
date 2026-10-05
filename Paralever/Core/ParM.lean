/-! # `ParM` — programs as data

A freer monad over `read`/`write`/`par`. Interpreters (`run`, `accesses`, `compile`) give it
meaning; `do`-notation builds it. No `iter`/unbounded loops — see `docs/program-model.md`; every
flagship example is structural recursion or fuel-bounded, so `ParM` values are finite trees and
every interpreter below is a plain total structural recursion.

Rationale: `docs/program-model.md`.
-/

namespace Paralever

/-- A heap address. `Nat` rather than an opaque type so that region arithmetic — "is `i*n+j` inside
`[base, base+len)`?" — is `omega`-friendly. -/
abbrev Loc := Nat

/-- The heap's value universe. Deliberately small: `Storable α` (`Lib/TypedRead.lean`) encodes
richer types into it, so adding a constructor here is never the right fix. -/
inductive Val where
  | int  : Int → Val
  | bool : Bool → Val
  | unit : Val
  deriving DecidableEq, Repr, Inhabited

/-- A program as data: a finite tree of pure results, memory effects, and parallel forks.

Each effect node carries its own continuation (the *freer* presentation), so the root of the tree is
always the next action and no evaluation contexts are needed. Two consequences worth knowing:
`bind` is a defined graft rather than a constructor, and there is no `parN` — N-ary parallelism is
derived from binary `par`, which makes the N-ary theorem a corollary. Being inductive, `ParM` can
only express terminating programs. Rationale: `docs/program-model.md`. -/
inductive ParM : Type → Type 1 where
  | pure  {α : Type}     : α → ParM α
  | read  {α : Type}     : Loc → (Val → ParM α) → ParM α
  | write {α : Type}     : Loc → Val → (Unit → ParM α) → ParM α
  /-- Fork two programs, then continue with both results. The only constructor whose meaning Lean
  does not already fix: `run` interprets it by interleaving, which is what makes the
  sequentialization theorem non-vacuous. -/
  | par   {α β γ : Type} : ParM α → ParM β → (α × β → ParM γ) → ParM γ

namespace ParM

variable {α β γ : Type}

/-- Sequential composition: graft `f` onto every `pure` leaf of `p`. A definition, not a
constructor — which is why the monad laws below hold on the nose. -/
@[simp, grind .]
def bind : ParM α → (α → ParM β) → ParM β
  | .pure a,      f => f a
  | .read l k,    f => .read l (fun v => bind (k v) f)
  | .write l v k, f => .write l v (fun u => bind (k u) f)
  | .par p q k,   f => .par p q (fun r => bind (k r) f)

/-- Lets `do`-notation build `ParM` terms. Proofs should use `ParM.bind` or the `doₚ` block
(`Lib/Notation.lean`) instead: `Bind.bind` blocks `simp` from seeing the graft. -/
instance : Monad ParM where
  pure := ParM.pure
  bind := ParM.bind

/-- Read location `l`. -/
def rd (l : Loc) : ParM Val := .read l .pure

/-- Write `v` to location `l`. -/
def wr (l : Loc) (v : Val) : ParM Unit := .write l v .pure

/-- Run `p` and `q` in parallel, returning both results. The left-hand side of the
sequentialization theorem; `seqPair` is the right. -/
def parPair (p : ParM α) (q : ParM β) : ParM (α × β) := .par p q .pure

/-- Run `p`, then `q`, returning both results. The right-hand side of the sequentialization
theorem: what `parPair p q` must agree with. -/
@[simp, grind .]
def seqPair (p : ParM α) (q : ParM β) : ParM (α × β) :=
  bind p (fun a => bind q (fun b => .pure (a, b)))

/-- Run every program in the list in parallel, collecting the results.

Derived from binary `par` rather than a constructor of its own (`List (ParM α)` would be an illegal
nested inductive). The nesting fixes an *association*, not a serialization, so this is genuinely
k-way parallel and the N-ary theorem comes out as a corollary of the binary one. -/
@[simp, grind .]
def parAll : List (ParM α) → ParM (List α)
  | []      => .pure []
  | p :: ps => bind (parPair p (parAll ps)) (fun r => .pure (r.1 :: r.2))

/-- Sequential counterpart of `parAll`: run the list left to right, collecting the results. -/
@[simp, grind .]
def seqAll : List (ParM α) → ParM (List α)
  | []      => .pure []
  | p :: ps => bind (seqPair p (seqAll ps)) (fun r => .pure (r.1 :: r.2))

/-- Run `f i` in parallel for every `i < n`. The target the `#parallel_for` pragma expands to. -/
def parFor (n : Nat) (f : Fin n → ParM α) : ParM (List α) := parAll (List.ofFn f)

/-- Sequential counterpart of `parFor`. -/
def seqFor (n : Nat) (f : Fin n → ParM α) : ParM (List α) := seqAll (List.ofFn f)

/-! ### Monad laws

These are equalities of *trees*, not merely equalities under `run`. That is the correctness check on
the representation: if one of them ever needs weakening to hold only up to `run`, the representation
is wrong. -/

/-- Left identity. -/
@[simp] theorem bind_pure_left (a : α) (f : α → ParM β) :
    bind (.pure a) f = f a := rfl

/-- Right identity. -/
@[simp] theorem bind_pure_right (p : ParM α) : bind p .pure = p := by
  induction p with
  | pure a => rfl
  | read l k ih => exact congrArg (ParM.read l) (funext ih)
  | write l v k ih => exact congrArg (ParM.write l v) (funext ih)
  | par p q k _ _ ih => exact congrArg (ParM.par p q) (funext ih)

/-- Associativity — free, because `bind` grafts onto leaves rather than wrapping the tree. -/
@[simp, grind .] theorem bind_assoc (p : ParM α) (f : α → ParM β) (g : β → ParM γ) :
    bind (bind p f) g = bind p (fun a => bind (f a) g) := by
  induction p with
  | pure a => rfl
  | read l k ih => exact congrArg (ParM.read l) (funext fun v => ih v f)
  | write l v k ih => exact congrArg (ParM.write l v) (funext fun u => ih u f)
  | par p q k _ _ ih => exact congrArg (ParM.par p q) (funext fun r => ih r f)

end ParM

end Paralever
