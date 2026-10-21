/-! # `ParM` — programs as data

A freer monad over `read`/`write`/`par`. Interpreters (`run`, `runSeq`, `accesses`) give it
meaning; `do`-notation builds it. No `iter`/unbounded loops — see `docs/program-model.md`; every
flagship example is structural recursion or fuel-bounded, so `ParM` values are finite trees and
every interpreter below is a plain total structural recursion.

`par` is N-ary and heterogeneous: it forks a whole list of children at once, each free to return its
own type. Binary parallelism is the two-child case, not a separate constructor.

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

def Val.addInt (v : Val) (n : Int) : Val :=
  match v with
  | .int i  => .int (i + n)
  | .bool b => .bool b
  | .unit   => .unit

def Val.mapInt (v : Val) (f : Int → Int) : Val :=
  match v with
  | .int i  => .int (f i)
  | .bool b => .bool b
  | .unit   => .unit

def Val.subInt (v : Val) (n : Int) : Val := v.mapInt (· - n)
def Val.mulInt (v : Val) (n : Int) : Val := v.mapInt (· * n)
def Val.divInt (v : Val) (n : Int) : Val := v.mapInt (· / n)
def Val.modInt (v : Val) (n : Int) : Val := v.mapInt (· % n)

instance : HAdd Val Int Val where
  hAdd v n := v.addInt n

instance : HAdd Int Val Val where
  hAdd n v := v.addInt n

instance : HAdd Val Nat Val where
  hAdd v n := v.addInt n

instance : HAdd Nat Val Val where
  hAdd n v := v.addInt n

-- ofNat instance
instance (n : Nat) : OfNat Val n where
  ofNat := Val.int (Int.ofNat n)

/-! ### The children of a fork -/

/-- The results a fork's children produce: one value per child, at that child's own result type.
`[] ↦ Unit` is where the trailing `Unit` in `α × β × Unit` comes from. -/
def Results : List Type → Type
  | []      => Unit
  | α :: αs => α × Results αs

/-- A heterogeneous list of `Node`-things, indexed by the types they return.
N-ary Children on a fork from parent, an inductive type to add a new child to the parent instead of another child branch(like binary tree) -/
inductive Childs (Node : Type → Type 1) : List Type → Type 1 where
  | nil  : Childs Node []
  | cons {α : Type} {αs : List Type} : Node α → Childs Node αs → Childs Node (α :: αs)

/-- A program as data: a finite tree of pure results, memory effects, and parallel forks.

Each effect node carries its own continuation (the *freer* presentation), so the root of the tree is
always the next action and no evaluation contexts are needed. `bind` is a defined graft rather than a
constructor. Being inductive, `ParM` can only express terminating programs.
Rationale: `docs/program-model.md`. -/
-- ANCHOR: site-parm
inductive ParM : Type → Type 1 where
  | pure  {α : Type}     : α → ParM α
  | read  {α : Type}     : Loc → (Val → ParM α) → ParM α
  | write {α : Type}     : Loc → Val → (Unit → ParM α) → ParM α
  /-- Fork every child at once, then continue with all their results. The only constructor whose
  meaning Lean does not already fix: `run` interprets it by interleaving, which is what makes the
  sequentialization theorem non-vacuous. -/
  | par   {β : Type} {αs : List Type} : Childs ParM αs → (Results αs → ParM β) → ParM β
-- ANCHOR_END: site-parm

/-! ### Notation

`Π[ … ]` builds a children list. Commas are decoration — `Π[ a b ]`, `Π[ a, b ]` and `Π[ a, b, ]`
are the same term. Items parse at `max` precedence, so an application needs parentheses: `Π[ (f x) ]`. -/

declare_syntax_cat childItem
syntax term:max (", ")? : childItem

syntax "Π[" childItem* "]" : term

open Lean in
macro_rules
  | `(Π[ $items:childItem* ]) => do
      let mut out ← `(Childs.nil)
      for it in items.reverse do
        let t : TSyntax `term := ⟨it.raw[0]⟩
        out ← `(Childs.cons $t $out)
      return out

/-- `motive` holds of every child. The children-side companion of an induction over `ParM`. -/
def Childs.All (motive : (α : Type) → ParM α → Prop) :
    {αs : List Type} → Childs ParM αs → Prop
  | _, .nil       => True
  | _, .cons p ps => motive _ p ∧ Childs.All motive ps

/-- **Induction on programs.** The `par` case gets an Induction Hypothesis for every child (`Childs.All`) and one for the continuation. -/
@[elab_as_elim]
theorem ParM.inductionOn {motive : (α : Type) → ParM α → Prop}
    (hpure : ∀ {α : Type} (a : α), motive α (.pure a))
    (hread : ∀ {α : Type} (l : Loc) (k : Val → ParM α),
      (∀ v, motive α (k v)) → motive α (.read l k))
    (hwrite : ∀ {α : Type} (l : Loc) (v : Val) (k : Unit → ParM α),
      (∀ u, motive α (k u)) → motive α (.write l v k))
    (hpar : ∀ {β : Type} {αs : List Type} (cs : Childs ParM αs) (k : Results αs → ParM β),
      Childs.All motive cs → (∀ vs, motive β (k vs)) → motive β (.par cs k))
    {α : Type} (p : ParM α) : motive α p :=
  ParM.rec (motive_1 := motive) (motive_2 := fun _ cs => Childs.All motive cs)
    (fun a => hpure a)
    (fun l k ih => hread l k ih)
    (fun l v k ih => hwrite l v k ih)
    (fun cs k ihcs ihk => hpar cs k ihcs ihk)
    trivial
    (fun _ _ ihp ihps => ⟨ihp, ihps⟩)
    p

/-- The children list in which every child has finished with the given result. The target of the
canonical schedule: run each child to completion, left to right. -/
def pureChilds : (αs : List Type) → Results αs → Childs ParM αs
  | [],     _  => .nil
  | _ :: as, vs => .cons (.pure vs.1) (pureChilds as vs.2)

/-- **Mutual induction over a program and a children list.** When the statement needs its
own children-level form: `motive2` is that form, and the `hcons` case is the
2-to-N step — assume it for one child and for the rest, conclude it for the whole list.

`inductionOn` is the lighter version, for when the children only need the program's own motive. -/
theorem ParM.mutualInduction
    {motive1 : (α : Type) → ParM α → Prop}
    {motive2 : (αs : List Type) → Childs ParM αs → Prop}
    (hpure : ∀ {α : Type} (a : α), motive1 α (.pure a))
    (hread : ∀ {α : Type} (l : Loc) (k : Val → ParM α),
      (∀ v, motive1 α (k v)) → motive1 α (.read l k))
    (hwrite : ∀ {α : Type} (l : Loc) (v : Val) (k : Unit → ParM α),
      (∀ u, motive1 α (k u)) → motive1 α (.write l v k))
    (hpar : ∀ {β : Type} {αs : List Type} (cs : Childs ParM αs) (k : Results αs → ParM β),
      motive2 αs cs → (∀ vs, motive1 β (k vs)) → motive1 β (.par cs k))
    (hnil : motive2 [] .nil)
    (hcons : ∀ {α : Type} {αs : List Type} (p : ParM α) (ps : Childs ParM αs),
      motive1 α p → motive2 αs ps → motive2 (α :: αs) (.cons p ps)) :
    (∀ {α : Type} (p : ParM α), motive1 α p) ∧
    (∀ {αs : List Type} (cs : Childs ParM αs), motive2 αs cs) := by
  have h1 : ∀ {α : Type} (p : ParM α), motive1 α p := fun p =>
    ParM.rec (motive_1 := motive1) (motive_2 := motive2)
      (fun a => hpure a) (fun l k ih => hread l k ih) (fun l v k ih => hwrite l v k ih)
      (fun cs k ih2 ihk => hpar cs k ih2 ihk) hnil
      (fun p ps ih1 ih2 => hcons p ps ih1 ih2) p
  refine ⟨h1, ?_⟩
  intro αs cs
  induction cs with
  | nil => exact hnil
  | cons p ps ih => exact hcons p ps (h1 p) ih

namespace ParM

variable {α β γ : Type}

/-- Sequential composition: graft `f` onto every `pure` leaf of `p`. A definition, not a
constructor — which is why the monad laws below hold on the nose. Needs no companion over `Childs`:
a fork's children are untouched, only its continuation is extended. -/
@[simp, grind .]
def bind : ParM α → (α → ParM β) → ParM β
  | .pure a,      f => f a
  | .read l k,    f => .read l (fun v => bind (k v) f)
  | .write l v k, f => .write l v (fun u => bind (k u) f)
  | .par cs k,    f => .par cs (fun vs => bind (k vs) f)

/-- Lets `do`-notation build `ParM` terms. Proofs should use `ParM.bind` or the `doₚ` block
(`Lib/Notation.lean`) instead: `Bind.bind` blocks `simp` from seeing the graft. -/
instance : Monad ParM where
  pure := ParM.pure
  bind := ParM.bind

/-- Read location `l`. -/
def rd (l : Loc) : ParM Val := .read l .pure

/-- Write `v` to location `l`. -/
def wr (l : Loc) (v : Val) : ParM Unit := .write l v .pure

/-- Run `p` and `q` in parallel, returning both results — the `N = 2` case of `par`. The left-hand
side of the sequentialization theorem; `seqPair` is the right. -/
def parPair (p : ParM α) (q : ParM β) : ParM (α × β) :=
  .par Π[ p q ] (fun r => .pure (r.1, r.2.1))

/-- Run `p`, then `q`, returning both results. The right-hand side of the sequentialization
theorem: what `parPair p q` must agree with. -/
@[simp, grind .]
def seqPair (p : ParM α) (q : ParM β) : ParM (α × β) :=
  bind p (fun a => bind q (fun b => .pure (a, b)))

/-! ### Homogeneous forks

A list of same-typed children is the common case (`parFor`, `mapArray`, `reduceArray`). Its type
index is one `α` per child. -/

/-- The type index of a homogeneous family: one `α` per child. -/
def tysOf (α : Type) : List (ParM α) → List Type
  | []      => []
  | _ :: ps => α :: tysOf α ps

def childsOf {α : Type} : (ps : List (ParM α)) → Childs ParM (tysOf α ps)
  | []      => .nil
  | p :: ps => .cons p (childsOf ps)

/-- Collapse a homogeneous fork's results back to a list. -/
def resultsToList {α : Type} : (ps : List (ParM α)) → Results (tysOf α ps) → List α
  | [],      _ => []
  | _ :: ps, x => x.1 :: resultsToList ps x.2

/-- Run every program in the list in parallel, collecting the results. **One** `par` node, whatever
the length — not a nest of binary forks. -/
def parAll {α : Type} (ps : List (ParM α)) : ParM (List α) :=
  .par (childsOf ps) (fun x => .pure (resultsToList ps x))

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
  induction p using ParM.inductionOn with
  | hpure a => rfl
  | hread l k ih => exact congrArg (ParM.read l) (funext ih)
  | hwrite l v k ih => exact congrArg (ParM.write l v) (funext ih)
  | hpar cs k _ ihk => exact congrArg (ParM.par cs) (funext ihk)

/-- Associativity — free, because `bind` grafts onto leaves rather than wrapping the tree. -/
@[simp, grind .] theorem bind_assoc (p : ParM α) (f : α → ParM β) (g : β → ParM γ) :
    bind (bind p f) g = bind p (fun a => bind (f a) g) := by
  induction p using ParM.inductionOn with
  | hpure a => rfl
  | hread l k ih => exact congrArg (ParM.read l) (funext fun v => ih v f)
  | hwrite l v k ih => exact congrArg (ParM.write l v) (funext fun u => ih u f)
  | hpar cs k _ ihk => exact congrArg (ParM.par cs) (funext fun r => ihk r f)

end ParM

end Paralever
