import Paralever.Kernels.Assign
import Paralever.Lib.Pure

/-! # Two-dimensional tasks, without index arithmetic

A loop nest over an `n × m` output grid is the commonest shape after a flat map, and it is where
a `Nat`-indexed validator costs the most: the user has to linearise `(i,j)` to `p = i*m + j`, write
every read location in terms of `p / m` and `p % m`, and then prove bounds on those quotients before
anything about footprints can even be stated.

None of that is necessary. `parEach` (`Lib/Assign.lean`) takes tasks keyed by an arbitrary type, so
the key can simply *be* the pair `(i, j)`. `gridIdx n m` is the list of those keys, and
`gridIdx_nodup` is the only fact about it anyone needs.

Rationale: `docs/reductions.md`. -/

namespace Paralever

/-! ### The index set -/

/-- Row `i` of the grid: `(i,0), …, (i,m-1)`. -/
def rowIdx (i : Nat) : Nat → List (Nat × Nat)
  | 0     => []
  | m + 1 => rowIdx i m ++ [(i, m)]

@[simp] theorem mem_rowIdx {i : Nat} : ∀ {m : Nat} {p : Nat × Nat},
    p ∈ rowIdx i m ↔ p.1 = i ∧ p.2 < m := by
  intro m
  induction m with
  | zero => intro p; simp [rowIdx]
  | succ m ih =>
      intro p
      simp only [rowIdx, List.mem_append, List.mem_singleton, ih]
      constructor
      · rintro (⟨h1, h2⟩ | rfl)
        · exact ⟨h1, by omega⟩
        · exact ⟨rfl, by omega⟩
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_or_ge p.2 m with h | h
        · exact Or.inl ⟨h1, h⟩
        · exact Or.inr (by obtain ⟨x, y⟩ := p; simp_all; omega)

theorem rowIdx_nodup (i : Nat) : ∀ m, (rowIdx i m).Nodup := by
  intro m
  induction m with
  | zero => simp [rowIdx]
  | succ m ih =>
      rw [rowIdx, List.nodup_append]
      refine ⟨ih, by simp, ?_⟩
      intro a ha b hb
      rw [mem_rowIdx] at ha
      simp only [List.mem_singleton] at hb
      subst hb
      intro h; rw [h] at ha; omega

/-- Every `(i, j)` with `i < n` and `j < m`, row by row. Defined by recursion rather than as a
`flatMap` so that both facts below are two-line inductions. -/
def gridIdx : Nat → Nat → List (Nat × Nat)
  | 0,     _ => []
  | n + 1, m => gridIdx n m ++ rowIdx n m

@[simp] theorem mem_gridIdx : ∀ {n m : Nat} {p : Nat × Nat},
    p ∈ gridIdx n m ↔ p.1 < n ∧ p.2 < m := by
  intro n
  induction n with
  | zero => intro m p; simp [gridIdx]
  | succ n ih =>
      intro m p
      simp only [gridIdx, List.mem_append, ih, mem_rowIdx]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨by omega, h2⟩
        · exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_or_ge p.1 n with h | h
        · exact Or.inl ⟨h, h2⟩
        · exact Or.inr ⟨by omega, h2⟩

/-- The grid lists each coordinate once — the only structural fact the validator needs. -/
theorem gridIdx_nodup : ∀ (n m : Nat), (gridIdx n m).Nodup := by
  intro n
  induction n with
  | zero => intro m; simp [gridIdx]
  | succ n ih =>
      intro m
      rw [gridIdx, List.nodup_append]
      refine ⟨ih m, rowIdx_nodup n m, ?_⟩
      intro a ha b hb
      rw [mem_gridIdx] at ha
      rw [mem_rowIdx] at hb
      intro h; rw [h] at ha; omega

/-! ### Row-major linearisation

A grid lives in a flat heap, so coordinates have to be laid out somewhere. These are the only two
facts anyone needs about the usual layout, and proving them here means no example has to reason
about `/` or `%` again: with `gridIdx` the *task* is keyed by `(i,j)`, and `lin` appears only in the
read and write addresses, where it is ordinary arithmetic. -/

/-- Row-major address of `(i,j)` in a grid of row length `w`. -/
def lin (w i j : Nat) : Nat := i * w + j

/-- A coordinate inside an `h × w` grid lands inside `[0, h*w)`. -/
theorem lin_lt {w h i j : Nat} (hi : i < h) (hj : j < w) : lin w i j < h * w := by
  have h1 : (i + 1) * w ≤ h * w := Nat.mul_le_mul_right w hi
  have h2 : i * w + w ≤ h * w := by rw [Nat.succ_mul] at h1; omega
  simp only [lin]; omega

/-- Distinct coordinates get distinct addresses. The one fact that a flat layout costs, proved once
instead of once per example. -/
theorem lin_inj {w i j i' j' : Nat} (hj : j < w) (hj' : j' < w)
    (h : lin w i j = lin w i' j') : i = i' ∧ j = j' := by
  simp only [lin] at h
  rcases Nat.lt_trichotomy i i' with hlt | heq | hgt
  · exfalso
    have h1 : (i + 1) * w ≤ i' * w := Nat.mul_le_mul_right w hlt
    rw [Nat.succ_mul] at h1; omega
  · exact ⟨heq, by subst heq; omega⟩
  · exfalso
    have h1 : (i' + 1) * w ≤ i * w := Nat.mul_le_mul_right w hgt
    rw [Nat.succ_mul] at h1; omega

/-- Recovering the row index from an address. This and `lin_mod` are the bridge to a
linearly-indexed formulation: they say the two keyings describe the same layout. -/
theorem lin_div {w i j : Nat} (hw : 0 < w) (hj : j < w) : lin w i j / w = i := by
  simp only [lin, Nat.mul_comm i w]
  rw [Nat.mul_add_div hw, Nat.div_eq_of_lt hj, Nat.add_zero]

/-- Recovering the column index from an address. -/
theorem lin_mod {w i j : Nat} (hj : j < w) : lin w i j % w = j := by
  simp only [lin, Nat.mul_comm i w]
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]

/-- The form `gridReduce_par_seq_eq`'s `hinj` wants: distinct cells of a row-major grid, offset by a
base address, write distinct locations. -/
theorem lin_ne_of_ne {w base i j i' j' : Nat} (hj : j < w) (hj' : j' < w)
    (hne : i ≠ i' ∨ j ≠ j') : base + lin w i j ≠ base + lin w i' j' := by
  intro h
  obtain ⟨rfl, rfl⟩ := lin_inj hj hj' (Nat.add_left_cancel h)
  rcases hne with h | h <;> exact h rfl

/-! ### A reduction per grid cell

Cell `(i,j)` folds `f` over the values at `locs i j k` for `k < K`, then writes the result to
`out i j`. The accumulator is an ordinary Lean value, so the cell's whole write set is the single
location `out i j` however many cells it reads — which is what lets different cells share their
reads without restriction. -/

/-- The task at cell `(i,j)`: fold over `[0, K)`, then store. -/
def gridCell {α : Type} (K : Nat) (locs : Nat → Nat → Nat → List Loc)
    (f : List Val → α → α) (init : α) (toVal : α → Val) (out : Nat → Nat → Loc)
    (p : Nat × Nat) : ParM Unit :=
  reduceInto (readsCombine (locs p.1 p.2) f) K init toVal (out p.1 p.2)

/-- All `n * m` cells at once: one `par` node, one child per cell. -/
def gridReducePar {α : Type} (n m K : Nat) (locs : Nat → Nat → Nat → List Loc)
    (f : List Val → α → α) (init : α) (toVal : α → Val) (out : Nat → Nat → Loc) :
    ParM (List Unit) := parEach (gridIdx n m) (gridCell K locs f init toVal out)

/-- Sequential counterpart of `gridReducePar`, row-major. -/
def gridReduceSeq {α : Type} (n m K : Nat) (locs : Nat → Nat → Nat → List Loc)
    (f : List Val → α → α) (init : α) (toVal : α → Val) (out : Nat → Nat → Loc) :
    ParM (List Unit) := seqEach (gridIdx n m) (gridCell K locs f init toVal out)

/-- **A grid of independent reductions.** Three obligations, and none of them mentions `/` or `%`:

* `hlocs` — every cell reads inside one shared region `P`. The *same* `P` for every cell, so cells
  may overlap their reads completely (a matrix row read by a whole row of cells).
* `hinj`  — distinct cells write distinct outputs.
* `hout`  — no cell writes into the read region.

Everything else, including the footprint of the inner fold, is discharged generically. -/
theorem gridReduce_par_seq_eq {α : Type} (n m K : Nat) (locs : Nat → Nat → Nat → List Loc)
    (f : List Val → α → α) (init : α) (toVal : α → Val) (out : Nat → Nat → Loc)
    (P : Loc → Prop)
    (hlocs : ∀ i j, i < n → j < m → ∀ k, k < K → ∀ l ∈ locs i j k, P l)
    (hinj : ∀ i j i' j', i < n → j < m → i' < n → j' < m →
      (i ≠ i' ∨ j ≠ j') → out i j ≠ out i' j')
    (hout : ∀ i j, i < n → j < m → ¬ P (out i j)) (σ : State) :
    ParSeqEq (gridReducePar n m K locs f init toVal out)
             (gridReduceSeq n m K locs f init toVal out) σ := by
  refine parEach_par_seq_eq (gridIdx n m) (gridCell K locs f init toVal out)
    (fun _ l => P l) (fun p l => l = out p.1 p.2) (gridIdx_nodup n m) ?_ ?_ ?_ ?_ ?_ σ
  · intro p _ σ'
    exact reduceInto_wellformed _ K init toVal _
      (fun k acc σ'' => readsCombine_wellformed (locs p.1 p.2) f k acc σ'') σ'
  · intro p hp σ'
    rw [mem_gridIdx] at hp
    exact reduceInto_readsWithin _ K init toVal _ P
      (fun k hk acc σ'' =>
        readsCombine_readsWithin (locs p.1 p.2) f k acc σ'' P
          (hlocs p.1 p.2 hp.1 hp.2 k hk)) σ'
  · intro p _ σ'
    exact reduceInto_writesWithin _ K init toVal _
      (fun k acc σ'' => readsCombine_no_writes (locs p.1 p.2) f k acc σ'') σ'
  · intro p q hp hq hpq l hlp hlq
    rw [mem_gridIdx] at hp hq
    refine hinj p.1 p.2 q.1 q.2 hp.1 hp.2 hq.1 hq.2 ?_ (hlp ▸ hlq ▸ rfl)
    by_cases h1 : p.1 = q.1
    · exact Or.inr (fun h2 => hpq (by obtain ⟨a,b⟩ := p; obtain ⟨c,d⟩ := q; simp_all))
    · exact Or.inl h1
  · intro p q hp _ _ l hlp hlq
    rw [mem_gridIdx] at hp
    exact hout p.1 p.2 hp.1 hp.2 (hlp ▸ hlq)

end Paralever
