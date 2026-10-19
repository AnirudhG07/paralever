import Paralever.Lang.Core
import Paralever.Kernels.Grid

/-! # Premade kernels in the language

The data-parallel shapes of `Kernels/`, written as `ParProg`s. Each carries its own obligation,
proved once at every size, so a program assembled from them needs no proof of its own — that is
what `par_seq_eq_of_kernels` says. -/

namespace Paralever.Lang
open Paralever

namespace ParProg

/-! ## The kernels, in the language

`Kernels/Assign.lean` and `Kernels/Grid.lean` build these shapes directly as `ParM` terms, with a
bespoke validator each. Here they are the same shapes written as `ParProg`, and they need no
validator at all: `footprintOf` is a fold and `wfB` is a `Bool`, so the obligation for any of them
is `decide`.

A loop is Lean-level: `parFor n body` instantiates `body i` for each `i < n`, and every resulting
thread has literal addresses. That is what keeps the footprint syntactic (`§Pointer arithmetic` in
the module header). -/

/-- One thread per index below `n` — the N-ary workhorse all the kernels below are built from. -/
def parFor (n : Nat) (body : Nat → ParProg) : ParProg := .par ((List.range n).map body)

/-- One thread per element of a list, for keys that are not indices (chunks, coordinates, names). -/
def parEach {α : Type} (xs : List α) (body : α → ParProg) : ParProg := .par (xs.map body)

/-- **Elementwise map.** Thread `i` reads `src + i`, applies `f`, writes `dst + i`.
The counterpart of `mapArray`. -/
def mapK (n src dst : Nat) (f : AExp → AExp) : ParProg :=
  parFor n fun i => .seq (.load 0 (src + i)) (.store (dst + i) (f (.reg 0)))

/-- **Broadcast.** Every thread reads the whole of `srcs`; thread `i` writes `dst + i`. Registers
`0 …` receive the inputs in order, so `f` sees them as `R 0, R 1, …`. The counterpart of
`broadcastPar`, and the clearest case of reads overlapping completely. -/
def broadcastK (n : Nat) (srcs : List Loc) (dst : Nat) (f : Nat → AExp) : ParProg :=
  parFor n fun i =>
    .seq (block ((srcs.zipIdx).map (fun p => .load p.2 p.1))) (.store (dst + i) (f i))

/-- The inner loop of a reduction: fold `step` over `locs 0 … locs (K-1)`, accumulating in register
`acc` and staging each value in `tmp`. Both registers are **thread-private**, which is why a whole
reduction writes exactly one cell. -/
def reduceBody (acc tmp : Reg) (locs : Nat → Loc) (step : AExp → AExp → AExp) : Nat → ParProg
  | 0     => .set acc (.lit 0)
  | k + 1 => .seq (reduceBody acc tmp locs step k)
               (.seq (.load tmp (locs k)) (.set acc (step (.reg acc) (.reg tmp))))

/-- **A reduction per output cell.** Thread `p` folds over `K` inputs and stores the result at
`out p`. The counterpart of `reduceArrayPar`: cells may read overlapping inputs, because each writes
only `out p`. -/
def reduceK (n K : Nat) (locs : Nat → Nat → Loc) (step : AExp → AExp → AExp) (out : Nat → Loc) :
    ParProg :=
  parFor n fun p => .seq (reduceBody 0 1 (locs p) step K) (.store (out p) (.reg 0))

/-- **A grid of reductions**, keyed by `(i,j)` rather than by a linear index — the counterpart of
`gridReducePar`, and the reason no address here needs `/` or `%`. -/
def gridK (rows cols K : Nat) (locs : Nat → Nat → Nat → Loc) (step : AExp → AExp → AExp)
    (out : Nat → Nat → Loc) : ParProg :=
  parEach (gridIdx rows cols) fun (ij : Nat × Nat) =>
    .seq (reduceBody 0 1 (locs ij.1 ij.2) step K) (.store (out ij.1 ij.2) (.reg 0))

/-! ### Kernels from machine learning

The shape most ML kernels have — every task reads a window of the input and writes one cell of its
own — is the Bernstein case exactly: reads overlap, writes do not. These are the four that recur
most, and the reason each is here is noted with it. -/

/-- **Elementwise binary op**: `out[i] := f a[i] b[i]`. Add, multiply, subtract, `max` for a ReLU —
the most common kernel there is, and the easiest: footprints are singletons. -/
def zipK (n a b out : Nat) (f : AExp → AExp → AExp) : ParProg :=
  parFor n fun i =>
    block [ .load 0 (a + i), .load 1 (b + i), .store (out + i) (f (.reg 0) (.reg 1)) ]

/-- **1-D convolution / stencil**: `out[i] := Σ_{k<w} coef k * inp[i+k]`.

The showcase. Thread `i` and thread `i+1` read windows overlapping in `w-1` cells, so their read
sets share almost everything while their writes stay disjoint — the case `∗`-disjointness rejects
outright and Bernstein accepts without a word. Convolution, pooling and any sliding-window layer
have this shape. -/
def stencilK (n w inp out : Nat) (coef : Nat → AExp) : ParProg :=
  parFor n fun i =>
    block ([ .set 2 (.lit 0) ]
      ++ (List.range w).map (fun k =>
           block [ .load 0 (inp + i + k), .set 2 (.reg 2 + coef k * .reg 0) ])
      ++ [ .store (out + i) (.reg 2) ])

/-- **Transpose**: `out[j, i] := inp[i, j]`, keyed by the coordinate so no address needs `/` or `%`.
Reads and writes both permute, which is why a region-based check would reject it and a per-pair one
does not. -/
def transposeK (rows cols inp out : Nat) : ParProg :=
  parEach (gridIdx rows cols) fun ij =>
    block [ .load 0 (inp + ij.1 * cols + ij.2), .store (out + ij.2 * rows + ij.1) (.reg 0) ]

/-- **Bias add**: `out[i, j] := inp[i, j] + bias[j]`. Every row reads the *same* bias vector, so the
sharing is along one axis — the broadcast pattern of a linear layer. -/
def biasAddK (rows cols inp bias out : Nat) : ParProg :=
  parEach (gridIdx rows cols) fun ij =>
    block [ .load 0 (inp + ij.1 * cols + ij.2), .load 1 (bias + ij.2),
            .store (out + ij.1 * cols + ij.2) (.reg 0 + .reg 1) ]

/-- **1-D convolution with weights in memory**: `out[i] := Σ_{k<w} wts[k] * inp[i+k]`.

Unlike `stencilK`, whose coefficients are compile-time expressions, this loads them — so *every*
thread reads the whole weight array as well as its own window. Two kinds of sharing at once, and
neither costs anything: `Indep` constrains writes only. -/
def conv1dK (n w inp wts out : Nat) : ParProg :=
  parFor n fun i =>
    block ([ .set 2 (.lit 0) ]
      ++ (List.range w).map (fun k =>
           block [ .load 0 (inp + i + k), .load 1 (wts + k),
                   .set 2 (.reg 2 + .reg 0 * .reg 1) ])
      ++ [ .store (out + i) (.reg 2) ])

/-- **Dense / fully-connected layer**: `out[i] := Σ_j W[i,j] * x[j] + b[i]`.

Thread `i` reads row `i` of `W`, the whole of `x`, and one bias cell. Every thread reads all of
`x` — the broadcast — while writing only `out[i]`. -/
def denseK (rows cols wgt xs bias out : Nat) : ParProg :=
  parFor rows fun i =>
    block ([ .set 2 (.lit 0) ]
      ++ (List.range cols).map (fun j =>
           block [ .load 0 (wgt + i * cols + j), .load 1 (xs + j),
                   .set 2 (.reg 2 + .reg 0 * .reg 1) ])
      ++ [ .load 1 (bias + i), .store (out + i) (.reg 2 + .reg 1) ])

/-- **Outer-product weight update**: `W[i,j] -= lr * e[i] * x[j]`, one SGD step for a dense layer.

The step is `e[i] * x[j] / lrDen`, so the learning rate is `1 / lrDen` — integer division keeps it
inside `Int` without a `Float`. Thread `(i,j)` reads and writes `W[i,j]` *in place* and reads
`e[i]`, `x[j]` which other threads also read. In-place update is fine here precisely because each thread owns its cell — a
region-based check would reject the whole kernel. -/
def outerUpdateK (rows cols wgt errs xs : Nat) (lrDen : Int) : ParProg :=
  parEach (gridIdx rows cols) fun ij =>
    block [ .load 0 (wgt + ij.1 * cols + ij.2), .load 1 (errs + ij.1), .load 2 (xs + ij.2),
            .store (wgt + ij.1 * cols + ij.2)
              (.reg 0 - .div (.reg 1 * .reg 2) (.lit lrDen)) ]

/-! ### Discharging a kernel's obligation at any size

`wfB` decides a *concrete* program. These lemmas lift it to every `n`, so a kernel is proved once
rather than per size. The content is `indepAllB` over a generated list, which is pairwise
independence of the bodies' syntactic footprints. -/

theorem threadFootprints_map {α : Type} (f : α → ParProg) :
    ∀ xs : List α, threadFootprints (xs.map f) = xs.map (fun x => footprintOf (f x)) := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, threadFootprints, ih]

theorem indepAllB_of_pairwise {α : Type} (g : α → Footprint) :
    ∀ xs : List α, (∀ x ∈ xs, ∀ y ∈ xs, x ≠ y → indepB (g x) (g y) = true) → xs.Nodup →
      indepAllB (xs.map g) = true := by
  intro xs
  induction xs with
  | nil => intro _ _; rfl
  | cons x xs ih =>
      intro hp hnd
      rw [List.map_cons, indepAllB, Bool.and_eq_true]
      constructor
      · rw [List.all_eq_true]
        intro b hb
        rw [List.mem_map] at hb
        obtain ⟨y, hy, rfl⟩ := hb
        refine hp x List.mem_cons_self y (List.mem_cons_of_mem x hy) ?_
        intro h; exact (List.nodup_cons.mp hnd).1 (h ▸ hy)
      · exact ih (fun a ha b hb => hp a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb))
          (List.nodup_cons.mp hnd).2

/-- Every thread of a mapped list is well-formed when each body is. -/
theorem wfAllB_map {α : Type} (body : α → ParProg) :
    ∀ xs : List α, (∀ x ∈ xs, wfB (body x) = true) → wfAllB (xs.map body) = true := by
  intro xs
  induction xs with
  | nil => intro _; rfl
  | cons x xs ih =>
      intro h
      rw [List.map_cons, wfAllB, Bool.and_eq_true]
      exact ⟨h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem x hy))⟩

/-- **A `parFor` is well-formed when its bodies are pairwise independent.** The side condition is a
statement about `footprintOf`, i.e. about the syntax — no heap, no `accesses`. -/
theorem wfB_parFor (n : Nat) (body : Nat → ParProg)
    (hbody : ∀ i, i < n → wfB (body i) = true)
    (hdisj : ∀ i j, i < n → j < n → i ≠ j →
      indepB (footprintOf (body i)) (footprintOf (body j)) = true) :
    wfB (parFor n body) = true := by
  rw [parFor, wfB, Bool.and_eq_true, threadFootprints_map]
  constructor
  · refine indepAllB_of_pairwise _ _ ?_ List.nodup_range
    intro i hi j hj hij
    rw [List.mem_range] at hi hj
    exact hdisj i j hi hj hij
  · exact wfAllB_map body _ (fun i hi => hbody i (List.mem_range.mp hi))

/-- **The obligation for a `parFor`, in terms of each thread's read and write lists.** Every kernel
below discharges its obligation through this: give the thread's footprint as two lists, then the
only content left is "distinct threads do not collide", which is arithmetic. -/
theorem wfB_parFor_of_lists (n : Nat) (body : Nat → ParProg)
    (rd wr : Nat → List Loc)
    (hfp : ∀ i, footprintOf (body i) = ⟨rd i, wr i⟩)
    (hbody : ∀ i, i < n → wfB (body i) = true)
    (hww : ∀ i j, i < n → j < n → i ≠ j → ∀ l, l ∈ wr i → l ∈ wr j → False)
    (hwr : ∀ i j, i < n → j < n → i ≠ j → ∀ l, l ∈ wr i → l ∈ rd j → False) :
    wfB (parFor n body) = true := by
  refine wfB_parFor n body hbody ?_
  intro i j hi hj hij
  rw [hfp i, hfp j]
  exact (indepB_iff _ _).mpr
    ⟨hww i j hi hj hij, hwr i j hi hj hij, hwr j i hj hi (fun h => hij h.symm)⟩

/-- **A `parEach` is well-formed when its bodies are pairwise independent.** `wfB_parFor` at an
arbitrary key type. `Nodup` is load-bearing: a repeated key forks the same thread twice. -/
theorem wfB_parEach {α : Type} (xs : List α) (body : α → ParProg) (hnd : xs.Nodup)
    (hbody : ∀ x ∈ xs, wfB (body x) = true)
    (hdisj : ∀ x ∈ xs, ∀ y ∈ xs, x ≠ y →
      indepB (footprintOf (body x)) (footprintOf (body y)) = true) :
    wfB (parEach xs body) = true := by
  rw [parEach, wfB, Bool.and_eq_true, threadFootprints_map]
  exact ⟨indepAllB_of_pairwise _ _ hdisj hnd, wfAllB_map body _ hbody⟩

/-- `wfB_parFor_of_lists` for `parEach`: give the footprint as two lists, and what remains is
index arithmetic. -/
theorem wfB_parEach_of_lists {α : Type} (xs : List α) (body : α → ParProg)
    (rd wr : α → List Loc) (hnd : xs.Nodup)
    (hfp : ∀ x, footprintOf (body x) = ⟨rd x, wr x⟩)
    (hbody : ∀ x ∈ xs, wfB (body x) = true)
    (hww : ∀ x ∈ xs, ∀ y ∈ xs, x ≠ y → ∀ l, l ∈ wr x → l ∈ wr y → False)
    (hwr : ∀ x ∈ xs, ∀ y ∈ xs, x ≠ y → ∀ l, l ∈ wr x → l ∈ rd y → False) :
    wfB (parEach xs body) = true := by
  refine wfB_parEach xs body hnd hbody ?_
  intro x hx y hy hxy
  rw [hfp x, hfp y]
  exact (indepB_iff _ _).mpr
    ⟨hww x hx y hy hxy, hwr x hx y hy hxy, hwr y hy x hx (fun h => hxy h.symm)⟩

/-- The elementwise map's footprint, per thread: one read and one write, both computed. -/
@[simp] theorem mapK_body_footprint (src dst i : Nat) (f : AExp → AExp) :
    footprintOf (.seq (.load 0 (src + i)) (.store (dst + i) (f (.reg 0))))
      = ⟨[src + i], [dst + i]⟩ := rfl

/-- **`mapK` is well-formed whenever its output region misses its input region.** Proved once, for
every `n`; the two side conditions are arithmetic about the layout. -/
theorem wfB_mapK (n src dst : Nat) (f : AExp → AExp)
    (hio : ∀ i j, i < n → j < n → dst + i ≠ src + j) :
    wfB (mapK n src dst f) = true := by
  refine wfB_parFor n _ (fun i _ => rfl) ?_
  intro i j hi hj hij
  rw [mapK_body_footprint, mapK_body_footprint, indepB]
  grind

/-! ### Kernels carry their own obligation

One lemma per kernel, discharged once at every size and `@[simp]`, so a pipeline's `wfB` closes by
`simp` without naming them. `wfB_of_parFree` covers the other kind of phase; between them a program
built from kernels and sequential code needs no proof at all (`par_seq_eq_of_kernels`). -/

/-- `block` on a list of two or more. Stated so proofs need not discharge the pattern-match side
condition of its equation lemma. -/
@[simp] theorem block_cons_cons (a b : ParProg) (rest : List ParProg) :
    block (a :: b :: rest) = .seq a (block (b :: rest)) := rfl

/-- `empty_union`'s mirror. -/
theorem union_empty (f : Footprint) : Footprint.union f Footprint.empty = f := by
  simp [Footprint.union, Footprint.empty]

/-- **A block's footprint splits at any concatenation.** What gives every kernel below its body
footprint. -- ref: `docs/block-ir.md` -/
theorem footprintOf_block_append : ∀ (xs ys : List ParProg),
    footprintOf (block (xs ++ ys))
      = Footprint.union (footprintOf (block xs)) (footprintOf (block ys)) := by
  intro xs
  induction xs with
  | nil => intro ys; rw [List.nil_append]; exact (Footprint.empty_union _).symm
  | cons x xs ih =>
      intro ys
      match xs, ys with
      | [],      []      => simp [block, footprintOf, Footprint.union, Footprint.empty]
      | [],      y :: ys => rw [List.cons_append, List.nil_append]; rfl
      | z :: zs, ys      =>
          -- stated, not rewritten: avoids a rewrite-order question
          have e1 : footprintOf (block ((x :: z :: zs) ++ ys))
              = Footprint.union (footprintOf x) (footprintOf (block ((z :: zs) ++ ys))) := rfl
          have e2 : footprintOf (block (x :: z :: zs))
              = Footprint.union (footprintOf x) (footprintOf (block (z :: zs))) := rfl
          rw [e1, ih, e2, Footprint.union_assoc]

/-- One location per step: `flatMap` collapses to `map`. -/
theorem flatMap_singleton {α β : Type} (f : α → β) : ∀ xs : List α,
    xs.flatMap (fun x => [f x]) = xs.map f := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, List.map_cons, ih, List.singleton_append]

/-- A mapped block's footprint, statement by statement. -/
theorem footprintOf_block_map {α : Type} (g : α → ParProg) (rd wr : α → List Loc)
    (hg : ∀ x, footprintOf (g x) = ⟨rd x, wr x⟩) : ∀ xs : List α,
    footprintOf (block (xs.map g)) = ⟨xs.flatMap rd, xs.flatMap wr⟩ := by
  intro xs
  induction xs with
  | nil => simp [block, footprintOf, Footprint.empty]
  | cons x xs ih =>
      rw [List.map_cons, show (g x :: xs.map g) = [g x] ++ xs.map g from rfl,
        footprintOf_block_append]
      simp only [block, hg x, ih, Footprint.union, List.flatMap_cons]

/-- The footprint of a chain of loads is exactly the locations it loads, and nothing is written. -/
theorem footprintOf_loadChain : ∀ ls : List (Loc × Nat),
    footprintOf (block (ls.map (fun p => ParProg.load p.2 p.1))) = ⟨ls.map Prod.fst, []⟩ := by
  intro ls
  induction ls with
  | nil => rfl
  | cons p ps ih =>
      cases ps with
      | nil => rfl
      | cons q qs =>
          simp only [List.map_cons] at ih ⊢
          rw [block_cons_cons, footprintOf, ih]
          rfl

/-- A chain of loads contains no fork. -/
theorem hasPar_loadChain : ∀ ls : List (Loc × Nat),
    hasPar (block (ls.map (fun p => ParProg.load p.2 p.1))) = false := by
  intro ls
  induction ls with
  | nil => rfl
  | cons p ps ih =>
      cases ps with
      | nil => rfl
      | cons q qs =>
          simp only [List.map_cons] at ih ⊢
          rw [block_cons_cons, hasPar, ih]
          rfl

/-- **`broadcastK` is well-formed whenever no thread writes into the shared input.** One side
condition, and nothing at all about the reads — every thread reads the whole of `srcs`, which is the
point of a broadcast and exactly what `∗`-disjointness would refuse. Proved once, at every `n`. -/
@[simp] theorem wfB_broadcastK (n : Nat) (srcs : List Loc) (dst : Nat) (f : Nat → AExp)
    (hout : ∀ i, i < n → dst + i ∉ srcs) :
    wfB (broadcastK n srcs dst f) = true := by
  have hfp : ∀ i : Nat,
      footprintOf (ParProg.seq (block ((srcs.zipIdx).map (fun p => ParProg.load p.2 p.1)))
        (ParProg.store (dst + i) (f i))) = ⟨srcs, [dst + i]⟩ := by
    intro i
    rw [footprintOf, footprintOf_loadChain, List.zipIdx_map_fst]
    simp [footprintOf, Footprint.union]
  refine wfB_parFor n _ (fun i _ => ?_) ?_
  · show wfB (ParProg.seq _ _) = true
    rw [wfB_seq, Bool.and_eq_true]
    exact ⟨wfB_of_parFree _ (hasPar_loadChain _), rfl⟩
  · grind

/-- `zipK`'s thread footprint: two reads, one write. -/
@[simp] theorem zipK_body_footprint (a b out i : Nat) (f : AExp → AExp → AExp) :
    footprintOf (block [ ParProg.load 0 (a + i), ParProg.load 1 (b + i),
                         ParProg.store (out + i) (f (.reg 0) (.reg 1)) ])
      = ⟨[a + i, b + i], [out + i]⟩ := rfl

/-- **`zipK` is well-formed when the output region misses both inputs.** Proved at every `n`. -/
@[simp] theorem wfB_zipK (n a b out : Nat) (f : AExp → AExp → AExp)
    (hoa : ∀ i j, i < n → j < n → out + i ≠ a + j)
    (hob : ∀ i j, i < n → j < n → out + i ≠ b + j) :
    wfB (zipK n a b out f) = true := by
  refine wfB_parFor_of_lists n _ (fun i => [a + i, b + i]) (fun i => [out + i])
    (fun i => rfl) (fun i _ => rfl) ?_ ?_
  · grind
  · grind

/-! ### The stencil, at any size -/

/-- One thread reads its window and writes `out + i`. -/
theorem stencilK_body_footprint (w inp out i : Nat) (coef : Nat → AExp) :
    footprintOf (block ([ParProg.set 2 (.lit 0)]
      ++ (List.range w).map (fun k =>
           block [ParProg.load 0 (inp + i + k), ParProg.set 2 (.reg 2 + coef k * .reg 0)])
      ++ [ParProg.store (out + i) (.reg 2)]))
      = ⟨(List.range w).map (fun k => inp + i + k), [out + i]⟩ := by
  rw [footprintOf_block_append, footprintOf_block_append,
    footprintOf_block_map _ (fun k => [inp + i + k]) (fun _ => []) (fun _ => rfl)]
  simp [block, footprintOf, Footprint.union, Footprint.empty, flatMap_singleton]

/-- **Well-formed at every size.** Windows may overlap; only the writes are constrained. -/
theorem wfB_stencilK (n w inp out : Nat) (coef : Nat → AExp)
    (hio : ∀ i j, i < n → j < n → ∀ k, k < w → out + i ≠ inp + j + k) :
    wfB (stencilK n w inp out coef) = true := by
  refine wfB_parFor_of_lists n _
    (fun i => (List.range w).map (fun k => inp + i + k)) (fun i => [out + i])
    (fun i => stencilK_body_footprint w inp out i coef) ?_ ?_ ?_
  ·
    intro i _
    refine wfB_block _ (fun s hs => ?_)
    rcases List.mem_append.mp hs with h | h
    · rcases List.mem_append.mp h with h | h
      · rw [List.mem_singleton] at h; rw [h]; rfl
      · obtain ⟨k, _, rfl⟩ := List.mem_map.mp h; rfl
    · rw [List.mem_singleton] at h; rw [h]; rfl
  · grind
  · grind

/-! ### Convolution and dense layer, at any size

`stencilK`'s shape with two loads per step, so the read list is a `flatMap`. -/

/-- One thread reads its window and the whole weight array. -/
theorem conv1dK_body_footprint (w inp wts out i : Nat) :
    footprintOf (block ([ParProg.set 2 (.lit 0)]
      ++ (List.range w).map (fun k =>
           block [ParProg.load 0 (inp + i + k), ParProg.load 1 (wts + k),
                  ParProg.set 2 (.reg 2 + .reg 0 * .reg 1)])
      ++ [ParProg.store (out + i) (.reg 2)]))
      = ⟨(List.range w).flatMap (fun k => [inp + i + k, wts + k]), [out + i]⟩ := by
  rw [footprintOf_block_append, footprintOf_block_append,
    footprintOf_block_map _ (fun k => [inp + i + k, wts + k]) (fun _ => []) (fun _ => rfl)]
  simp [block, footprintOf, Footprint.union, Footprint.empty]

/-- **Well-formed at every size.** No output cell is any thread's input. -/
theorem wfB_conv1dK (n w inp wts out : Nat)
    (hio : ∀ i j, i < n → j < n → ∀ k, k < w →
      out + i ≠ inp + j + k ∧ out + i ≠ wts + k) :
    wfB (conv1dK n w inp wts out) = true := by
  refine wfB_parFor_of_lists n _
    (fun i => (List.range w).flatMap (fun k => [inp + i + k, wts + k])) (fun i => [out + i])
    (fun i => conv1dK_body_footprint w inp wts out i) ?_ ?_ ?_
  · intro i _
    refine wfB_block _ (fun t ht => ?_)
    rcases List.mem_append.mp ht with h | h
    · rcases List.mem_append.mp h with h | h
      · rw [List.mem_singleton] at h; rw [h]; rfl
      · obtain ⟨k, _, rfl⟩ := List.mem_map.mp h; rfl
    · rw [List.mem_singleton] at h; rw [h]; rfl
  · intro i j hi hj hij l hli hlj
    rw [List.mem_singleton] at hli hlj
    exact hij (by grind)
  · intro i j hi hj _ l hli hlj
    rw [List.mem_singleton] at hli
    obtain ⟨k, hk, hl⟩ := List.mem_flatMap.mp hlj
    obtain ⟨h1, h2⟩ := hio i j hi hj k (List.mem_range.mp hk)
    rcases List.mem_cons.mp hl with rfl | hl
    · exact h1 hli.symm
    · rw [List.mem_singleton] at hl; exact h2 (hli.symm.trans hl)

/-- One thread reads row `i` of the weights, all of `xs`, and one bias. -/
theorem denseK_body_footprint (cols wgt xs bias out i : Nat) :
    footprintOf (block ([ParProg.set 2 (.lit 0)]
      ++ (List.range cols).map (fun j =>
           block [ParProg.load 0 (wgt + i * cols + j), ParProg.load 1 (xs + j),
                  ParProg.set 2 (.reg 2 + .reg 0 * .reg 1)])
      ++ [ParProg.load 1 (bias + i), ParProg.store (out + i) (.reg 2 + .reg 1)]))
      = ⟨(List.range cols).flatMap (fun j => [wgt + i * cols + j, xs + j]) ++ [bias + i],
         [out + i]⟩ := by
  rw [footprintOf_block_append, footprintOf_block_append,
    footprintOf_block_map _ (fun j => [wgt + i * cols + j, xs + j]) (fun _ => []) (fun _ => rfl)]
  simp [block, footprintOf, Footprint.union, Footprint.empty]

/-- **Well-formed at every size.** Every thread reads all of `xs`; each writes only `out + i`. -/
theorem wfB_denseK (rows cols wgt xs bias out : Nat)
    (hw : ∀ i j, i < rows → j < rows → ∀ k, k < cols →
      out + i ≠ wgt + j * cols + k ∧ out + i ≠ xs + k)
    (hb : ∀ i j, i < rows → j < rows → out + i ≠ bias + j) :
    wfB (denseK rows cols wgt xs bias out) = true := by
  refine wfB_parFor_of_lists rows _
    (fun i => (List.range cols).flatMap (fun j => [wgt + i * cols + j, xs + j]) ++ [bias + i])
    (fun i => [out + i])
    (fun i => denseK_body_footprint cols wgt xs bias out i) ?_ ?_ ?_
  · intro i _
    refine wfB_block _ (fun t ht => ?_)
    rcases List.mem_append.mp ht with h | h
    · rcases List.mem_append.mp h with h | h
      · rw [List.mem_singleton] at h; rw [h]; rfl
      · obtain ⟨j, _, rfl⟩ := List.mem_map.mp h; rfl
    · rcases List.mem_cons.mp h with rfl | h
      · rfl
      · rw [List.mem_singleton] at h; rw [h]; rfl
  · intro i j hi hj hij l hli hlj
    rw [List.mem_singleton] at hli hlj
    exact hij (by grind)
  · grind

/-! ### The grid-keyed kernels, at any size

All three are `parEach (gridIdx rows cols)` over a straight-line body. Write-map injectivity is a
hypothesis: the caller knows the layout, and at a concrete one it is `lin_ne_of_ne`. -/

/-- **Well-formed at every size.** Reads and writes both permute. -/
theorem wfB_transposeK (rows cols inp out : Nat)
    (hinj : ∀ i j i' j', i < rows → j < cols → i' < rows → j' < cols → (i ≠ i' ∨ j ≠ j') →
      out + j * rows + i ≠ out + j' * rows + i')
    (hio : ∀ i j i' j', i < rows → j < cols → i' < rows → j' < cols →
      out + j * rows + i ≠ inp + i' * cols + j') :
    wfB (transposeK rows cols inp out) = true := by
  refine wfB_parEach_of_lists (gridIdx rows cols) _
    (fun ij => [inp + ij.1 * cols + ij.2]) (fun ij => [out + ij.2 * rows + ij.1])
    (gridIdx_nodup rows cols) (fun _ => rfl) (fun _ _ => rfl) ?_ ?_
  · intro x hx y hy hxy l hlx hly
    rw [mem_gridIdx] at hx hy
    rw [List.mem_singleton] at hlx hly
    refine hinj x.1 x.2 y.1 y.2 hx.1 hx.2 hy.1 hy.2 ?_ (hlx ▸ hly ▸ rfl)
    by_cases h1 : x.1 = y.1
    · exact Or.inr (fun h2 => hxy (Prod.ext h1 h2))
    · exact Or.inl h1
  · intro x hx y hy _ l hlx hly
    rw [mem_gridIdx] at hx hy
    rw [List.mem_singleton] at hlx hly
    exact hio x.1 x.2 y.1 y.2 hx.1 hx.2 hy.1 hy.2 (hlx ▸ hly ▸ rfl)

/-- **Well-formed at every size.** Every row reads the same bias vector. -/
theorem wfB_biasAddK (rows cols inp bias out : Nat)
    (hinj : ∀ i j i' j', i < rows → j < cols → i' < rows → j' < cols → (i ≠ i' ∨ j ≠ j') →
      out + i * cols + j ≠ out + i' * cols + j')
    (hio : ∀ i j i' j', i < rows → j < cols → i' < rows → j' < cols →
      out + i * cols + j ≠ inp + i' * cols + j' ∧ out + i * cols + j ≠ bias + j') :
    wfB (biasAddK rows cols inp bias out) = true := by
  refine wfB_parEach_of_lists (gridIdx rows cols) _
    (fun ij => [inp + ij.1 * cols + ij.2, bias + ij.2])
    (fun ij => [out + ij.1 * cols + ij.2])
    (gridIdx_nodup rows cols) (fun _ => rfl) (fun _ _ => rfl) ?_ ?_
  · intro x hx y hy hxy l hlx hly
    rw [mem_gridIdx] at hx hy
    rw [List.mem_singleton] at hlx hly
    refine hinj x.1 x.2 y.1 y.2 hx.1 hx.2 hy.1 hy.2 ?_ (hlx ▸ hly ▸ rfl)
    by_cases h1 : x.1 = y.1
    · exact Or.inr (fun h2 => hxy (Prod.ext h1 h2))
    · exact Or.inl h1
  · intro x hx y hy _ l hlx hly
    rw [mem_gridIdx] at hx hy
    rw [List.mem_singleton] at hlx
    obtain ⟨h1, h2⟩ := hio x.1 x.2 y.1 y.2 hx.1 hx.2 hy.1 hy.2
    rcases List.mem_cons.mp hly with rfl | hl
    · exact h1 hlx.symm
    · rw [List.mem_singleton] at hl; exact h2 (hlx.symm.trans hl)

/-- **Well-formed at every size.** Thread `(i,j)` reads *and writes* `W[i,j]`: admissible because
each thread owns that cell. -/
theorem wfB_outerUpdateK (rows cols wgt errs xs : Nat) (lrDen : Int)
    (hinj : ∀ i j i' j', i < rows → j < cols → i' < rows → j' < cols → (i ≠ i' ∨ j ≠ j') →
      wgt + i * cols + j ≠ wgt + i' * cols + j')
    (hio : ∀ i j i' j', i < rows → j < cols → i' < rows → j' < cols →
      wgt + i * cols + j ≠ errs + i' ∧ wgt + i * cols + j ≠ xs + j') :
    wfB (outerUpdateK rows cols wgt errs xs lrDen) = true := by
  refine wfB_parEach_of_lists (gridIdx rows cols) _
    (fun ij => [wgt + ij.1 * cols + ij.2, errs + ij.1, xs + ij.2])
    (fun ij => [wgt + ij.1 * cols + ij.2])
    (gridIdx_nodup rows cols) (fun _ => rfl) (fun _ _ => rfl) ?_ ?_
  · intro x hx y hy hxy l hlx hly
    rw [mem_gridIdx] at hx hy
    rw [List.mem_singleton] at hlx hly
    refine hinj x.1 x.2 y.1 y.2 hx.1 hx.2 hy.1 hy.2 ?_ (hlx ▸ hly ▸ rfl)
    by_cases h1 : x.1 = y.1
    · exact Or.inr (fun h2 => hxy (Prod.ext h1 h2))
    · exact Or.inl h1
  · intro x hx y hy hxy l hlx hly
    rw [mem_gridIdx] at hx hy
    rw [List.mem_singleton] at hlx
    obtain ⟨h1, h2⟩ := hio x.1 x.2 y.1 y.2 hx.1 hx.2 hy.1 hy.2
    rcases List.mem_cons.mp hly with rfl | hl
    · refine hinj x.1 x.2 y.1 y.2 hx.1 hx.2 hy.1 hy.2 ?_ hlx.symm
      by_cases h3 : x.1 = y.1
      · exact Or.inr (fun h4 => hxy (Prod.ext h3 h4))
      · exact Or.inl h3
    · rcases List.mem_cons.mp hl with rfl | hl
      · exact h1 hlx.symm
      · rw [List.mem_singleton] at hl; exact h2 (hlx.symm.trans hl)

/-! ### A grid of reductions, at any size

The accumulator is a *register*, so the body writes nothing — which is why a reduction is cheap for
`Indep`. -/

/-- The body reads `locs 0 … locs (K-1)` and writes nothing. -/
theorem reduceBody_footprint (acc tmp : Reg) (locs : Nat → Loc) (step : AExp → AExp → AExp) :
    ∀ K, footprintOf (reduceBody acc tmp locs step K) = ⟨(List.range K).map locs, []⟩ := by
  intro K
  induction K with
  | zero => rfl
  | succ k ih =>
      show footprintOf (.seq (reduceBody acc tmp locs step k) _) = _
      rw [footprintOf, ih]
      simp [footprintOf, Footprint.union, Footprint.empty, List.range_succ]

/-- …and contains no `parallel` block. -/
theorem hasPar_reduceBody (acc tmp : Reg) (locs : Nat → Loc) (step : AExp → AExp → AExp) :
    ∀ K, hasPar (reduceBody acc tmp locs step K) = false := by
  intro K
  induction K with
  | zero => rfl
  | succ k ih =>
      show hasPar (.seq (reduceBody acc tmp locs step k) _) = false
      rw [hasPar, ih]
      rfl

/-- One cell's footprint: its `K` inputs, and the one cell it writes. -/
theorem gridK_body_footprint (K : Nat) (locs : Nat → Nat → Nat → Loc)
    (step : AExp → AExp → AExp) (out : Nat → Nat → Loc) (ij : Nat × Nat) :
    footprintOf (.seq (reduceBody 0 1 (locs ij.1 ij.2) step K) (.store (out ij.1 ij.2) (.reg 0)))
      = ⟨(List.range K).map (locs ij.1 ij.2), [out ij.1 ij.2]⟩ := by
  rw [footprintOf, reduceBody_footprint]
  simp [footprintOf, Footprint.union]

/-- One thread reads its `K` inputs and writes one cell. -/
theorem reduceK_body_footprint (K : Nat) (locs : Nat → Nat → Loc) (step : AExp → AExp → AExp)
    (out : Nat → Loc) (p : Nat) :
    footprintOf (.seq (reduceBody 0 1 (locs p) step K) (.store (out p) (.reg 0)))
      = ⟨(List.range K).map (locs p), [out p]⟩ := by
  rw [footprintOf, reduceBody_footprint]
  simp [footprintOf, Footprint.union]

/-- **Well-formed at every size.** Cells may read overlapping inputs; each writes only `out p`. -/
theorem wfB_reduceK (n K : Nat) (locs : Nat → Nat → Loc) (step : AExp → AExp → AExp)
    (out : Nat → Loc)
    (hinj : ∀ p q, p < n → q < n → p ≠ q → out p ≠ out q)
    (hout : ∀ p q, p < n → q < n → ∀ k, k < K → out p ≠ locs q k) :
    wfB (reduceK n K locs step out) = true := by
  refine wfB_parFor_of_lists n _ (fun p => (List.range K).map (locs p)) (fun p => [out p])
    (fun p => reduceK_body_footprint K locs step out p) ?_ ?_ ?_
  · intro p _
    refine wfB_of_parFree _ ?_
    show hasPar (ParProg.seq (reduceBody 0 1 (locs p) step K) _) = false
    rw [hasPar, hasPar_reduceBody]
    rfl
  · intro p q hp hq hpq l hlp hlq
    rw [List.mem_singleton] at hlp hlq
    exact hinj p q hp hq hpq (hlp ▸ hlq ▸ rfl)
  · intro p q hp hq _ l hlp hlq
    rw [List.mem_singleton] at hlp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hlq
    exact hout p q hp hq k (List.mem_range.mp hk) hlp.symm

/-- **Well-formed at every size.** Output cells distinct, no output an input; reads may overlap
freely. The `ParM` counterpart is `gridReduce_par_seq_eq`. -/
theorem wfB_gridK (rows cols K : Nat) (locs : Nat → Nat → Nat → Loc) (step : AExp → AExp → AExp)
    (out : Nat → Nat → Loc)
    (hinj : ∀ i j i' j', i < rows → j < cols → i' < rows → j' < cols →
      (i ≠ i' ∨ j ≠ j') → out i j ≠ out i' j')
    (hout : ∀ i j i' j', i < rows → j < cols → i' < rows → j' < cols →
      ∀ k, k < K → out i j ≠ locs i' j' k) :
    wfB (gridK rows cols K locs step out) = true := by
  refine wfB_parEach_of_lists (gridIdx rows cols) _
    (fun ij => (List.range K).map (locs ij.1 ij.2)) (fun ij => [out ij.1 ij.2])
    (gridIdx_nodup rows cols) (gridK_body_footprint K locs step out) ?_ ?_ ?_
  · intro ij _
    exact wfB_of_parFree _ (by
      show hasPar (.seq (reduceBody 0 1 (locs ij.1 ij.2) step K) _) = false
      rw [hasPar, hasPar_reduceBody]; rfl)
  · intro x hx y hy hxy l hlx hly
    rw [mem_gridIdx] at hx hy
    rw [List.mem_singleton] at hlx hly
    refine hinj x.1 x.2 y.1 y.2 hx.1 hx.2 hy.1 hy.2 ?_ (hlx ▸ hly ▸ rfl)
    by_cases h1 : x.1 = y.1
    · exact Or.inr (fun h2 => hxy (Prod.ext h1 h2))
    · exact Or.inl h1
  · intro x hx y hy _ l hlx hly
    rw [mem_gridIdx] at hx hy
    rw [List.mem_singleton] at hlx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hly
    exact hout x.1 x.2 y.1 y.2 hx.1 hx.2 hy.1 hy.2 k (List.mem_range.mp hk) hlx.symm

attribute [simp] wfB_mapK

attribute [simp] wfB_of_parFree wfB_seq wfB_label

/-- **The one call.** A program whose parallel blocks are all premade kernels — and whose other
phases contain no fork — is already Par = Seq: supply the per-phase facts (each of which is a
kernel lemma or `wfB_of_parFree`) and nothing else is needed. -/
theorem par_seq_eq_of_kernels {s : ParProg} (h : wfB s = true) (ρ : Regs) (σ : State) :
    ParSeqEq (execPar s ρ) (execSeq s ρ) σ := par_seq_eq h ρ σ
end ParProg

end Paralever.Lang
