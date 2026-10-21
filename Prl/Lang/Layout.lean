import Paralever.Lib.ArrRef
import Paralever.Lib.Render

/-! # `Layout` — declare buffers, not addresses

Declare a buffer with a shape and an initializer; `alloc` places it, so overlap is impossible by
construction (`alloc_pairwise`). `Layout.at "W" [i, j]` subscripts it, `Layout.state` is the initial
heap, and `Layout.nameOf` is the reverse map a diagnostic needs.

Out-of-range subscripting stays total and unchecked, as `ArrRef.loc` is; `inRange` and `covers` are
how you say you meant otherwise. -- ref: `docs/layout.md` -/

namespace Paralever
open Paralever

/-! ### Declarations -/

/-- Cells in a shape: the product of its dimensions, so a scalar (`[]`) is one cell. Written as a
recursion rather than a `foldl` because every lemma below inducts on it. -/
def cells : List Nat → Nat
  | []      => 1
  | d :: ds => d * cells ds

/-- A buffer to be allocated: a name, a shape, and row-major initial contents (missing entries are
`0`). Carries no address — that is the allocator's business. -/
structure Buf where
  name  : String
  /-- `[]` is a scalar, `[n]` a vector, `[r, c]` a matrix, and so on. -/
  shape : List Nat
  init  : List Int := []
  deriving Repr, DecidableEq

/-! ### Initializers

A shape alone is enough: `buf "c" [6]` is six zeros. An `Init` is a function *of the shape*, which
is what lets `ones` take no size and `rows` pad each row to the last dimension. -/

/-- How a buffer's cells start out, given its shape. -/
abbrev Init := List Nat → List Int

/-- All zero — the default, and the same as giving no initializer at all. -/
def zeros : Init := fun _ => []

/-- All one. -/
def ones : Init := fun s => List.replicate (cells s) 1

/-- Every cell `k`. -/
def full (k : Int) : Init := fun s => List.replicate (cells s) k

/-- `0, 1, 2, …` in row-major order. -/
def arange : Init := fun s => (List.range (cells s)).map Int.ofNat

/-- `1` on the main diagonal, `0` elsewhere. Defined for a 2-D shape; anything else is `zeros`. -/
def eye : Init := fun s =>
  match s with
  | [r, c] => (List.range r).flatMap (fun i => (List.range c).map (fun j => if i == j then 1 else 0))
  | _      => []

/-- Contents given explicitly, row-major. Short lists are padded with `0`. -/
def data (xs : List Int) : Init := fun _ => xs

/-- Contents by rows, each padded or truncated to the last dimension. -/
def rows (rs : List (List Int)) : Init := fun s =>
  match s.reverse with
  | c :: _ => (rs.map fun r => r.take c ++ List.replicate (c - r.length) 0).flatten
  | []     => rs.flatten

/-- A bare list of contents reads as `data`, so `buf "CW" [3] [1, 0, -1]` keeps working. -/
instance : Coe (List Int) Init := ⟨data⟩

/-- `buf "C" [6]` (zeros), `buf "W" [2, 6] ones`, `buf "I" [3, 3] eye`,
`buf "W" [2, 3] (rows [[1, 0, -1], [0, 1, 0]])`. -/
def buf (name : String) (shape : List Nat) (init : Init := zeros) : Buf :=
  ⟨name, shape, init shape⟩

/-- Row-major strides, fastest axis last: `[2, 6]` gives `[6, 1]`. -/
def strides : List Nat → List Nat
  | []      => []
  | _ :: ds => cells ds :: strides ds

/-- The row-major offset of a subscript. Total: a missing axis contributes nothing, and an
out-of-range subscript gives an offset past the buffer rather than an error — same choice as
`ArrRef.loc`, for the same reason (`docs/semantics.md`). `inRangeOf` is how you say you meant
otherwise. -/
def offsetOf : List Nat → List Nat → Nat
  | [],      _       => 0
  | _ :: _,  []      => 0
  | _ :: ds, i :: is => cells ds * i + offsetOf ds is

/-- Whether `idx` names a cell of `shape`: one subscript per axis, each inside its dimension. -/
def inRangeOf : List Nat → List Nat → Bool
  | [],      []      => true
  | [],      _ :: _  => false
  | _ :: _,  []      => false
  | d :: ds, i :: is => i < d && inRangeOf ds is

/-- **A subscript in range addresses a cell of the buffer.** This is what lets a layout feed the
`FootprintWithin` combinators of `Theory/Intervals.lean`: a kernel indexing `W[i, j]` with `i`, `j`
in range provably touches only `W`'s range. -/
theorem offsetOf_lt : ∀ (shape idx : List Nat), inRangeOf shape idx = true →
    offsetOf shape idx < cells shape
  | [],      [],      _ => by simp [offsetOf, cells]
  | [],      _ :: _,  h => by simp [inRangeOf] at h
  | _ :: _,  [],      h => by simp [inRangeOf] at h
  | d :: ds, i :: is, h => by
      simp only [inRangeOf, Bool.and_eq_true, decide_eq_true_eq] at h
      have ih := offsetOf_lt ds is h.2
      have hd : i + 1 ≤ d := h.1
      have e : cells (d :: ds) = cells ds * d := by
        simp only [cells]; exact Nat.mul_comm _ _
      rw [offsetOf, e]
      calc cells ds * i + offsetOf ds is
          < cells ds * i + cells ds := by omega
        _ = cells ds * (i + 1)      := (Nat.mul_succ _ _).symm
        _ ≤ cells ds * d            := Nat.mul_le_mul_left _ hd

/-- How many cells the buffer occupies. -/
def Buf.size (b : Buf) : Nat := cells b.shape

/-- The row-major offset of a subscript into `b`. -/
def Buf.offset (b : Buf) (idx : List Nat) : Nat := offsetOf b.shape idx

/-- Whether `idx` names a cell of `b`. -/
def Buf.inRange (b : Buf) (idx : List Nat) : Bool := inRangeOf b.shape idx

/-- `Buf.offset_lt`, in the buffer's own terms. -/
theorem Buf.offset_lt (b : Buf) {idx : List Nat} (h : b.inRange idx = true) :
    b.offset idx < b.size :=
  offsetOf_lt b.shape idx h

/-! ### Allocation -/

/-- A buffer with its assigned base address. -/
structure Placed extends Buf where
  base : Loc
  deriving Repr

/-- The buffer's range, as the `ArrRef` the rest of the library takes. -/
def Placed.ref (p : Placed) : ArrRef := ⟨p.base, p.toBuf.size⟩

/-- **Pack buffers into consecutive ranges**, in declaration order, starting at `start`. Each
buffer begins where the previous one ended, so no two overlap and nothing is assigned by hand. -/
def alloc (start : Loc) : List Buf → List Placed
  | []      => []
  | b :: bs => ⟨b, start⟩ :: alloc (start + b.size) bs

/-- Total cells a declaration list occupies. -/
def total (bs : List Buf) : Nat := bs.foldl (fun a b => a + b.size) 0

/-- Nothing is placed below `start`. -/
theorem alloc_ge (bs : List Buf) (start : Loc) : ∀ p ∈ alloc start bs, start ≤ p.base := by
  induction bs generalizing start with
  | nil => intro p hp; simp [alloc] at hp
  | cons b bs ih =>
      intro p hp
      simp only [alloc, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact Nat.le_refl _
      · exact Nat.le_trans (Nat.le_add_right _ _) (ih (start + b.size) p hp)

/-- **No two allocated buffers overlap** — one ends no later than the other begins. This is exactly
the hypothesis `ArrRef.disjoint_of_range` takes, discharged once for the allocator rather than once
per pair of arrays. -/
theorem alloc_pairwise (bs : List Buf) (start : Loc) :
    (alloc start bs).Pairwise
      (fun p q => p.base + p.toBuf.size ≤ q.base ∨ q.base + q.toBuf.size ≤ p.base) := by
  induction bs generalizing start with
  | nil => simp [alloc]
  | cons b bs ih =>
      simp only [alloc, List.pairwise_cons]
      refine ⟨?_, ih (start + b.size)⟩
      intro q hq
      exact Or.inl (alloc_ge bs (start + b.size) q hq)

/-! ### The layout -/

/-- A placed set of buffers: the declarations plus the addresses the allocator chose. -/
structure Layout where
  bufs : List Placed
  deriving Repr

/-- Allocate a declaration list. `start` leaves room below the arena if something else wants it. -/
def Layout.of (bs : List Buf) (start : Loc := 0) : Layout := ⟨alloc start bs⟩

/-- The named buffer, if it was declared. -/
def Layout.find? (L : Layout) (name : String) : Option Placed :=
  L.bufs.find? (fun p => p.name == name)

/-- The named buffer's range. An undeclared name gets the empty range at `0`, which `wfB`-style
checks and `covers` will reject rather than silently accept. -/
def Layout.ref (L : Layout) (name : String) : ArrRef :=
  (L.find? name).elim ⟨0, 0⟩ Placed.ref

/-- **`L.at "W" [i, j]`** — the location of a cell, by name and subscript. Total, like
`ArrRef.loc`: an out-of-range subscript is an address like any other. -/
def Layout.at (L : Layout) (name : String) (idx : List Nat := []) : Loc :=
  (L.find? name).elim 0 (fun p => p.base + p.toBuf.offset idx)

/-- Whether the subscript names a cell of the named buffer. -/
def Layout.inRange (L : Layout) (name : String) (idx : List Nat) : Bool :=
  (L.find? name).elim false (fun p => p.toBuf.inRange idx)

/-- Cells the layout declares in total. Not the arena's extent when there are gaps — that is `top`. -/
def Layout.size (L : Layout) : Nat := total (L.bufs.map Placed.toBuf)

/-- The lowest address any buffer occupies, and one past the highest. These are the sum of the
buffers' cells only when the buffers are packed: a hand-placed buffer (`at`) can leave a gap, and a
`free` can let two of them share cells. -/
def Layout.bot (L : Layout) : Loc :=
  match L.bufs with
  | []     => 0
  | p :: _ => L.bufs.foldl (fun m q => min m q.base) p.base

def Layout.top (L : Layout) : Loc := L.bufs.foldl (fun m p => max m (p.base + p.toBuf.size)) 0

/-- Every declared buffer lies inside this one range, so a footprint confined to the arena is
confined to the declarations. -/
def Layout.arena (L : Layout) : ArrRef :=
  match L.bufs with
  | [] => ⟨0, 0⟩
  | _  => ⟨L.bot, L.top - L.bot⟩

/-! ### Two facts a proof wants

What lets a layout feed `Theory/Intervals.lean` and `ArrRef.disjoint_of_range`. -/

/-- **A subscript in range addresses a cell of its own buffer** — `FootprintWithin`'s
hypothesis. -/
theorem Layout.at_inRange (L : Layout) {name : String} {idx : List Nat}
    (h : L.inRange name idx = true) : (L.ref name).InRange (L.at name idx) := by
  unfold Layout.inRange Layout.ref Layout.at at *
  cases hf : L.find? name with
  | none => rw [hf] at h; simp at h
  | some p =>
      rw [hf] at h
      simp only [Option.elim] at h ⊢
      refine ⟨Nat.le_add_right _ _, ?_⟩
      have hlt := Buf.offset_lt p.toBuf h
      show p.base + p.toBuf.offset idx < (Placed.ref p).base + (Placed.ref p).len
      simp only [Placed.ref]
      exact Nat.add_lt_add_left hlt p.base

/-- Two named buffers do not overlap, as a `Bool` — `by decide` at a concrete layout. Checked, not
assumed, because a `Layout` can also be written out by hand. -/
def Layout.disjointB (L : Layout) (m n : String) : Bool :=
  let a := L.ref m
  let b := L.ref n
  decide (a.base + a.len ≤ b.base) || decide (b.base + b.len ≤ a.base)

/-- `disjointB` discharges the hypothesis `ArrRef.disjoint_of_range` takes, so the last step of an
array example's independence proof becomes a `decide` on the layout. -/
theorem Layout.disjoint (L : Layout) (m n : String) (h : L.disjointB m n = true) :
    ∀ l, (L.ref m).InRange l → (L.ref n).InRange l → False := by
  apply ArrRef.disjoint_of_range
  simp only [Layout.disjointB, Bool.or_eq_true, decide_eq_true_eq] at h
  exact h

/-! ### Lifetimes

`alloc` places buffers that all live as long as the program. A declaration can also end: `free`
returns the cells to the allocator when the buffer is the most recent one placed, so the next
declaration is placed on them — `buf`/`free` is a stack, and freeing out of order leaves the hole.
Nothing is zeroed and no location goes away, which is why this is an arena and not a heap. There is
no run-time allocator; `Prl.Compile.Lower` decides the same placement from a `.prl` file.
-- ref: `docs/prl.md` § Declaring memory -/

/-- **Where the cursor goes when `p` is freed**: back to the buffer's base when it is the most
recent one placed, and nowhere otherwise — which is what makes `buf`/`free` a stack and what leaves
the hole when it is used out of order. `Prl.Compile.Lower` frees by this rule too. -/
def Placed.release (p : Placed) (next : Loc) : Loc :=
  if p.base + p.toBuf.size == next then p.base else next

/-- A declaration with a lifetime: place a buffer, or end one's. -/
inductive LDecl where
  | buf  : Buf → LDecl
  | free : String → LDecl
  deriving Repr

/-- Buffers placed so far, the names whose lifetime has ended, and where the next buffer goes. -/
structure Arena where
  bufs : List Placed := []
  dead : List String := []
  next : Loc := 0
  deriving Repr

/-- The buffer of this name whose lifetime has not ended. -/
def Arena.find? (A : Arena) (nm : String) : Option Placed :=
  if A.dead.contains nm then none else A.bufs.find? (fun p => p.name == nm)

/-- One declaration. Freeing a name that is not live does nothing: `Prl.Compile.Lower` rejects that
case, and the cursor must not move back over cells a later buffer now owns. -/
def Arena.decl (A : Arena) : LDecl → Arena
  | .buf b   => { A with bufs := A.bufs ++ [⟨b, A.next⟩], next := A.next + b.size }
  | .free nm =>
      match A.find? nm with
      | none   => A
      | some p => { A with dead := nm :: A.dead, next := p.release A.next }

/-- **Place declarations with lifetimes.** `Arena.of [.buf a, .free "a", .buf b]` puts `b` on `a`'s
cells. -/
def Arena.of (ds : List LDecl) (start : Loc := 0) : Arena :=
  ds.foldl Arena.decl { next := start }

/-- The buffers whose lifetime has not ended. -/
def Arena.live (A : Arena) : List Placed := A.bufs.filter (fun p => !A.dead.contains p.name)

/-- Every buffer placed, live or not — a dead one keeps its address, so `Layout.nameOf` can still
say whose cells an address was, and `Layout.state` still lays out what it was initialized with. -/
def Arena.layout (A : Arena) : Layout := ⟨A.bufs⟩

/-! Two invariants carry the placement argument. `Below` is what `free` restores when it lowers the
cursor; `Disjoint` is the statement a user wants. -/

/-- `p.ref.InRange`, as the two inequalities. -/
private theorem Placed.inRange_iff (p : Placed) (l : Loc) :
    p.ref.InRange l ↔ p.base ≤ l ∧ l < p.base + p.toBuf.size := Iff.rfl

/-- The same, for a buffer placed at a given address. -/
private theorem inRange_place (b : Buf) (base l : Loc) :
    (Placed.mk b base).ref.InRange l ↔ base ≤ l ∧ l < base + b.size := Iff.rfl

/-- Every live buffer's cells lie below the cursor. -/
def Arena.Below (A : Arena) : Prop :=
  ∀ p ∈ A.bufs, p.name ∉ A.dead → ∀ l, p.ref.InRange l → l < A.next

/-- No location belongs to two buffers that are live at once. -/
def Arena.Disjoint (A : Arena) : Prop :=
  ∀ p ∈ A.bufs, ∀ q ∈ A.bufs, p.name ∉ A.dead → q.name ∉ A.dead → p.name ≠ q.name →
    ∀ l, p.ref.InRange l → q.ref.InRange l → False

/-- One declaration preserves both. The `free` case is where they interact: the cursor drops to the
freed buffer's base, and what stops a live buffer from being left above it is that such a buffer
would have had to overlap the one just freed. -/
theorem Arena.decl_inv (A : Arena) (d : LDecl) (hb : A.Below) (hd : A.Disjoint) :
    (A.decl d).Below ∧ (A.decl d).Disjoint := by
  cases d with
  | buf b =>
      have hbufs : (A.decl (.buf b)).bufs = A.bufs ++ [⟨b, A.next⟩] := rfl
      have hdead : (A.decl (.buf b)).dead = A.dead := rfl
      have hnext : (A.decl (.buf b)).next = A.next + b.size := rfl
      constructor
      · intro r hr hlive l hl
        rw [hbufs] at hr
        rw [hdead] at hlive
        rw [hnext]
        rcases List.mem_append.1 hr with h | h
        · exact Nat.lt_of_lt_of_le (hb r h hlive l hl) (Nat.le_add_right _ _)
        · have hr' : r = ⟨b, A.next⟩ := by simpa using h
          subst hr'
          exact ((inRange_place b A.next l).1 hl).2
      · intro x hx y hy hlx hly hne l hxl hyl
        rw [hbufs] at hx hy
        rw [hdead] at hlx hly
        rcases List.mem_append.1 hx with hx' | hx'
        · rcases List.mem_append.1 hy with hy' | hy'
          · exact hd x hx' y hy' hlx hly hne l hxl hyl
          · have hy'' : y = ⟨b, A.next⟩ := by simpa using hy'
            subst hy''
            exact absurd (hb x hx' hlx l hxl)
              (Nat.not_lt.mpr ((inRange_place b A.next l).1 hyl).1)
        · have hx'' : x = ⟨b, A.next⟩ := by simpa using hx'
          subst hx''
          rcases List.mem_append.1 hy with hy' | hy'
          · exact absurd (hb y hy' hly l hyl)
              (Nat.not_lt.mpr ((inRange_place b A.next l).1 hxl).1)
          · have hy'' : y = ⟨b, A.next⟩ := by simpa using hy'
            exact hne (by rw [hy''])
  | free nm =>
      cases hf : A.find? nm with
      | none =>
          have h : A.decl (.free nm) = A := by simp [Arena.decl, hf]
          rw [h]; exact ⟨hb, hd⟩
      | some p =>
          have key : p ∈ A.bufs ∧ p.name = nm ∧ nm ∉ A.dead := by
            simp only [Arena.find?] at hf
            split at hf
            · simp at hf
            · rename_i hc
              exact ⟨List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf,
                     by simpa using hc⟩
          obtain ⟨hpm, hpn, hnd⟩ := key
          have hplive : p.name ∉ A.dead := by rw [hpn]; exact hnd
          have hbufs : (A.decl (.free nm)).bufs = A.bufs := by simp [Arena.decl, hf]
          have hdead : (A.decl (.free nm)).dead = nm :: A.dead := by simp [Arena.decl, hf]
          have hnext : (A.decl (.free nm)).next
              = if p.base + p.toBuf.size == A.next then p.base else A.next := by
            simp [Arena.decl, Placed.release, hf]
          constructor
          · intro q hq hlive l hl
            rw [hbufs] at hq
            rw [hdead] at hlive
            have hqn : q.name ≠ nm := fun h => hlive (by simp [h])
            have hqd : q.name ∉ A.dead := fun h => hlive (List.mem_cons_of_mem _ h)
            have hlt : l < A.next := hb q hq hqd l hl
            have hpq : p.name ≠ q.name := by rw [hpn]; exact fun h => hqn h.symm
            rw [hnext]
            split
            · rename_i htop
              have htop' : p.base + p.toBuf.size = A.next := by simpa using htop
              rcases Nat.lt_or_ge l p.base with hlo | hhi
              · exact hlo
              · exact absurd (hd p hpm q hq hplive hqd hpq l
                    ((Placed.inRange_iff p l).2 ⟨hhi, by rw [htop']; exact hlt⟩) hl) not_false
            · exact hlt
          · intro x hx y hy hlx hly hne l hxl hyl
            rw [hbufs] at hx hy
            rw [hdead] at hlx hly
            exact hd x hx y hy (fun h => hlx (List.mem_cons_of_mem _ h))
              (fun h => hly (List.mem_cons_of_mem _ h)) hne l hxl hyl

private theorem Arena.fold_inv (ds : List LDecl) (A : Arena) (hb : A.Below) (hd : A.Disjoint) :
    (ds.foldl Arena.decl A).Below ∧ (ds.foldl Arena.decl A).Disjoint := by
  induction ds generalizing A with
  | nil => exact ⟨hb, hd⟩
  | cons d ds ih =>
      obtain ⟨hb', hd'⟩ := Arena.decl_inv A d hb hd
      exact ih _ hb' hd'

/-- **Two buffers that are live at the same time share no location.** The lifetime-aware
counterpart of `alloc_pairwise`: a `free` lets a later buffer reuse the cells, and this is what
survives it. -/
theorem Arena.live_disjoint (ds : List LDecl) (start : Loc) {p q : Placed}
    (hp : p ∈ (Arena.of ds start).live) (hq : q ∈ (Arena.of ds start).live)
    (hne : p.name ≠ q.name) : ∀ l, p.ref.InRange l → q.ref.InRange l → False := by
  have h := (Arena.fold_inv ds { next := start } (by intro r hr; simp at hr)
              (by intro r hr; simp at hr)).2
  simp only [Arena.of, Arena.live, List.mem_filter] at hp hq
  exact h p hp.1 q hq.1 (by simpa using hp.2) (by simpa using hq.2) hne

/-! ### The heap

Flattened into an `Array` so reads are `O(1)`: `Examples/Language/NeuralNet.lean` records a 40× slowdown from
a heap whose reads walked a structure per access. -/

/-- The declared initial contents, laid out at the assigned addresses. -/
def Layout.data (L : Layout) : Array Val := Id.run do
  let mut a : Array Val := Array.replicate L.top (.int 0)
  for p in L.bufs do
    for (v, k) in p.init.zipIdx do
      if p.base + k < a.size then a := a.set! (p.base + k) (.int v)
  return a

/-- **The initial heap.** Bind to a `def`: the array is built once per call. -/
def Layout.state (L : Layout) : State :=
  let a := L.data
  fun l => a.getD l (.int 0)

/-! ### Reading a layout back -/

/-- Unflatten a row-major offset into a subscript — `offsetOf`'s inverse on cells in range. -/
def unoffset : List Nat → Nat → List Nat
  | [],      _ => []
  | _ :: ds, k =>
      let s := cells ds
      (if s == 0 then 0 else k / s) :: unoffset ds (if s == 0 then 0 else k % s)

/-- The buffer and subscript an address belongs to, as `"W2[0, 3]"`; `none` outside every one. -/
def Layout.nameOf (L : Layout) (l : Loc) : Option String :=
  (L.bufs.find? (fun p => p.base ≤ l && l < p.base + p.toBuf.size)).map fun p =>
    let idx := unoffset p.shape (l - p.base)
    if idx.isEmpty then p.name
    else p.name ++ "[" ++ ", ".intercalate (idx.map toString) ++ "]"

/-- An address as `W2[0, 3]` when it is one, and as a bare number when it is not. -/
def Layout.show (L : Layout) (l : Loc) : String :=
  (L.nameOf l).getD (toString l ++ " (unallocated)")

/-- Footprint locations outside every declared buffer: empty means "stays inside its arrays". -/
def Layout.strayLocs (L : Layout) (f : Footprint) : List Loc :=
  (f.reads ++ f.writes).filter (fun l => (L.nameOf l).isNone)

/-- Whether a footprint stays inside the declared buffers. -/
def Layout.covers (L : Layout) (f : Footprint) : Bool := (L.strayLocs f).isEmpty

/-! ### Printing -/

private def chunk (n : Nat) (xs : List α) : List (List α) := go xs.length xs
where
  /-- Fuel is the list's length, so this is structural. -/
  go : Nat → List α → List (List α)
    | 0,     _  => []
    | _,     [] => []
    | f + 1, ys => ys.take (max n 1) :: go f (ys.drop (max n 1))

/-- One buffer's contents, shaped: a matrix prints a row per line. -/
def Placed.render (p : Placed) (σ : State) : String :=
  let cells := (List.range p.toBuf.size).map (fun k => showVal (σ (p.base + k)))
  let hdr := p.name ++ " " ++ toString p.shape ++ " @" ++ toString p.base ++ "  "
  match p.shape with
  | [_, c] =>
      let rows := (chunk c cells).map (fun r => "[" ++ ", ".intercalate r ++ "]")
      hdr ++ "\n".intercalate (rows.zipIdx.map fun (r, i) =>
        (if i == 0 then "" else String.ofList (List.replicate hdr.length ' ')) ++ r)
  | _ => hdr ++ "[" ++ ", ".intercalate cells ++ "]"

/-- **The heap as the buffers you declared.** -/
def Layout.render (L : Layout) (σ : State) : String :=
  "\n".intercalate (L.bufs.map (fun p => p.render σ))

/-! ### Checking the declaration -/

/-- Names distinct, and no buffer given more initial data than it has room for. -/
def Layout.wfB (L : Layout) : Bool :=
  let names := L.bufs.map (fun p => p.name)
  names.length == names.eraseDups.length &&
    L.bufs.all (fun p => p.init.length ≤ p.toBuf.size)

end Paralever
