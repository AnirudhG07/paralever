import Paralever.Theory.Box
import Paralever.Core.Access

/-! # The loop nest's independence certificate

What `wfB` checks about a *rolled* loop nest, in place of enumerating its iterations. An access is
declared as an affine function of the induction variables; the certificate is a `Bool` over those
declarations, and `mapsDisjoint_sound` turns it into the disjointness `Indep` wants.

Cost is O((#reads + #writes)²) and **independent of the bounds**, which is the whole point: the
unrolled route costs 19 s at a hundred threads (`Examples/Programs/MatMul.lean:267`) and PolyBench
runs to 10⁶.

Packaging: PolCert's generic-theorem-plus-decidable-validator pair (Li, Liang, Feng, TASE 2024),
instantiated for `ParProg` rather than for Coq's polyhedral IR. Independence is Bernstein, so there
is no read-versus-read clause — which is what lets gemm through, since a whole row of iterations
shares `A`'s row.

Rationale: `docs/loops.md`. -/

namespace Paralever.Nest
open Paralever Paralever.Box

/-! ## An access, as declared

One cell per iteration, at an affine function of the induction variables. The coefficients are
`Nat`: a negative stride would need the index to be offset first, and `levelVals` already generates
the values a bound takes, so a loop running downwards is a different value list rather than a
negative coefficient. -/

/-- A declared access: which buffer, and where in it. -/
structure AffAccess where
  /-- the buffer's base address -/
  base   : Loc
  /-- cells in the buffer, so an access can be confined to it -/
  size   : Nat
  /-- one coefficient per loop level, outermost first -/
  coeffs : List Nat
  /-- the constant term, inside the buffer -/
  off    : Nat
  deriving Repr, DecidableEq, Inhabited

/-- `Σ cᵏ · pᵏ`, stopping when either list runs out, so every use is total. -/
def dotN : List Nat → List Nat → Nat
  | c :: cs, p :: ps => c * p + dotN cs ps
  | _,       _       => 0

/-- The row-major stride vector of a box: `[n₁·n₂⋯, n₂⋯, …, 1]`. -/
def strides : List Nat → List Nat
  | []      => []
  | _ :: ns => prodN ns :: strides ns

/-- The cell this access touches at a point. -/
def AffAccess.addr (a : AffAccess) (p : List Nat) : Loc := a.base + a.off + dotN a.coeffs p

/-- The largest point of a box. Coefficients are non-negative, so this is where the address is
largest — which is what makes `inBounds` a one-point check rather than a search. -/
def maxPoint (ns : List Nat) : List Nat := ns.map (fun n => n - 1)

/-! ## The bridge to `linBox`

A row-major access *is* the row-major address, so `linBox_inj` is its injectivity. -/

theorem dotN_strides : ∀ (ns ps : List Nat), dotN (strides ns) ps = linBox ns ps := by
  intro ns
  induction ns with
  | nil => intro ps; cases ps <;> simp [dotN, strides, linBox]
  | cons n ns ih =>
      intro ps
      cases ps with
      | nil => simp [dotN, strides, linBox]
      | cons p ps =>
          simp only [strides, dotN, linBox, ih ps, Nat.mul_comm]

/-! ## Confinement

An address disjointness argument that compares buffers needs each address to be *in* its buffer.

`grind` rather than `omega` throughout: `Loc` is an `abbrev` for `Nat`, and `omega` does not unfold
it when it decides which subterms are integer atoms, so `a.base` is opaque to it and every goal
reads as "no usable constraints". `ArrRef.loc_mem` is the same wall. -- ref: `docs/loops.md` -/

/-- **A point of the box never addresses higher than the box's largest point.** One induction on
the bounds, which `InBox` ties to the point's own length -- so there is no ragged case to handle,
and no monotonicity lemma over mismatched lists. -/
theorem dotN_le_maxPoint : ∀ (ns : List Nat) (cs ps : List Nat), InBox ns ps →
    dotN cs ps ≤ dotN cs (maxPoint ns) := by
  intro ns
  induction ns with
  | nil =>
      intro cs ps h
      cases ps with
      | nil => simp [maxPoint]
      | cons _ _ => exact absurd h (by simp [InBox])
  | cons n ns ih =>
      intro cs ps h
      cases ps with
      | nil => exact absurd h (by simp [InBox])
      | cons p ps =>
      obtain ⟨hpn, hrest⟩ := h
      cases cs with
      | nil => simp [dotN]
      | cons c cs =>
          have hih := ih cs ps hrest
          have hple : p ≤ n - 1 := by omega
          have hmul : c * p ≤ c * (n - 1) := Nat.mul_le_mul_left c hple
          simp only [maxPoint, List.map_cons, dotN]
          have : dotN cs ps ≤ dotN cs ((ns.map (fun n => n - 1))) := by
            simpa [maxPoint] using hih
          omega

/-- **The access stays inside its buffer**, decidably and at one point. -/
def AffAccess.inBounds (sizes : List Nat) (a : AffAccess) : Bool :=
  a.off + dotN a.coeffs (maxPoint sizes) < a.size

theorem addr_lt {sizes : List Nat} {a : AffAccess} {p : List Nat}
    (hb : a.inBounds sizes = true) (hp : InBox sizes p) : a.addr p < a.base + a.size := by
  have hmono : dotN a.coeffs p ≤ dotN a.coeffs (maxPoint sizes) :=
    dotN_le_maxPoint sizes a.coeffs p hp
  have hin : a.off + dotN a.coeffs (maxPoint sizes) < a.size := by
    simpa [AffAccess.inBounds] using hb
  have h2 : a.off + dotN a.coeffs p < a.size :=
    Nat.lt_of_le_of_lt (Nat.add_le_add_left hmono _) hin
  grind [AffAccess.addr]

theorem base_le_addr (a : AffAccess) (p : List Nat) : a.base ≤ a.addr p := by
  grind [AffAccess.addr]

/-- Every cell the access can reach over the box: `base` through
`base + off + dotN coeffs (maxPoint sizes)`. Unconditional — no `inBounds` hypothesis — because
`dotN_le_maxPoint` bounds the offset at every point of the box. This is the bound a rolled nest's
footprint gets, exactly as `ArrRef.cells` is the bound a computed subscript gets.
-- ref: `docs/loops.md` § The footprint fallback -/
def AffAccess.span (sizes : List Nat) (a : AffAccess) : List Loc :=
  (List.range (a.off + dotN a.coeffs (maxPoint sizes) + 1)).map (fun i => a.base + i)

theorem addr_mem_span {sizes : List Nat} {a : AffAccess} {p : List Nat} (hp : InBox sizes p) :
    a.addr p ∈ a.span sizes := by
  have hmono : dotN a.coeffs p ≤ dotN a.coeffs (maxPoint sizes) :=
    dotN_le_maxPoint sizes a.coeffs p hp
  refine List.mem_map.mpr ⟨a.off + dotN a.coeffs p, List.mem_range.mpr (by omega), ?_⟩
  simp only [AffAccess.addr, Nat.add_assoc]

/-! ## Splitting a point into forked and sequential coordinates

A nest forks its `d` outermost levels and runs the remaining levels inside each thread, so a point
of the whole box is `u ++ p` with `u` the forked coordinates. Bernstein's question is asked about
`u` alone: two threads differ in `u`, and each one runs every `p`.

This is what lets gemm through. `C[i,j]` over the box `(i,j,k)` is written by a thousand iterations
of `k`, so it is **not** injective on the whole box — and it does not need to be, because those
thousand iterations all belong to one thread. What it must be is injective in `(i,j)`, which is
`outerInjective` below. -/

/-- `dotN` splits along a split of both lists. -/
theorem dotN_append : ∀ (cs u : List Nat), cs.length = u.length →
    ∀ (ds p : List Nat), dotN (cs ++ ds) (u ++ p) = dotN cs u + dotN ds p := by
  intro cs
  induction cs with
  | nil =>
      intro u hu ds p
      cases u with
      | nil => simp [dotN]
      | cons _ _ => simp at hu
  | cons c cs ih =>
      intro u hu ds p
      cases u with
      | nil => simp at hu
      | cons x xs =>
          have hx : cs.length = xs.length := by simpa using hu
          simp only [List.cons_append, dotN, ih xs hx ds p]
          omega

/-- Zero coefficients contribute nothing, which is what makes a forked access blind to the levels
below it. -/
theorem dotN_replicate_zero : ∀ (z : Nat) (p : List Nat),
    dotN (List.replicate z 0) p = 0 := by
  intro z
  induction z with
  | zero => intro p; simp [dotN]
  | succ z ih =>
      intro p
      cases p with
      | nil => simp [dotN]
      | cons x xs => simp only [List.replicate_succ, dotN, ih xs]; omega

theorem length_strides : ∀ (ns : List Nat), (strides ns).length = ns.length := by
  intro ns
  induction ns with
  | nil => rfl
  | cons _ ns ih => simp [strides, ih]

/-- `InBox` ties the lengths, which is why no lemma here has a ragged case. -/
theorem inBox_length : ∀ (ns ps : List Nat), InBox ns ps → ns.length = ps.length := by
  intro ns
  induction ns with
  | nil =>
      intro ps h
      cases ps with
      | nil => rfl
      | cons _ _ => exact absurd h (by simp [InBox])
  | cons n ns ih =>
      intro ps h
      cases ps with
      | nil => exact absurd h (by simp [InBox])
      | cons p ps => simpa using ih ps h.2

/-- Scaling a coefficient vector scales the whole sum. -/
theorem dotN_map_mul : ∀ (s : Nat) (cs ps : List Nat),
    dotN (cs.map (fun c => c * s)) ps = s * dotN cs ps := by
  intro s cs
  induction cs with
  | nil => intro ps; cases ps <;> simp [dotN]
  | cons c cs ih =>
      intro ps
      cases ps with
      | nil      => simp [dotN]
      | cons p ps =>
          simp only [List.map_cons, dotN, ih ps, Nat.mul_add]
          grind

/-- **How far the sequential levels can move an address**: one more than the largest offset they
add. `1` when the access does not mention them, which is the case `A[i]` and gemm's `C[i,j]` at
`d = 2` are in. -/
def innerSpan (sizes : List Nat) (d : Nat) (a : AffAccess) : Nat :=
  1 + dotN (a.coeffs.drop d) (maxPoint (sizes.drop d))

/-- **Injective in the forked coordinates.** The forked levels walk row-major *scaled past* the
sequential levels' span, so a thread's cells form a block of `innerSpan` consecutive addresses and
two threads own two blocks. At `innerSpan = 1` this is "row-major over the forked levels and blind
to the rest" — `A[i]` accumulated over `j`; at `innerSpan = sizes.drop d`'s span it is row-major
over the whole box — `C[i,j]` written by a nest that forks `i` only. Both are shapes PolyBench is
made of, and one clause decides them. -- ref: `docs/loops.md` § Injective in the forked levels -/
def outerInjective (sizes : List Nat) (d : Nat) (a : AffAccess) : Bool :=
  a.coeffs.length == sizes.length
    && a.coeffs.take d == (strides (sizes.take d)).map (fun c => c * innerSpan sizes d a)

/-- A forked access addresses in blocks: the thread picks the block, the inner point the offset
inside it, and the offset cannot reach the next block. -/
theorem addr_outer {sizes : List Nat} {d : Nat} {a : AffAccess} {u p : List Nat}
    (h : outerInjective sizes d a = true) (hu : InBox (sizes.take d) u)
    (hp : InBox (sizes.drop d) p) :
    a.addr (u ++ p)
      = a.base + a.off + innerSpan sizes d a * linBox (sizes.take d) u
        + dotN (a.coeffs.drop d) p
    ∧ dotN (a.coeffs.drop d) p < innerSpan sizes d a := by
  have hh := (Bool.and_eq_true _ _).mp h
  have hc : a.coeffs.take d = (strides (sizes.take d)).map
      (fun c => c * innerSpan sizes d a) := eq_of_beq hh.2
  have hlen : (a.coeffs.take d).length = u.length := by
    rw [hc, List.length_map, length_strides, List.length_take]
    rw [← inBox_length _ _ hu, List.length_take]
  refine ⟨?_, ?_⟩
  · have hsplit := dotN_append (a.coeffs.take d) u hlen (a.coeffs.drop d) p
    rw [List.take_append_drop] at hsplit
    have hhead : dotN (a.coeffs.take d) u = innerSpan sizes d a * linBox (sizes.take d) u := by
      rw [hc, dotN_map_mul, dotN_strides]
    simp only [AffAccess.addr, hsplit, hhead, Nat.add_assoc]
  · have := dotN_le_maxPoint (sizes.drop d) (a.coeffs.drop d) p hp
    simp only [innerSpan]
    omega

/-- **Distinct blocks are distinct addresses.** The one arithmetic step the clause rests on. -/
theorem mul_add_inj {S x t y t' : Nat} (ht : t < S) (ht' : t' < S)
    (h : S * x + t = S * y + t') : x = y := by
  rcases Nat.lt_trichotomy x y with hlt | heq | hgt
  · have hle : S * (x + 1) ≤ S * y := Nat.mul_le_mul_left S hlt
    rw [Nat.mul_succ] at hle
    omega
  · exact heq
  · have hle : S * (y + 1) ≤ S * x := Nat.mul_le_mul_left S hgt
    rw [Nat.mul_succ] at hle
    omega

/-! ## The certificate

Two clauses, and the two that were tried and rejected are recorded in `docs/loops.md`. The first
accepted two accesses on one buffer when they had the same coefficients and *different* constant
offsets, which accepted `A[i] := A[i-1] + 1`; the second guarded the write-versus-write loop with
`w == w' ||` and so skipped the self-pair, which is the pair that matters most. Both were the same
error: the wrong quantifier. -/

/-- The accesses lie in different buffers. -/
def bufsDisjoint (a b : AffAccess) : Bool :=
  a.base + a.size ≤ b.base || b.base + b.size ≤ a.base

/-- **Independent across distinct threads**: different buffers, or the same access injective in the
forked coordinates — the read-modify-write of one cell by its own thread, which Bernstein permits
and which both `A[i] := A[i] + 1` and gemm's accumulation into `C[i,j]` need. -/
def mapsDisjoint (sizes : List Nat) (d : Nat) (a b : AffAccess) : Bool :=
  bufsDisjoint a b || (a == b && outerInjective sizes d a)

/-- **The certificate is sound.** Two accesses it accepts never touch one cell from two distinct
*threads* — which is exactly the hypothesis `parAll_par_seq_eq_of_indexed_rw` consumes as `hww` and
`hwr`, with the thread's index being the forked prefix. -/
theorem mapsDisjoint_sound {sizes : List Nat} {d : Nat} {a b : AffAccess}
    (ha : a.inBounds sizes = true) (hb : b.inBounds sizes = true)
    (h : mapsDisjoint sizes d a b = true) :
    ∀ u v p q, InBox (sizes.take d) u → InBox (sizes.take d) v → u ≠ v →
      InBox sizes (u ++ p) → InBox sizes (v ++ q) →
      a.addr (u ++ p) ≠ b.addr (v ++ q) := by
  intro u v p q hu hv hne hp hq
  rcases Bool.or_eq_true _ _ |>.mp h with hbuf | hsame
  · -- different buffers: each address is confined to its own, and the two ranges do not meet
    intro heq
    have hpa := addr_lt ha hp
    have hqb := addr_lt hb hq
    have hpa' := base_le_addr a (u ++ p)
    have hqb' := base_le_addr b (v ++ q)
    rcases Bool.or_eq_true _ _ |>.mp hbuf with hlr | hrl
    · have hle : a.base + a.size ≤ b.base := of_decide_eq_true hlr
      grind
    · have hle : b.base + b.size ≤ a.base := of_decide_eq_true hrl
      grind
  · -- the same forked access: the two threads own two blocks, so `linBox_inj` applies
    have hs := Bool.and_eq_true _ _ |>.mp hsame
    obtain ⟨rfl, hoi⟩ : a = b ∧ outerInjective sizes d a = true :=
      ⟨of_decide_eq_true hs.1, hs.2⟩
    have hsplit : sizes.take d ++ sizes.drop d = sizes := List.take_append_drop d sizes
    have hdp : InBox (sizes.drop d) p :=
      inBox_drop _ _ u p (inBox_length _ _ hu) (by rw [hsplit]; exact hp)
    have hdq : InBox (sizes.drop d) q :=
      inBox_drop _ _ v q (inBox_length _ _ hv) (by rw [hsplit]; exact hq)
    obtain ⟨hep, htp⟩ := addr_outer hoi hu hdp
    obtain ⟨heq, htq⟩ := addr_outer hoi hv hdq
    intro hcollide
    rw [hep, heq] at hcollide
    have hkey : innerSpan sizes d a * linBox (sizes.take d) u + dotN (a.coeffs.drop d) p
              = innerSpan sizes d a * linBox (sizes.take d) v + dotN (a.coeffs.drop d) q := by
      grind
    exact hne (linBox_inj _ u v hu hv (mul_add_inj htp htq hkey))

/-! ## Bernstein over a nest's declarations

Write-versus-write and write-versus-read only. A read-versus-read clause would reject gemm, whose
iterations share `A`'s rows and `B`'s columns completely.

**The self-pair is checked, not skipped.** In a parallel nest two *distinct* threads both perform
the same write, so the pair `(W, W)` is the case that matters most; `mapsDisjoint sizes d W W`
reduces to `outerInjective sizes d W`, which is the injectivity the collision would need to
violate. -/

/-- Every declared access is confined to its buffer. Checked, not assumed: a declared footprint the
body escapes would make the certificate vacuous. -/
def boundsOK (sizes : List Nat) (reads writes : List AffAccess) : Bool :=
  reads.all (·.inBounds sizes) && writes.all (·.inBounds sizes)

/-- **One forked point is no fork at all.** `boxNat (sizes.take d)` has `prodN (sizes.take d)`
points, so at `d = 0` — a sequential `affine.for` — there is exactly one thread and Bernstein has
nothing to say. Without this clause every sequential nest would be refused, since a loop-carried
write is not row-major in zero forked levels. -/
theorem inBox_unique_of_prodN_le_one {ns u v : List Nat} (h : prodN ns ≤ 1)
    (hu : InBox ns u) (hv : InBox ns v) : u = v := by
  have h1 := linBox_lt ns u hu
  have h2 := linBox_lt ns v hv
  exact linBox_inj ns u v hu hv (by omega)

/-- **The nest's obligation.** O((#reads + #writes)²) in the declarations, and it never mentions a
point of the box. -/
private def strictIndepB (sizes : List Nat) (d : Nat) (reads writes : List AffAccess) : Bool :=
  boundsOK sizes reads writes
    && writes.all (fun w => writes.all (fun w' => mapsDisjoint sizes d w w'))
    && writes.all (fun w => reads.all (fun r => mapsDisjoint sizes d w r))

def nestIndepB (sizes : List Nat) (d : Nat) (reads writes : List AffAccess) : Bool :=
  prodN (sizes.take d) ≤ 1 || strictIndepB sizes d reads writes

private theorem bounds_of_nestIndepB {sizes : List Nat} {d : Nat} {reads writes : List AffAccess}
    (h : strictIndepB sizes d reads writes = true) :
    (∀ r ∈ reads, r.inBounds sizes = true) ∧ (∀ w ∈ writes, w.inBounds sizes = true) := by
  have hb := (Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp h).1
  have hbo := (Bool.and_eq_true _ _).mp hb.1
  exact ⟨fun r hr => List.all_eq_true.mp hbo.1 r hr,
         fun w hw => List.all_eq_true.mp hbo.2 w hw⟩

/-- **The write-versus-write half**, in the form `parAll_par_seq_eq_of_indexed_rw`'s `hww` wants. -/
theorem nestIndepB_ww {sizes : List Nat} {d : Nat} {reads writes : List AffAccess}
    (h : nestIndepB sizes d reads writes = true) :
    ∀ w ∈ writes, ∀ w' ∈ writes, ∀ u v p q,
      InBox (sizes.take d) u → InBox (sizes.take d) v → u ≠ v →
      InBox sizes (u ++ p) → InBox sizes (v ++ q) → w.addr (u ++ p) ≠ w'.addr (v ++ q) := by
  intro w hw w' hw' u v p q hu hv hne hp hq
  rcases (Bool.or_eq_true _ _).mp h with hone | hrest
  · exact absurd (inBox_unique_of_prodN_le_one (of_decide_eq_true hone) hu hv) hne
  · have hbw := (bounds_of_nestIndepB hrest).2
    have h3 := (Bool.and_eq_true _ _).mp (by exact hrest : strictIndepB sizes d reads writes = true)
    have hb := (Bool.and_eq_true _ _).mp h3.1
    exact mapsDisjoint_sound (hbw w hw) (hbw w' hw')
      (List.all_eq_true.mp (List.all_eq_true.mp hb.2 w hw) w' hw')
      u v p q hu hv hne hp hq

/-- **The write-versus-read half**, in the form `hwr` wants. -/
theorem nestIndepB_wr {sizes : List Nat} {d : Nat} {reads writes : List AffAccess}
    (h : nestIndepB sizes d reads writes = true) :
    ∀ w ∈ writes, ∀ r ∈ reads, ∀ u v p q,
      InBox (sizes.take d) u → InBox (sizes.take d) v → u ≠ v →
      InBox sizes (u ++ p) → InBox sizes (v ++ q) → w.addr (u ++ p) ≠ r.addr (v ++ q) := by
  intro w hw r hr u v p q hu hv hne hp hq
  rcases (Bool.or_eq_true _ _).mp h with hone | hrest
  · exact absurd (inBox_unique_of_prodN_le_one (of_decide_eq_true hone) hu hv) hne
  · have hbs := bounds_of_nestIndepB hrest
    have h3 := (Bool.and_eq_true _ _).mp
      (by exact hrest : strictIndepB sizes d reads writes = true)
    exact mapsDisjoint_sound (hbs.2 w hw) (hbs.1 r hr)
      (List.all_eq_true.mp (List.all_eq_true.mp h3.2 w hw) r hr)
      u v p q hu hv hne hp hq

end Paralever.Nest
