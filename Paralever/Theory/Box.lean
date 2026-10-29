/-! # The index box, in d dimensions

A loop nest's iteration space, and the two facts anyone needs about it: it lists each point once,
and the row-major layout sends distinct points to distinct addresses. Both are the d-dimensional
form of what `Paralever/Kernels/Grid.lean` proves for two levels — `gridIdx_nodup` and `lin_inj` —
and the two-level cases are gated against those originals in `Test/Box.lean`.

Nothing here mentions `ParM`, `Loc` or a footprint, so this module imports nothing and
`lean Paralever/Theory/Box.lean` type-checks on its own.

Two index types, deliberately:

* **`boxIdx` enumerates points as `List Int`**, because that is what a loop bound is — an
  `affine.for` has `(lo, hi, step)` over `Int`, and `MLIR/Affine.lean`'s `AffMap.apply` consumes
  `List Int`. A level contributes its own list of values (`levelVals`), so the stride never appears
  inside an induction.
* **`linBox` addresses points as `List Nat`**, because an address is a `Loc`. This is `lin`
  generalised, and it is where injectivity lives.

Rationale: `docs/loops.md`. -/

namespace Paralever.Box

/-! ## Enumerating the points -/

/-- The values `for %i = lo to hi step s` takes. Empty for a non-positive step, which is what makes
every function here total without a side condition. -/
def levelVals (lo hi step : Int) : List Int :=
  if step ≤ 0 then []
  else
    let n := if hi ≤ lo then 0 else ((hi - lo + step - 1) / step).toNat
    (List.range n).map (fun k : Nat => lo + step * Int.ofNat k)

/-- Every point of the box, outermost level first, lexicographic. One level per element of `lvls`,
each carrying its own values. -/
def boxIdx : List (List Int) → List (List Int)
  | []         => [[]]
  | vs :: rest => vs.flatMap (fun v => (boxIdx rest).map (fun p => v :: p))

/-- The box over a list of `(lo, hi, step)` bounds — the form a `LoopNest` stores. -/
def boxOf (ranges : List (Int × Int × Int)) : List (List Int) :=
  boxIdx (ranges.map (fun r => levelVals r.1 r.2.1 r.2.2))

/-! ### It lists each point once

`boxIdx_nodup` is the only structural fact `parAll_par_seq_eq_of_indexed_rw` consumes
(`Paralever/Lib/Loop.lean:107`), and the reason it is needed is there: a repeated index would fork
the same task twice, and the write predicate could not tell the copies apart. -/

/-- Prefixing one value preserves distinctness, since `cons` is injective. -/
theorem nodup_map_cons {v : Int} : ∀ {T : List (List Int)}, T.Nodup →
    (T.map (fun p => v :: p)).Nodup := by
  intro T
  induction T with
  | nil => intro _; simp
  | cons t ts ih =>
      intro h
      rw [List.nodup_cons] at h
      simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih h.2⟩
      intro hm
      obtain ⟨t', ht', heq⟩ := List.mem_map.mp hm
      exact h.1 (by cases heq; exact ht')

/-- A point of a prefixed image carries that prefix. -/
theorem head_of_mem_map_cons {v : Int} {T : List (List Int)} {a : List Int}
    (h : a ∈ T.map (fun p => v :: p)) : ∃ t, t ∈ T ∧ a = v :: t := by
  obtain ⟨t, ht, heq⟩ := List.mem_map.mp h
  exact ⟨t, ht, heq.symm⟩

/-- A point of the flattened image carries one of the prefixes. -/
theorem head_of_mem_flatMap {T : List (List Int)} : ∀ {vt : List Int} {b : List Int},
    b ∈ vt.flatMap (fun w => T.map (fun p => w :: p)) → ∃ w, w ∈ vt ∧ ∃ t, t ∈ T ∧ b = w :: t := by
  intro vt
  induction vt with
  | nil => intro b h; simp at h
  | cons w ws ih =>
      intro b h
      rw [List.flatMap_cons, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨t, ht, heq⟩ := head_of_mem_map_cons h
        exact ⟨w, List.mem_cons_self, t, ht, heq⟩
      · obtain ⟨w', hw', t, ht, heq⟩ := ih h
        exact ⟨w', List.mem_cons_of_mem w hw', t, ht, heq⟩

/-- **The box lists each point once**, given each level does — `gridIdx_nodup` in d dimensions. -/
theorem boxIdx_nodup : ∀ (lvls : List (List Int)), (∀ vs ∈ lvls, vs.Nodup) →
    (boxIdx lvls).Nodup := by
  intro lvls
  induction lvls with
  | nil => intro _; simp [boxIdx]
  | cons vs rest ih =>
      intro hall
      have hrest : (boxIdx rest).Nodup := ih (fun l hl => hall l (List.mem_cons_of_mem vs hl))
      have hvs : vs.Nodup := hall vs List.mem_cons_self
      show (vs.flatMap (fun v => (boxIdx rest).map (fun p => v :: p))).Nodup
      clear hall ih
      induction vs with
      | nil => simp
      | cons v vt ihv =>
          rw [List.nodup_cons] at hvs
          rw [List.flatMap_cons, List.nodup_append]
          refine ⟨nodup_map_cons hrest, ihv hvs.2, ?_⟩
          intro a ha b hb
          obtain ⟨t, _, rfl⟩ := head_of_mem_map_cons ha
          obtain ⟨w, hw, t', _, rfl⟩ := head_of_mem_flatMap hb
          intro heq
          exact hvs.1 (by cases heq; exact hw)

/-! ## Addressing the points

`lin w i j = i * w + j` with the row length `w` as the stride. In d levels the stride at a level is
the product of the sizes below it, which is what `prodN ns` is in `linBox`'s `cons` case. -/

/-- Cells in a box of the given sizes. -/
def prodN : List Nat → Nat
  | []      => 1
  | n :: ns => n * prodN ns

/-- Row-major address of a point — `lin` generalised to d levels. -/
def linBox : List Nat → List Nat → Nat
  | _ :: ns, p :: ps => p * prodN ns + linBox ns ps
  | _,       _       => 0

/-- A point is level-wise inside the box. Stated as a `Prop` rather than a `Bool` because it is a
hypothesis of the two theorems below, never something decided. -/
def InBox : List Nat → List Nat → Prop
  | [],      []      => True
  | n :: ns, p :: ps => p < n ∧ InBox ns ps
  | _,       _       => False

/-- **A point of the box lands inside `[0, prodN ns)`** — `lin_lt` in d dimensions, and what makes
the leading index recoverable in `linBox_inj`. -/
theorem linBox_lt : ∀ (ns ps : List Nat), InBox ns ps → linBox ns ps < prodN ns := by
  intro ns
  induction ns with
  | nil =>
      intro ps h
      cases ps with
      | nil => simp [linBox, prodN]
      | cons _ _ => exact absurd h (by simp [InBox])
  | cons n ns ih =>
      intro ps h
      cases ps with
      | nil => exact absurd h (by simp [InBox])
      | cons p ps =>
          obtain ⟨hpn, hrest⟩ := h
          have hr := ih ps hrest
          show p * prodN ns + linBox ns ps < n * prodN ns
          have h1 : (p + 1) * prodN ns ≤ n * prodN ns := Nat.mul_le_mul_right _ hpn
          rw [Nat.succ_mul] at h1
          omega

/-- **Distinct points of the box get distinct addresses.** The one fact a flat layout costs, proved
once here instead of once per kernel — and the soundness of the `outerInjective` clause of the nest
certificate. `lin_inj` is the two-level case. -/
theorem linBox_inj : ∀ (ns ps qs : List Nat), InBox ns ps → InBox ns qs →
    linBox ns ps = linBox ns qs → ps = qs := by
  intro ns
  induction ns with
  | nil =>
      intro ps qs hp hq _
      cases ps <;> cases qs <;> simp_all [InBox]
  | cons n ns ih =>
      intro ps qs hp hq heq
      cases ps with
      | nil => exact absurd hp (by simp [InBox])
      | cons p ps =>
      cases qs with
      | nil => exact absurd hq (by simp [InBox])
      | cons q qs =>
          obtain ⟨hpn, hprest⟩ := hp
          obtain ⟨hqn, hqrest⟩ := hq
          have hpr := linBox_lt ns ps hprest
          have hqr := linBox_lt ns qs hqrest
          show (p :: ps) = (q :: qs)
          simp only [linBox] at heq
          have hpq : p = q := by
            rcases Nat.lt_trichotomy p q with h | h | h
            · exfalso
              have h1 : (p + 1) * prodN ns ≤ q * prodN ns := Nat.mul_le_mul_right _ h
              rw [Nat.succ_mul] at h1
              omega
            · exact h
            · exfalso
              have h1 : (q + 1) * prodN ns ≤ p * prodN ns := Nat.mul_le_mul_right _ h
              rw [Nat.succ_mul] at h1
              omega
          subst hpq
          have hrest : linBox ns ps = linBox ns qs := by omega
          rw [ih ps qs hprest hqrest hrest]

/-- The contrapositive, in the form a disjointness obligation wants. -/
theorem linBox_ne_of_ne {ns ps qs : List Nat} (hp : InBox ns ps) (hq : InBox ns qs)
    (hne : ps ≠ qs) : linBox ns ps ≠ linBox ns qs :=
  fun h => hne (linBox_inj ns ps qs hp hq h)

/-- Offset by a base address, which is how a buffer is placed. -/
theorem base_linBox_ne_of_ne {ns ps qs : List Nat} (base : Nat) (hp : InBox ns ps)
    (hq : InBox ns qs) (hne : ps ≠ qs) : base + linBox ns ps ≠ base + linBox ns qs :=
  fun h => linBox_ne_of_ne hp hq hne (Nat.add_left_cancel h)


/-! ## The box as a list of `Nat` points

`boxIdx` enumerates `Int` points, which is what a `(lo, hi, step)` range produces. The nest
certificate works in `Nat` — `InBox` and `AffAccess.addr` both do — so the box a nest forks over is
enumerated here instead, and **by address**: `boxNat ns` is `unlin ns` over `[0, prodN ns)`.

Enumerating by address is what makes `boxNat_nodup` one inverse lemma rather than a second copy of
`boxIdx_nodup`'s double induction, and it ties the enumeration to `linBox` — the same address
`outerInjective` is about. -/

/-- The point at row-major address `k`. Left inverse of `linBox` below `prodN ns`. -/
def unlin : List Nat → Nat → List Nat
  | [],      _ => []
  | _ :: ns, k => k / prodN ns :: unlin ns (k % prodN ns)

/-- A size list with room for `k` has a positive stride at every level. -/
private theorem prodN_pos_of_lt {n : Nat} {ns : List Nat} {k : Nat}
    (h : k < prodN (n :: ns)) : 0 < prodN ns := by
  rcases Nat.eq_zero_or_pos (prodN ns) with h0 | hp
  · exact absurd h (by simp [prodN, h0])
  · exact hp

/-- **`unlin` inverts `linBox`.** -/
theorem linBox_unlin : ∀ (ns : List Nat) (k : Nat), k < prodN ns → linBox ns (unlin ns k) = k := by
  intro ns
  induction ns with
  | nil => intro k h; simp only [prodN] at h; simp only [linBox]; omega
  | cons n ns ih =>
      intro k h
      have hm : 0 < prodN ns := prodN_pos_of_lt h
      have hmod : k % prodN ns < prodN ns := Nat.mod_lt _ hm
      simp only [unlin, linBox, ih _ hmod]
      rw [Nat.mul_comm]
      exact Nat.div_add_mod k (prodN ns)

/-- **The point at an in-range address is in the box**, which is the hypothesis
`nestIndepB_ww` and `nestIndepB_wr` consume. -/
theorem inBox_unlin : ∀ (ns : List Nat) (k : Nat), k < prodN ns → InBox ns (unlin ns k) := by
  intro ns
  induction ns with
  | nil => intro k _; exact trivial
  | cons n ns ih =>
      intro k h
      have hm : 0 < prodN ns := prodN_pos_of_lt h
      have hmod : k % prodN ns < prodN ns := Nat.mod_lt _ hm
      refine ⟨?_, ih _ hmod⟩
      exact Nat.div_lt_of_lt_mul (by simpa [prodN, Nat.mul_comm] using h)

/-- The box of a nest, as the points of `[0, prodN ns)` in row-major order. -/
def boxNat (ns : List Nat) : List (List Nat) := (List.range (prodN ns)).map (unlin ns)

/-- Every point of `boxNat` is in the box. -/
theorem inBox_of_mem_boxNat {ns : List Nat} {p : List Nat} (h : p ∈ boxNat ns) : InBox ns p := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
  exact inBox_unlin ns k (List.mem_range.mp hk)

/-- A map is injective on a list as soon as something inverts it there. Proved here rather than
imported: `unlin []` is constant, so `unlin ns` is *not* globally injective and
`List.Nodup.map` does not apply -- only the restriction to `[0, prodN ns)` is injective. -/
private theorem nodup_map_of_left_inv {α β : Type} {f : α → β} {g : β → α} :
    ∀ {l : List α}, (∀ a ∈ l, g (f a) = a) → l.Nodup → (l.map f).Nodup := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons a l ih =>
      intro hg h
      rw [List.nodup_cons] at h
      simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih (fun x hx => hg x (List.mem_cons_of_mem a hx)) h.2⟩
      intro hm
      obtain ⟨x, hx, hfx⟩ := List.mem_map.mp hm
      have : a = x := by
        calc a = g (f a) := (hg a List.mem_cons_self).symm
          _ = g (f x) := by rw [hfx]
          _ = x := hg x (List.mem_cons_of_mem a hx)
      exact h.1 (this ▸ hx)

/-- **The box lists each point once** — `idxs.Nodup`, the one structural fact
`parAll_par_seq_eq_of_indexed_rw` consumes. `linBox` is the inverse that proves it. -/
theorem boxNat_nodup (ns : List Nat) : (boxNat ns).Nodup :=
  nodup_map_of_left_inv (g := linBox ns)
    (fun k hk => linBox_unlin ns k (List.mem_range.mp hk)) List.nodup_range

/-- The box has exactly `prodN ns` points, so a nest's thread count is its size product. -/
theorem length_boxNat (ns : List Nat) : (boxNat ns).length = prodN ns := by
  simp [boxNat]

/-- **A forked point followed by a sequential point is a point of the whole box.** What makes
`u ++ p` well-formed when `u` ranges over `boxNat (ns.take d)` and `p` over `boxNat (ns.drop d)`;
with `List.take_append_drop` the two together cover `ns`. -- ref: `docs/loops.md` -/
theorem inBox_append : ∀ (ns ms u p : List Nat), InBox ns u → InBox ms p →
    InBox (ns ++ ms) (u ++ p) := by
  intro ns
  induction ns with
  | nil =>
      intro ms u p hu hp
      cases u with
      | nil      => simpa using hp
      | cons v u => simp only [InBox] at hu
  | cons n ns ih =>
      intro ms u p hu hp
      cases u with
      | nil      => simp only [InBox] at hu
      | cons v u => exact ⟨hu.1, ih ms u p hu.2 hp⟩

/-- **…and splits back off it.** The converse of `inBox_append` for the second half, which is what
recovers the sequential coordinates' own box from a point of the whole one: a nest's certificate is
handed `InBox sizes (u ++ p)` and needs `InBox (sizes.drop d) p` to bound what the inner levels can
add to an address. -- ref: `docs/loops.md` -/
theorem inBox_drop : ∀ (ns ms u p : List Nat), ns.length = u.length →
    InBox (ns ++ ms) (u ++ p) → InBox ms p := by
  intro ns
  induction ns with
  | nil =>
      intro ms u p hlen h
      cases u with
      | nil      => simpa using h
      | cons _ _ => simp at hlen
  | cons n ns ih =>
      intro ms u p hlen h
      cases u with
      | nil      => simp at hlen
      | cons v u => exact ih ms u p (by simpa using hlen) h.2

end Paralever.Box
