import Paralever.Theory.Intervals

/-! # `#parallel_for` — mark a loop parallel, get the independence proof for free

The loop validator: say, per iteration, where its writes land and where its reads land, plus one
disjointness fact between any two distinct iterations, and `parAll_wellformed_of_indexed_rw` returns
`WellFormed`/`ParSeqEq` for the whole loop at any size — no per-example induction.

Reads and writes are bounded *separately* on purpose: iterations may share reads freely, only writes
need checking against everything. `parAll_wellformed_of_indexed_footprint` is the corollary for the
common case where one region covers both. `#parallel_for` itself is pure syntax, expanding to the
`ParM.parAll` term you would otherwise write by hand.

-- ref: PolCert's `bernsteinOK`-and-soundness pair (Li/Liang/Feng TASE'24), instantiated for `ParM`;
`PLAN.md` Milestone 8.
-/

namespace Paralever.Pragma.ParallelFor
open Paralever

/-- **The pragma validator, proved once — the general (shared-reads-allowed) form.** `Pr i`/`Pw i`
bound iteration `i`'s reads/writes *separately*; `hww` is the write/write check, `hwr` the
write/read check (used in both directions since it is stated for every ordered pair `i, j`) — no
read/read check exists, because `Indep` doesn't need one. This is what lets a loop like matmul
(disjoint output cells, overlapping input rows/columns) go through at all. -/
@[simp]
theorem parAll_wellformed_of_indexed_rw {κ τ : Type} (idxs : List κ) (body : κ → ParM τ)
    (Pr Pw : κ → Loc → Prop) (hnodup : idxs.Nodup)
    (hwf : ∀ i ∈ idxs, ∀ σ, WellFormed (body i) σ)
    (hbodyR : ∀ i ∈ idxs, ∀ σ, ReadsWithin (accesses (body i) σ) (Pr i))
    (hbodyW : ∀ i ∈ idxs, ∀ σ, WritesWithin (accesses (body i) σ) (Pw i))
    (hww : ∀ i j, i ∈ idxs → j ∈ idxs → i ≠ j → ∀ l, Pw i l → Pw j l → False)
    (hwr : ∀ i j, i ∈ idxs → j ∈ idxs → i ≠ j → ∀ l, Pw i l → Pr j l → False) :
    ∀ σ, WellFormed (ParM.parAll (idxs.map body)) σ ∧
      ReadsWithin (accesses (ParM.parAll (idxs.map body)) σ) (fun l => ∃ i ∈ idxs, Pr i l) ∧
      WritesWithin (accesses (ParM.parAll (idxs.map body)) σ) (fun l => ∃ i ∈ idxs, Pw i l) := by
  induction idxs with
  | nil => intro σ; exact ⟨WellFormed_parAll_nil σ, ReadsWithin.empty _, WritesWithin.empty _⟩
  | cons i is ih =>
      intro σ
      have hnodup' : is.Nodup := (List.nodup_cons.mp hnodup).2
      have hnotmem : i ∉ is := (List.nodup_cons.mp hnodup).1
      have hwf' : ∀ i' ∈ is, ∀ σ, WellFormed (body i') σ := fun i' hi' => hwf i' (List.mem_cons_of_mem i hi')
      have hbodyR' : ∀ i' ∈ is, ∀ σ, ReadsWithin (accesses (body i') σ) (Pr i') :=
        fun i' hi' => hbodyR i' (List.mem_cons_of_mem i hi')
      have hbodyW' : ∀ i' ∈ is, ∀ σ, WritesWithin (accesses (body i') σ) (Pw i') :=
        fun i' hi' => hbodyW i' (List.mem_cons_of_mem i hi')
      have hww' : ∀ i' j, i' ∈ is → j ∈ is → i' ≠ j → ∀ l, Pw i' l → Pw j l → False :=
        fun i' j hi' hj' => hww i' j (List.mem_cons_of_mem i hi') (List.mem_cons_of_mem i hj')
      have hwr' : ∀ i' j, i' ∈ is → j ∈ is → i' ≠ j → ∀ l, Pw i' l → Pr j l → False :=
        fun i' j hi' hj' => hwr i' j (List.mem_cons_of_mem i hi') (List.mem_cons_of_mem i hj')
      simp only [List.map_cons]
      have hPri : ReadsWithin (accesses (body i) σ) (Pr i) := hbodyR i List.mem_cons_self σ
      have hPwi : WritesWithin (accesses (body i) σ) (Pw i) := hbodyW i List.mem_cons_self σ
      obtain ⟨ihWF, ihR, ihW⟩ := ih hnodup' hwf' hbodyR' hbodyW' hww' hwr' (runSeq (body i) σ).2
      have hwwHead : ∀ l, Pw i l → (∃ j ∈ is, Pw j l) → False := by
        intro l hPwil ⟨j, hjmem, hPwjl⟩
        have hij : i ≠ j := fun h => hnotmem (h ▸ hjmem)
        exact hww i j List.mem_cons_self (List.mem_cons_of_mem i hjmem) hij l hPwil hPwjl
      have hwrHead : ∀ l, Pw i l → (∃ j ∈ is, Pr j l) → False := by
        intro l hPwil ⟨j, hjmem, hPrjl⟩
        have hij : i ≠ j := fun h => hnotmem (h ▸ hjmem)
        exact hwr i j List.mem_cons_self (List.mem_cons_of_mem i hjmem) hij l hPwil hPrjl
      have hrwHead : ∀ l, (∃ j ∈ is, Pw j l) → Pr i l → False := by
        intro l ⟨j, hjmem, hPwjl⟩ hPril
        have hji : j ≠ i := fun h => hnotmem (h ▸ hjmem)
        exact hwr j i (List.mem_cons_of_mem i hjmem) List.mem_cons_self hji l hPwjl hPril
      have hindep : Indep (accesses (body i) σ)
          (accesses (ParM.parAll (is.map body)) (runSeq (body i) σ).2) :=
        indep_of_read_write_confined hPri hPwi ihR ihW hwwHead hwrHead hrwHead
      refine ⟨WellFormed_parAll_cons (body i) (is.map body) σ (hwf i List.mem_cons_self σ)
        hindep ihWF, ?_, ?_⟩
      all_goals
        rw [accesses_parAll_cons]
        simp only [Footprint.union]
      · intro l hl
        rcases List.mem_append.mp hl with hl | hl
        · exact ⟨i, List.mem_cons_self, hPri.apply l hl⟩
        · obtain ⟨j, hjmem, hPrjl⟩ := ihR.apply l hl
          exact ⟨j, List.mem_cons_of_mem i hjmem, hPrjl⟩
      · intro l hl
        rcases List.mem_append.mp hl with hl | hl
        · exact ⟨i, List.mem_cons_self, hPwi.apply l hl⟩
        · obtain ⟨j, hjmem, hPwjl⟩ := ihW.apply l hl
          exact ⟨j, List.mem_cons_of_mem i hjmem, hPwjl⟩

/-- The common-case corollary: one region `P i` covers both reads and writes of iteration `i` — no
shared reads to worry about, so a single disjointness fact `hdisj` suffices (matches `Sort.lean`/
`MergeSort.lean`'s shape, e.g. `TouchesOnly`). A specialization of `parAll_wellformed_of_indexed_rw`
at `Pr = Pw = P`, not a separate induction. -/
@[simp]
theorem parAll_wellformed_of_indexed_footprint {κ τ : Type} (idxs : List κ) (body : κ → ParM τ)
    (P : κ → Loc → Prop) (hnodup : idxs.Nodup)
    (hwf : ∀ i ∈ idxs, ∀ σ, WellFormed (body i) σ)
    (hbody : ∀ i ∈ idxs, ∀ σ, FootprintWithin (accesses (body i) σ) (P i))
    (hdisj : ∀ i j, i ∈ idxs → j ∈ idxs → i ≠ j → ∀ l, P i l → P j l → False) :
    ∀ σ, WellFormed (ParM.parAll (idxs.map body)) σ ∧
      FootprintWithin (accesses (ParM.parAll (idxs.map body)) σ) (fun l => ∃ i ∈ idxs, P i l) := by
  intro σ
  obtain ⟨hWF, hR, hW⟩ := parAll_wellformed_of_indexed_rw idxs body P P hnodup hwf
    (fun i hi σ => (hbody i hi σ).reads) (fun i hi σ => (hbody i hi σ).writes) hdisj hdisj σ
  exact ⟨hWF, hR, hW⟩

/-- The metatheorem, general form: a loop satisfying the read/write-confinement hypotheses reaches
exactly the outcomes its sequential counterpart does. -/
@[simp]
theorem parAll_par_seq_eq_of_indexed_rw {κ τ : Type} (idxs : List κ) (body : κ → ParM τ)
    (Pr Pw : κ → Loc → Prop) (hnodup : idxs.Nodup)
    (hwf : ∀ i ∈ idxs, ∀ σ, WellFormed (body i) σ)
    (hbodyR : ∀ i ∈ idxs, ∀ σ, ReadsWithin (accesses (body i) σ) (Pr i))
    (hbodyW : ∀ i ∈ idxs, ∀ σ, WritesWithin (accesses (body i) σ) (Pw i))
    (hww : ∀ i j, i ∈ idxs → j ∈ idxs → i ≠ j → ∀ l, Pw i l → Pw j l → False)
    (hwr : ∀ i j, i ∈ idxs → j ∈ idxs → i ≠ j → ∀ l, Pw i l → Pr j l → False) (σ : State) :
    ParSeqEq (ParM.parAll (idxs.map body)) (ParM.seqAll (idxs.map body)) σ :=
  parAll_par_seq_eq _ σ
    (parAll_wellformed_of_indexed_rw idxs body Pr Pw hnodup hwf hbodyR hbodyW hww hwr σ).1

/-- The metatheorem, common-case corollary. -/
theorem parAll_par_seq_eq_of_indexed_footprint {κ τ : Type} (idxs : List κ) (body : κ → ParM τ)
    (P : κ → Loc → Prop) (hnodup : idxs.Nodup)
    (hwf : ∀ i ∈ idxs, ∀ σ, WellFormed (body i) σ)
    (hbody : ∀ i ∈ idxs, ∀ σ, FootprintWithin (accesses (body i) σ) (P i))
    (hdisj : ∀ i j, i ∈ idxs → j ∈ idxs → i ≠ j → ∀ l, P i l → P j l → False) (σ : State) :
    ParSeqEq (ParM.parAll (idxs.map body)) (ParM.seqAll (idxs.map body)) σ :=
  parAll_par_seq_eq _ σ
    (parAll_wellformed_of_indexed_footprint idxs body P hnodup hwf hbody hdisj σ).1

/-- `#parallel_for n, body` : run `body 0, body 1, ..., body (n-1)` in parallel — pure sugar for
`ParM.parAll`, carries no proof obligation of its own (checked by `rfl` at each use site). -/
syntax "#parallel_for " term ", " term : term
macro_rules
  | `(#parallel_for $n , $body) => `(ParM.parAll ((List.range $n).map $body))

/-- `#parallel[ p, q, ... ]` : run a fixed, heterogeneous-in-shape (but uniform-in-type) list of
named tasks in parallel — the non-loop generalization of `#parallel_for`, for "these N specific
things are independent" rather than "this range of iterations is." Same pure-sugar status. -/
syntax "#parallel[" term,+ "]" : term
macro_rules
  | `(#parallel[ $ts,* ]) => `(ParM.parAll [ $ts,* ])

end Paralever.Pragma.ParallelFor
