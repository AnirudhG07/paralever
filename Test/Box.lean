import Paralever.Theory.Box
import Paralever.Kernels.Grid

/-! # The index box, gated against the two-level originals

`Paralever/Theory/Box.lean` claims to generalise `gridIdx`/`lin` from two levels to d. These gates
are what makes that a claim rather than a hope: `linBox [h, w]` must agree with `lin w` at every
point of a grid, and the box must enumerate what `gridIdx` enumerates.

Rationale: `docs/loops.md`. -/

namespace Paralever.Test.Box
open Paralever Paralever.Box

/-! ## Enumerating -/

#guard levelVals 0 4 1 == [0, 1, 2, 3]
#guard levelVals 0 10 3 == [0, 3, 6, 9]
#guard levelVals 2 7 2 == [2, 4, 6]
#guard levelVals 0 0 1 == []
#guard levelVals 5 1 1 == []
-- a non-positive step is empty rather than divergent, which is what keeps every function total
#guard levelVals 0 4 0 == []
#guard levelVals 0 4 (-1) == []

#guard boxIdx [] == [[]]
#guard boxIdx [[0, 1], [0, 1, 2]] == [[0,0], [0,1], [0,2], [1,0], [1,1], [1,2]]
#guard (boxIdx [levelVals 0 4 1, levelVals 0 4 1]).length == 16
#guard (boxIdx [levelVals 0 10 1, levelVals 0 10 1]).length == 100

#guard boxOf [(0, 3, 1)] == [[0], [1], [2]]
#guard boxOf [(0, 2, 1), (0, 2, 1)] == [[0,0], [0,1], [1,0], [1,1]]
#guard (boxOf [(0, 8, 1), (0, 8, 1), (0, 8, 1)]).length == 512

/-! ### Against `gridIdx`

The same index set in the same order, so `gridIdx`'s own users keep their meaning. -/

/-- `gridIdx`'s pairs, as the box's points. -/
private def gridAsBox (n m : Nat) : List (List Int) :=
  (gridIdx n m).map (fun p => [(p.1 : Int), (p.2 : Int)])

#guard gridAsBox 2 3 == boxOf [(0, 2, 1), (0, 3, 1)]
#guard gridAsBox 4 4 == boxOf [(0, 4, 1), (0, 4, 1)]
#guard gridAsBox 3 5 == boxOf [(0, 3, 1), (0, 5, 1)]
#guard gridAsBox 1 7 == boxOf [(0, 1, 1), (0, 7, 1)]
#guard gridAsBox 7 1 == boxOf [(0, 7, 1), (0, 1, 1)]

/-! ## Addressing

`lin w i j = i * w + j`, so the stride at the outer level is the row length and the box is
`[h, w]`. -/

#guard prodN [] == 1
#guard prodN [3, 4, 5] == 60
#guard prodN [1000, 1000] == 1000000

#guard linBox [3, 4, 5] [1, 2, 3] == 33        -- 1*20 + 2*5 + 3
#guard linBox [1000, 1000] [7, 9] == 7009

-- **The two-level case is `lin`**, at every point of a 6x7 and an 8x8 grid.
#guard (List.range 6).all (fun i => (List.range 7).all (fun j =>
          linBox [6, 7] [i, j] == lin 7 i j))
#guard (List.range 8).all (fun i => (List.range 8).all (fun j =>
          linBox [8, 8] [i, j] == lin 8 i j))

-- and the bound is `lin_lt`'s
#guard (List.range 6).all (fun i => (List.range 7).all (fun j =>
          linBox [6, 7] [i, j] < prodN [6, 7]))

-- Three levels address a cube without collision: the fact `linBox_inj` states, checked
-- concretely at 4x4x4 so a change of definition is caught even if the proof still goes through.
#guard ((boxOf [(0,4,1), (0,4,1), (0,4,1)]).map
          (fun p => linBox [4, 4, 4] (p.map Int.toNat))).eraseDups.length == 64

/-! ## The theorems, used

A proof that only ever appears in its own file is not known to be usable. -/

example : InBox [3, 4] [1, 2] := ⟨by omega, by omega, trivial⟩
example : InBox [1000, 1000] [999, 0] := ⟨by omega, by omega, trivial⟩

example : linBox [3, 4] [1, 2] < prodN [3, 4] :=
  linBox_lt [3, 4] [1, 2] ⟨by omega, by omega, trivial⟩

example : linBox [5, 5] [1, 2] ≠ linBox [5, 5] [2, 1] :=
  linBox_ne_of_ne ⟨by omega, by omega, trivial⟩ ⟨by omega, by omega, trivial⟩ (by simp)

/-- Offset by a buffer's base, which is the form a placed buffer needs. -/
example : 64 + linBox [5, 5] [1, 2] ≠ 64 + linBox [5, 5] [2, 1] :=
  base_linBox_ne_of_ne 64 ⟨by omega, by omega, trivial⟩ ⟨by omega, by omega, trivial⟩ (by simp)

/-- The injectivity fact at symbolic sizes, so nothing here depends on a literal. -/
example (n m i j i' j' : Nat) (hi : i < n) (hj : j < m) (hi' : i' < n) (hj' : j' < m)
    (h : linBox [n, m] [i, j] = linBox [n, m] [i', j']) : [i, j] = [i', j'] :=
  linBox_inj [n, m] [i, j] [i', j'] ⟨hi, hj, trivial⟩ ⟨hi', hj', trivial⟩ h

/-- Nodup at symbolic levels: the hypothesis is per level, so a box of ranges always satisfies it
once each level's values are distinct. -/
example (a b : List Int) (ha : a.Nodup) (hb : b.Nodup) : (boxIdx [a, b]).Nodup := by
  refine boxIdx_nodup [a, b] ?_
  intro vs hvs
  rcases List.mem_cons.mp hvs with rfl | hvs
  · exact ha
  · rcases List.mem_cons.mp hvs with rfl | hvs
    · exact hb
    · simp at hvs

/-! ## The box as `Nat` points, enumerated by address

`boxNat` is what a nest forks over, and it is `unlin` over `[0, prodN ns)` rather than a second
`flatMap` nest — so `linBox` is its inverse and the nodup proof is that one fact. Gated here against
`boxOf`, which enumerates the same points over `Int`. -/

#guard unlin [4, 4] 0 == [0, 0]
#guard unlin [4, 4] 5 == [1, 1]
#guard unlin [4, 4] 15 == [3, 3]
#guard unlin [2, 3, 4] 23 == [1, 2, 3]

#guard boxNat [] == [[]]
#guard boxNat [2, 3] == [[0, 0], [0, 1], [0, 2], [1, 0], [1, 1], [1, 2]]
#guard (boxNat [4, 4, 4]).length == 64
#guard (boxNat [10, 10]).length == 100

-- a zero-sized level gives an empty box rather than a division by zero
#guard boxNat [0] == []
#guard boxNat [3, 0] == []

-- `linBox` inverts the enumeration pointwise, which is what `boxNat_nodup` rests on
#guard (boxNat [4, 4]).map (linBox [4, 4]) == List.range 16
#guard (boxNat [2, 3, 4]).map (linBox [2, 3, 4]) == List.range 24

-- distinctness, computed rather than assumed
#guard (boxNat [3, 3]).eraseDups.length == 9
#guard (boxNat [2, 2, 2]).eraseDups.length == 8

-- the two enumerators agree: `boxOf` over `Int`, `boxNat` over `Nat`
#guard (boxNat [2, 3]).map (fun p => p.map Int.ofNat) == boxOf [(0, 2, 1), (0, 3, 1)]
#guard (boxNat [4, 4]).map (fun p => p.map Int.ofNat) == boxOf [(0, 4, 1), (0, 4, 1)]

-- and `boxNat` has `prodN` points, so a nest's thread count is its size product
example : (boxNat [1000, 1000]).length = 1000000 := length_boxNat [1000, 1000]
example : (boxNat [4, 4]).Nodup := boxNat_nodup [4, 4]
example : ∀ p ∈ boxNat [4, 4], InBox [4, 4] p := fun _ h => inBox_of_mem_boxNat h

end Paralever.Test.Box
