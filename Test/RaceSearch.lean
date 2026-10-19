import Paralever.Search.RaceSearch
import Paralever.Compile.Exec
import Plausible

/-! # Property tests for the counterexample search

Both directions of the standing anti-vacuity obligation (`CLAUDE.md`): equality on independent
programs, a reachable `wrong` on racy ones. Two gates — exhaustive enumeration of small trees, and
random `Prog` trees via Plausible. Both fail the build when they fail: `Testable.check` throws,
whereas the `plausible` tactic would admit the goal instead.

Locations are drawn from `0..3` so collisions are common: over a wide address space almost every
random program is independent and the racy direction never gets exercised. -/

namespace Paralever.Test.RaceSearch
open Paralever Plausible

def σ0 : State := fun _ => .int 0

/-- Has the search found a racing schedule for `p`? `stepBound` is the exact number of steps a full
run takes, so the search cannot miss a race by running out of fuel. -/
def racesFound (p : Prog) : Bool := (findWrong p.stepBound (.run p.toParM σ0)).isSome

/-- The same, with the search aimed by phase 1's conflict locations. -/
def racesFoundGuided (p : Prog) : Bool := (findWrongFrom p.stepBound p.toParM σ0).isSome

/-! ### Exhaustive, for small trees

Depth ≤ 2 over two locations. This is the strongest form of the claim: the Bernstein scan accepts
exactly those programs for which no schedule reaches `wrong`. -/

def enumProgs : Nat → List Prog
  | 0     => [.rd 0, .rd 1, .wr 0 1, .wr 1 1]
  | d + 1 =>
      let small := enumProgs d
      small ++ small.flatMap fun a => small.flatMap fun b => [.seq a b, .par a b]

-- **The scan accepts exactly the race-free programs.** Both directions, every tree of depth ≤ 2.
#guard (enumProgs 2).all fun p => wellFormedB p.toParM σ0 == !racesFound p

-- **Aiming the search loses nothing.** `findWrongGuided` reorders the successors `findWrong`
-- visits, so on every tree of depth ≤ 2 the two agree on whether a race is reachable.
#guard (enumProgs 2).all fun p => racesFound p == racesFoundGuided p

-- And what it returns is a real schedule, not merely a `some`.
#guard (enumProgs 2).all fun p =>
  match findWrongFrom p.stepBound p.toParM σ0 with
  | none   => true
  | some s => (follow (.run p.toParM σ0) s).map Conf.isWrong == some true

-- On an accepted program the threaded run agrees with the sequential one everywhere it looks.
#guard (enumProgs 2).all fun p => !wellFormedB p.toParM σ0 ||
  p.locs.all fun l => runPar p.toParM σ0 l == (runSeq p.toSeq σ0).2 l

/-! ### Random trees -/

private def genLoc : Gen Loc := do
  let n ← Gen.chooseNatLt 0 4 (by decide)
  pure n.val

private def genLeaf : Gen Prog := do
  let l ← genLoc
  let b ← Gen.chooseNatLt 0 2 (by decide)
  pure (if b.val = 0 then .rd l else .wr l 1)

private def genProg : Nat → Gen Prog
  | 0     => genLeaf
  | d + 1 => Gen.oneOf #[genLeaf,
      (do pure (.seq (← genProg d) (← genProg d))),
      (do pure (.par (← genProg d) (← genProg d)))] (by simp)

instance : Arbitrary Prog where
  arbitrary := genProg 3

/-- Shrink to a subtree, so a reported counterexample is the smallest racing tree. -/
instance : Shrinkable Prog where
  shrink
    | .rd _    => []
    | .wr _ _  => []
    | .seq a b => [a, b]
    | .par a b => [a, b]

-- Accepted ⇒ no racing schedule.
#eval Testable.check (∀ p : Prog, wellFormedB p.toParM σ0 = true → racesFound p = false)
  { quiet := true }

-- Rejected ⇒ a racing schedule exists. The completeness direction, tested rather than proved.
#eval Testable.check (∀ p : Prog, wellFormedB p.toParM σ0 = false → racesFound p = true)
  { quiet := true }

-- The aimed search agrees with the blind one on random trees too.
#eval Testable.check (∀ p : Prog, racesFound p = racesFoundGuided p) { quiet := true }

-- Accepted ⇒ threaded and sequential runs agree.
#eval Testable.check (∀ p : Prog, wellFormedB p.toParM σ0 = true →
    (p.locs.all fun l => runPar p.toParM σ0 l == (runSeq p.toSeq σ0).2 l) = true) { quiet := true }

/-! ### From a found schedule to a theorem

The search is untrusted. What it returns is checked by `follow` and promoted by `follow_sound`. -/

/-- `wr 1 7; rd 0` against `wr 0 99`: race-free at the first step, racy at the second. -/
def racy : Prog := .par (.seq (.wr 1 7) (.rd 0)) (.wr 0 99)

/-- info: ([{ left := { reads := [0], writes := [1] }, right := { reads := [], writes := [0] }, conflicts := [0] }], some [0, 0]) -/
#guard_msgs in
#eval diagnose racy σ0

/-- The schedule the search returned, checked by `rfl` and promoted to a run. -/
theorem racy_wrong : Reaches (.run racy.toParM σ0) .wrong :=
  follow_sound [0, 0] _ _ rfl

theorem racy_not_safe : ¬ Safe (.run racy.toParM σ0) := fun h => h racy_wrong

/-- Disjoint writes, shared reads: accepted, as Bernstein requires and `∗` would not. -/
def sharedReads : Prog := .par (.seq (.rd 0) (.wr 2 1)) (.seq (.rd 0) (.wr 3 1))

/-- info: ([], none) -/
#guard_msgs in
#eval diagnose sharedReads σ0

end Paralever.Test.RaceSearch
