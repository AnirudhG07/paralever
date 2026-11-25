import Paralever.Search.RaceSearch

/-! # Running a program under a randomly chosen schedule

`run` executes the canonical order: every fork's children left to right. That order is one member of
`step`'s successor set, and a reader watching it has no way to see that the set has other members.
This module walks the same `step` relation choosing a successor at random, so a run interleaves the
children the way a scheduler would.

The walk is untrusted — it is a random choice, nothing more. What makes its answer mean something is
that it records the `Schedule` it took: `follow_sound` (`Search/RaceSearch.lean`) turns that
schedule into a `Reaches` proof, so every outcome reported here is an outcome of the semantics the
theorems are about, not of a second executor. `walk_follow` below is the link.

The randomness is a seeded generator rather than `IO.rand`, so a surprising outcome can be replayed
by quoting its seed. -- ref: `docs/interleave.md` -/

namespace Paralever

/-! ### The generator

A 64-bit linear congruential generator with Knuth's MMIX constants. The low bits of an LCG are
famously poor, so the index is taken from the high half. -/

/-- The next state of the generator. -/
def lcgNext (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- A run's seed, scrambled so that consecutive seeds do not give correlated first choices. -/
def seedOf (n : Nat) : UInt64 := lcgNext (lcgNext (UInt64.ofNat n + 0x9E3779B97F4A7C15))

/-- The index this generator state picks out of `n` successors. -/
def pick (s : UInt64) (n : Nat) : Nat := (s >>> 33).toNat % max n 1

/-! ### The walk -/

/-- How a walk ended. -/
inductive Halt where
  /-- The configuration has no successors: the program finished, or it is `wrong`. -/
  | done
  /-- The fuel ran out with the program still running. The outcome below is not an outcome. -/
  | outOfFuel
  deriving DecidableEq, Repr

/-- Walk `c` by picking a successor at random until there are none, or the fuel runs out. Returns
the schedule taken, where it ended, and why it stopped. -/
def walk {τ : Type} : Nat → UInt64 → Conf τ → Schedule × Conf τ × Halt
  | 0,        _, c => ([], c, .outOfFuel)
  | fuel + 1, s, c =>
      let succs := stepC c
      if succs.isEmpty then ([], c, .done)
      else
        let s' := lcgNext s
        let i  := pick s' succs.length
        match succs[i]? with
        | some c' => let r := walk fuel s' c'; (i :: r.1, r.2)
        | none    => ([], c, .done)

/-- **The walk's schedule leads where the walk went.** The random choice is untrusted; this is what
makes its answer a fact about the program. With `follow_sound` it gives `Reaches c c'`. -/
theorem walk_follow {τ : Type} (fuel : Nat) (s : UInt64) (c : Conf τ) :
    follow c (walk fuel s c).1 = some (walk fuel s c).2.1 := by
  induction fuel generalizing s c with
  | zero => rfl
  | succ n ih =>
      simp only [walk]
      split
      · rfl
      · next _ =>
          split
          · next c' h => simpa only [follow, h] using ih (lcgNext s) c'
          · rfl

/-- **Every outcome a random walk reports is reachable.** -/
theorem walk_reaches {τ : Type} (fuel : Nat) (s : UInt64) (c : Conf τ) :
    Reaches c (walk fuel s c).2.1 :=
  follow_sound _ _ _ (walk_follow fuel s c)

/-- Run `p` from `σ` under the schedule that `seed` names. -/
def runInterleaved {τ : Type} (fuel : Nat) (seed : Nat) (p : ParM τ) (σ : State) :
    Schedule × Conf τ × Halt :=
  walk fuel (seedOf seed) (.run p σ)

/-- **Interleaved runs land in reachable configurations**, whatever the seed. -/
theorem runInterleaved_reaches {τ : Type} (fuel seed : Nat) (p : ParM τ) (σ : State) :
    Reaches (.run p σ) (runInterleaved fuel seed p σ).2.1 :=
  walk_reaches _ _ _

end Paralever
