import Lang.Compile.Parse
import Lang.Compile.Lower
import Lang.Core.Analysis
import Paralever.Compile.ExecArr
import Bench.Time

/-! # A thousand lines of nothing in particular

`Bench/Threads.lean` measures one shape — a matrix multiply written as a `;`-chain — which is the
best case for a parallelizer: every output cell is independent of every other and the units are
all the same size. This file measures the opposite.

The program is `Bench/chaos.prl`: a thousand lines that do many unrelated things in
sequence — index arithmetic, a branch per cell, a four-point stencil, an odd-even sorting network,
serial folds that carry a dependence and so cannot be parallelized at all, and a few matrix
multiplies buried in the middle. It is written as a file, in the surface language, and nothing in
it is parallel. Finding the threads is `autoPar`'s job.

Its three `const` lines are the parameters. This file rewrites only those three lines, so the
program's *shape* — how many statements, how many stages, which stage reads which buffer — is
fixed across every measurement, and what changes is how much work each line stands for.

Three runs are compared at each parameter: the file as written; `autoPar` over every statement in
it, with the region markers stripped first so the planner sees one flat list; and `autoPar` applied
only inside the `{ … } :: "name"` regions the file marks. The regions are where the parallelism is
— the matrix multiplies, the stencils, the branch sweeps — so the third run pays for planning only
where planning can repay it. Rationale: `docs/bench.md`. -/

namespace Paralever.Bench.Chaos
open Paralever Paralever.Lang

/-! ## The file, retuned

The source of truth is the `.prl` file, not this module. The only thing substituted is the value
on each of the three `const` lines; every other line is passed through untouched. -/

def chaosPath : String := "Bench/chaos.prl"

/-- The file with `n`, `m` and `d` set. A line is rewritten only if it is exactly the declaration
of one of the three, so a `const` the file adds later is left alone. -/
def retune (n m d : Nat) (src : String) : String :=
  String.intercalate "\n" <| (src.splitOn "\n").map fun l =>
    if l.startsWith "const n = " then s!"const n = {n}"
    else if l.startsWith "const m = " then s!"const m = {m}"
    else if l.startsWith "const d = " then s!"const d = {d}"
    else l

def source (n m d : Nat) : IO String := do
  pure (retune n m d (← IO.FS.readFile chaosPath))

/-- Memory operations and register assignments in the lowered program. Exact except at an `if`,
where only one arm runs and the larger of the two is counted — the arms here differ by at most one
statement, so the figure is the executed count to within the number of branches. -/
partial def instrs : ParProg → Nat
  | .load _ _      => 1
  | .store _ _     => 1
  | .set _ _       => 1
  | .loadAt _ _ _  => 1
  | .storeAt _ _ _ => 1
  | .seq a b       => instrs a + instrs b
  | .par cs        => cs.foldl (fun k c => k + instrs c) 0
  | .label _ b     => instrs b
  | .ifElse _ t e  => 1 + max (instrs t) (instrs e)
  | _              => 0

/-- Children summed over every fork in the program. -/
partial def forks : ParProg → Nat
  | .par cs    => cs.length + cs.foldl (fun k c => k + forks c) 0
  | .seq a b   => forks a + forks b
  | .label _ b => forks b
  | .ifElse _ t e => forks t + forks e
  | _          => 0

/-- The program with its region markers removed. `flatten` stops at a `label`, so to the planner a
region is one opaque statement and `autoParTuned` applied to the file as it stands never looks
inside one. Removing the markers is what the planner saw before regions existed, and it is the
third run compared below. (`chaos.prl` has no fork, so the only labels in it are its regions.) -/
partial def unmark : ParProg → ParProg
  | .label _ s => unmark s
  | .seq a b   => .seq (unmark a) (unmark b)
  | p          => p

/-- Every cell of the final heap summed: forces the run, and catches a rewrite that changed it. -/
def checksum (a : AState) : Int :=
  (List.range a.size).foldl
    (fun (acc : Int) i => match a.get i with | .int v => acc + v | _ => acc) 0

def compileAt (n m d : Nat) : IO (Except String Compiled) := do
  match parse (← source n m d) with
  | .error e => pure (.error (toString (repr e)))
  | .ok f    => match compileOne f "" with
    | .error e => pure (.error (toString (repr e)))
    | .ok c    => pure (.ok c)

private def pad (w : Nat) (s : String) : String := "".pushn ' ' (w - min w s.length) ++ s

private def ratio (a b : Nat) : String :=
  if b == 0 then "--"
  else s!"{a / b}.{(a * 100 / b) % 100 / 10}{(a * 100 / b) % 10}x"

def banner : String :=
  "".pushn ' ' 36 ++ pad 34 "-- autopar, markers off --  " ++ pad 34 "--- marked regions only ---  "

def header : String :=
  pad 5 "n" ++ pad 5 "m" ++ pad 6 "d" ++ pad 11 "instrs" ++ pad 9 "seq ms"
    ++ pad 8 "forks" ++ pad 9 "plan ms" ++ pad 8 "run ms" ++ pad 9 "speedup"
    ++ pad 8 "forks" ++ pad 9 "plan ms" ++ pad 8 "run ms" ++ pad 9 "speedup"
    ++ pad 7 "wfB" ++ pad 7 "same"

/-- One parameter point: the file at `(n, m, d)`, run three ways. -/
def row (n m d reps grain : Nat) : IO String := do
  -- planning is deterministic and slow, so it is timed once however often the run is repeated
  match ← compileAt n m d with
  | .error e => pure s!"n = {n}: {e}"
  | .ok c    => do
      let ρ : Regs := fun _ => 0
      let a : AState := ⟨c.layout.data⟩
      let i := instrs c.prog
      let _ ← IO.lazyPure fun _ => i
      let (cs, ssam) ← repeatTimed reps (IO.lazyPure fun _ =>
        checksum (execArrD (ParProg.execPar c.prog ρ) a []).2.heap)
      -- every statement offered to the planner, regions and glue alike
      let (all, apsam) ← repeatTimed 1 (IO.lazyPure fun _ =>
        let p := ParProg.autoParTuned 8 grain (unmark c.prog)
        let _ := instrs p
        p)
      let af := forks all
      let _ ← IO.lazyPure fun _ => af
      let (ca, asam) ← repeatTimed reps (IO.lazyPure fun _ =>
        checksum (execArrD (ParProg.execPar all ρ) a []).2.heap)
      -- only the statements inside a marked region
      let (reg, rpsam) ← repeatTimed 1 (IO.lazyPure fun _ =>
        let p := ParProg.autoParIn 8 grain (fun _ => true) c.prog
        let _ := instrs p
        p)
      let rf := forks reg
      let _ ← IO.lazyPure fun _ => rf
      let (cr, rsam) ← repeatTimed reps (IO.lazyPure fun _ =>
        checksum (execArrD (ParProg.execPar reg ρ) a []).2.heap)
      -- the proved full-scan join, as the reference the sparse one is checked against
      let cf := checksum (execArr (ParProg.execPar all ρ) a).2
      let wf := ParProg.wfB all && ParProg.wfB reg
      pure (pad 5 (toString n) ++ pad 5 (toString m) ++ pad 6 (toString d)
        ++ pad 11 (toString i) ++ pad 9 (toString ssam.median)
        ++ pad 8 (toString af) ++ pad 9 (toString apsam.median) ++ pad 8 (toString asam.median)
        ++ pad 9 (ratio ssam.median asam.median)
        ++ pad 8 (toString rf) ++ pad 9 (toString rpsam.median) ++ pad 8 (toString rsam.median)
        ++ pad 9 (ratio ssam.median rsam.median)
        ++ pad 7 (toString wf) ++ pad 7 (toString (cs == ca && cs == cr && cs == cf)))

private def preface (src : String) (grain : Nat) : IO Unit := do
  match parse src with
  | .error _ => pure ()
  | .ok f    => match compileOne f "" with
    | .error _ => pure ()
    | .ok c    => do
        let rs := ParProg.regionNames c.prog
        IO.println s!"{(src.splitOn "\n").length} lines of {chaosPath}, {rs.length} marked regions."
        IO.println s!"seq = the file as written. grain = {grain}: a group carrying less work than"
        IO.println "that stays sequential. plan is compile time and is in no run."

/-- Sweep the unit *count*: `n` grows, so the planner sees more units of fixed size. -/
def sweep (ns : List Nat) (reps grain d : Nat) : IO Unit := do
  preface (← source 8 32 d) grain
  IO.println s!"n swept, m = 4n, d = {d}.\n"
  IO.println banner
  IO.println header
  IO.println ("".pushn '-' 139)
  for n in ns do
    IO.println (← row n (4 * n) d reps grain)
    (← IO.getStdout).flush

/-- Sweep the work *per unit*: `n` is fixed, so the plan and its planning cost are fixed too, and
`d` scales what each thread has to do. This is the sweep the crossover shows up in. -/
def sweepDepth (n : Nat) (ds : List Nat) (reps grain : Nat) : IO Unit := do
  preface (← source n (4 * n) 8) grain
  IO.println s!"n = {n}, m = {4 * n} fixed; d swept.\n"
  IO.println banner
  IO.println header
  IO.println ("".pushn '-' 139)
  for d in ds do
    IO.println (← row n (4 * n) d reps grain)
    (← IO.getStdout).flush

/-! ## Which regions pay

The sweeps above ask whether the regions as a set are worth forking. This asks which of them are:
the same file, the same parameter, one run per *kind* of region, with `keep` admitting that kind
and refusing every other. A kind is the first word of the region's name — `matmul`, `stencil`,
`branch` — which is how `chaos.prl` names them. -/

private def kindOf (nm : String) : String := (nm.splitOn " ").headD nm

def kinds (p : ParProg) : List String :=
  (ParProg.regionNames p).map kindOf |>.foldl (fun acc k => if acc.contains k then acc else acc ++ [k]) []

def byRegion (n m d reps grain : Nat) : IO Unit := do
  match ← compileAt n m d with
  | .error e => IO.println e
  | .ok c    => do
      let ρ : Regs := fun _ => 0
      let a : AState := ⟨c.layout.data⟩
      let ks := kinds c.prog
      let rs := ParProg.regionNames c.prog
      IO.println s!"{chaosPath} at n = {n}, m = {m}, d = {d}: {rs.length} regions, kinds {ks}."
      IO.println s!"grain = {grain}. Each row forks inside one kind of region and nowhere else.\n"
      IO.println (pad 12 "regions" ++ pad 9 "count" ++ pad 9 "forks" ++ pad 10 "plan ms"
        ++ pad 9 "run ms" ++ pad 10 "speedup" ++ pad 7 "wfB" ++ pad 7 "same")
      IO.println ("".pushn '-' 73)
      let (cs, ssam) ← repeatTimed reps (IO.lazyPure fun _ =>
        checksum (execArrD (ParProg.execPar c.prog ρ) a []).2.heap)
      IO.println (pad 12 "none (seq)" ++ pad 9 "0" ++ pad 9 "0" ++ pad 10 "0"
        ++ pad 9 (toString ssam.median) ++ pad 10 "1.00x" ++ pad 7 "true" ++ pad 7 "true")
      for k in ks ++ ["*"] do
        let keep := fun nm => k == "*" || kindOf nm == k
        let cnt := (rs.filter keep).length
        let (p, psam) ← repeatTimed 1 (IO.lazyPure fun _ =>
          let q := ParProg.autoParIn 8 grain keep c.prog
          let _ := instrs q
          q)
        let fk := forks p
        let _ ← IO.lazyPure fun _ => fk
        let (cp, rsam) ← repeatTimed reps (IO.lazyPure fun _ =>
          checksum (execArrD (ParProg.execPar p ρ) a []).2.heap)
        IO.println (pad 12 (if k == "*" then "all" else k) ++ pad 9 (toString cnt)
          ++ pad 9 (toString fk) ++ pad 10 (toString psam.median) ++ pad 9 (toString rsam.median)
          ++ pad 10 (ratio ssam.median rsam.median) ++ pad 7 (toString (ParProg.wfB p))
          ++ pad 7 (toString (cs == cp)))
        (← IO.getStdout).flush

end Paralever.Bench.Chaos
