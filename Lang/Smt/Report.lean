import Lang.Smt.Solve
import Lang.Verdict
import Paralever.Search.RaceSearch

/-! # The verification condition, as a report and as a file

What `paralever vc` prints, and the `.smt2` it writes with `-o`. Names come from the `Compiled`
layout, which is why this is separate from `Lang/Smt/Vc.lean`: the obligation is about a `ParProg`,
and only a compiled file knows that cell 3 is `dst[0]`.

See `docs/cli.md` § vc. -/

namespace Paralever.Smt

open Paralever.Lang

/-- **What the two checks already know**, before a solver is asked anything — the same two-part
verdict `check` prints, so the two reports cannot disagree. A solver is asked about the *any heap*
half and about nothing else: the declared heap is already decided here, exactly, by `raceSites`.
-- ref: `docs/general-heap.md` § The two parts -/
def headline (c : Compiled) : String :=
  "\n".intercalate ((verdictParts c).map fun (lbl, txt) =>
    lbl ++ String.ofList (List.replicate (12 - min 12 lbl.length) ' ') ++ txt)

/-- The buffer a computed address stays inside, by name. -/
private def bufName (c : Compiled) (a : ArrRef) : String :=
  match c.layout.bufs.find? (fun p => p.base == a.base && p.toBuf.size == a.len) with
  | some p => p.name
  | none   => s!"the {a.len} cells at {a.base}"

/-- `u0  the value read from idx[0]` — without this a query is unreadable, and an assumption about
`u0` cannot be written by someone who does not know what it is. -/
def originLine (c : Compiled) : Nat × Origin → String
  | (k, .cell l)     => s!"  {Query.unknownName k}  the value read from {c.locName l}"
  | (k, .computed a) => s!"  {Query.unknownName k}  a value read from a computed cell of {bufName c a}"
  | (k, .reg r)      => s!"  {Query.unknownName k}  register %{r}, never assigned before its use"

/-- One fork's heading: its name, its thread count, and what `wfB` made of it. -/
private def forkHead (v : Vc) : String :=
  s!"{v.name} — {v.threads} threads"

/-- The report for one fork, before any solver runs. -/
def vcLines (c : Compiled) (v : Vc) : List String :=
  match v.status with
  | .independent =>
      [ forkHead v, "  independent — decided here, no solver needed" ]
  | .collides l =>
      -- a widened footprint makes a collision a possibility, not a race: only one branch runs
      if v.approx then
        [ forkHead v,
          s!"  inconclusive — two threads may touch {c.locName l}, from opposite sides of a branch" ]
      else
        [ forkHead v, s!"  RACY — two threads touch {c.locName l}" ]
  | .query q pairs =>
      let logic := if q.goal.nonlinear then "QF_NIA (nonlinear: a product of two computed values)"
                   else "QF_LIA"
      [ forkHead v,
        s!"  {pairs.length} pair(s) left to decide, over {q.unknowns} unknown value(s), in {logic}" ]
        ++ (if v.origins.isEmpty then [] else v.origins.map (originLine c))

/-- The assumptions a run was given, as a line of the report. It qualifies every answer below it,
so it sits with them rather than at the end. -/
def assumeLine : List String → List String
  | []  => []
  | nms => [s!"assuming {String.intercalate ", " nms}"]

/-- Every fork's obligation, as text. -/
def vcReport (c : Compiled) (vs : List Vc) (assume : List String := []) : String :=
  if vs.isEmpty then "nothing to discharge: no parallel block\n"
  else String.intercalate "\n"
    ([headline c] ++ assumeLine assume ++ vs.flatMap (vcLines c) ++ [""])

/-! ## The file

Several forks share one file, each query inside `(push 1)`/`(pop 1)` so its declarations do not
leak into the next. `set-logic` may appear once, so it is the strongest any query needs. -/

def smtFile (c : Compiled) (vs : List Vc) : String :=
  let qs := vs.filterMap fun v => match v.status with
    | .query q _ => some (v.name, { q with notes := q.notes ++ v.origins.map (originLine c) })
    | _          => none
  match qs with
  | []        => "; every fork was decided without a solver\n"
  | [(_, q)]  => q.render
  | _ =>
      let logic := if qs.any (fun (_, q) => q.goal.nonlinear) then "QF_NIA" else "QF_LIA"
      let one := fun (nq : String × Query) =>
        let (nm, q) := nq
        String.intercalate "\n"
          ([ "", s!"(push 1)", s!"; {nm}" ]
            ++ q.unknownNames.map (fun u => s!"(declare-const {u} Int)")
            ++ [ s!"(assert {q.goal.render})", "(check-sat)", "(pop 1)" ])
      "; paralever: one query per parallel block; unsat means that block is independent\n"
        ++ s!"(set-logic {logic})\n" ++ String.intercalate "\n" (qs.map one) ++ "\n"

/-- Assert that every loaded value is at or above zero. `ArrRef.addr` clamps a negative index to the
buffer's first cell (`i.toNat`), so *every* thread with a possibly-negative computed index aliases
there — which is a true collision, and almost never the one a reader is asking about. Stating this
hypothesis is how they ask the other question; it weakens the claim, so the report names it. -/
def assumeNonneg (v : Vc) : Vc :=
  match v.status with
  | .query q pairs =>
      let q' : Query :=
        { q with assume := q.unknownNames.map (fun u => Sx.app ">=" [.atom u, .int 0]) }
      { v with status := .query q' pairs }
  | _ => v

/-! ## With a solver

`unsat` is reported as *discharged by* the named solver, never as proved: it is not a Lean proof.
`sat` is checked here before it is believed — `witness` recomputes the collision in Lean.
-- ref: `docs/smt-vc.md` § Trust, which is asymmetric -/

def solveLines (c : Compiled) (s : Solver) (v : Vc) : IO (List String × Bool) := do
  match v.status with
  | .query q pairs =>
      match ← solve s q with
      | .unsat =>
          pure ([s!"  independent — unsat"], true)
      | .sat m =>
          let vals := String.intercalate ", "
            (m.map fun (k, n) => s!"{Query.unknownName k} = {n}")
          match witness pairs m with
          | some (_, _, l) =>
              -- a model is an assignment, not a run: nothing says the heap can hold it, so this is
              -- the obligation failing rather than a race found
              pure ([s!"  inconclusive — not discharged: the threads can touch {c.locName l} \
when {vals}"], false)
          | none =>
              if m.isEmpty then
                pure ([s!"  inconclusive — not discharged: sat, but {s.exe}'s model could not be \
read"], false)
              else
                pure ([s!"  inconclusive — not discharged: sat, but no pair collides at {vals} \
(solver error)"], false)
      | .unknown =>
          let more := if s.timeout == 0 then "" else s!" within {s.timeout} ms; raise --timeout"
          pure ([s!"  inconclusive — not discharged: the solver did not decide this query{more}"],
                false)
      | .failed e => pure ([s!"  not attempted — {e}"], false)
  | _ => pure ([], true)

/-- The report with a solver run on every query that is left. The `Bool` is whether every fork came
out independent, which is what the command's exit code reports. -/
def solveReport (c : Compiled) (s : Solver) (ver : String) (vs : List Vc)
    (assume : List String := []) : IO (String × Bool) := do
  if vs.isEmpty then
    pure ("nothing to discharge: no parallel block\n", true)
  else
  -- the solver line, and its one trust caveat, only when a query is actually sent
  let asked := vs.any fun v => match v.status with | .query _ _ => true | _ => false
  let mut lines : List String :=
    [headline c] ++ assumeLine assume
      ++ (if asked then [s!"solver: {ver} — unsat is its word, not Lean's"] else [])
  let mut ok := true
  for v in vs do
    let head := vcLines c v
    let (tail, good) ← solveLines c s v
    lines := lines ++ head ++ tail
    ok := ok && good && (match v.status with | .collides _ => false | _ => true)
  pure (String.intercalate "\n" (lines ++ [""]), ok)

end Paralever.Smt
