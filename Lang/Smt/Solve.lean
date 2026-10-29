import Lang.Smt.Vc

/-! # Running a solver, and what its answer is worth

An external solver is not Lean's kernel, so the two answers are worth different things and this
file keeps the difference visible. `unsat` is *discharged by* the named solver and never reported as
proved. `sat` is checked here: the model's values are substituted back into the symbolic addresses
(`Sym.evalWith`) and the collision is recomputed, so a wrong solver can waste time but cannot
produce a wrong verdict.

Rationale: `docs/smt-vc.md` § Trust, which is asymmetric. -/

namespace Paralever.Smt

/-- A solver to call. `args` ends with the query's path, which `solve` appends. `timeFlag` is how
this solver spells a per-query limit; the milliseconds are appended to it. -/
structure Solver where
  exe      : String
  args     : List String := []
  timeFlag : String := ""
  /-- Milliseconds per query; `0` is no limit. A query that runs out answers `unknown`. -/
  timeout  : Nat := 0
  deriving Repr, Inhabited

/-- The command line for one query. -/
def Solver.argsFor (s : Solver) (path : String) : Array String :=
  (s.args ++ (if s.timeout == 0 || s.timeFlag.isEmpty then []
              else [s!"{s.timeFlag}{s.timeout}"]) ++ [path]).toArray

/-- `z3` and `cvc5` both read an `.smt2` path as a positional argument and print `sat`/`unsat` on
the first line, so one shape covers both. cvc5 needs asking before it will answer `(get-value …)`. -/
def z3   : Solver := { exe := "z3",   args := ["-smt2"], timeFlag := "-t:" }
def cvc5 : Solver := { exe := "cvc5", args := ["--lang=smt2", "--produce-models"],
                       timeFlag := "--tlimit=" }

/-- Looked for in order, and the first one that runs is used. Any other solver that reads an
`.smt2` path is reached through `PARALEVER_SMT`, which is tried before these. -/
def known : List Solver := [z3, cvc5]

/-- The solver `PARALEVER_SMT` names, with the argument shape its name implies. A bare name is
looked up on `PATH`; a path is used as given, so a solver that was never installed still works. -/
def named (e : String) : Solver :=
  let base := (System.FilePath.mk e).fileName.getD e
  if base.startsWith "cvc5" then { cvc5 with exe := e } else { z3 with exe := e }

/-- Its version line, or why it could not be run. Printed beside a verdict, because "discharged by
a solver" is not a claim until the solver is named. -/
def Solver.version (s : Solver) : IO (Except String String) := do
  try
    let out ← IO.Process.output { cmd := s.exe, args := #["--version"] }
    if out.exitCode != 0 then
      pure (.error s!"'{s.exe}' could not be run (exit {out.exitCode}); \
point --solver or PARALEVER_SMT at a solver that reads an .smt2 file")
    else
      pure (.ok ((out.stdout.splitOn "\n").headD "").trimAscii.toString)
  catch _ =>
    pure (.error s!"'{s.exe}' could not be run; point --solver or PARALEVER_SMT at a solver's path")

/-- **The first solver present**, with its version line. `PARALEVER_SMT` wins when it is set, and
its absence is an error rather than a silent fall-through: naming a solver that is not there is a
mistake worth reporting. Otherwise each of `known` is tried in turn. -/
def discover : IO (Except String (Solver × String)) := do
  match ← IO.getEnv "PARALEVER_SMT" with
  | some e =>
      if e.isEmpty then pure (.error "PARALEVER_SMT is set but empty") else
      let s := named e
      match ← s.version with
      | .ok v    => pure (.ok (s, v))
      | .error m => pure (.error m)
  | none => go known []
where
  go : List Solver → List String → IO (Except String (Solver × String))
    | [],      tried => pure (.error
        s!"no SMT solver found (tried {String.intercalate ", " tried.reverse}); \
install one, or name it with --solver (or PARALEVER_SMT)")
    | s :: ss, tried => do
        match ← s.version with
        | .ok v  => pure (.ok (s, v))
        | .error _ => go ss (s.exe :: tried)

/-- The solver to use: the one asked for by name or path, else whatever `discover` finds. Asking
for one that cannot be run is an error, never a fall-through to another. -/
def choose : Option String → IO (Except String (Solver × String))
  | none   => discover
  | some e => do
      if e.isEmpty then pure (.error "--solver needs a name or a path") else
      let s := named e
      match ← s.version with
      | .ok v    => pure (.ok (s, v))
      | .error m => pure (.error m)

/-- What a solver said. -/
inductive Answer where
  /-- No assignment collides: the threads are independent, on this solver's word. -/
  | unsat : Answer
  /-- An assignment that collides, as `(unknown, value)` pairs. -/
  | sat : List (Nat × Int) → Answer
  /-- The solver gave up — a timeout, or a logic it does not decide. -/
  | unknown : Answer
  /-- The solver could not be run, or said something unrecognized. -/
  | failed : String → Answer
  deriving Repr, Inhabited

/-! ## Reading the model

z3 and cvc5 both answer `(get-value (u0 u1))` with `((u0 3) (u1 (- 1)))`, possibly across lines. The
numbers are all that is wanted, so the text is scanned for `uN` and the integer that follows it
rather than parsed as S-expressions. -/

private def intAfter (s : String) : Option Int :=
  let s := s.trimAscii.toString
  let (neg, s) := if s.startsWith "(-" then (true, (s.drop 2).trimAscii.toString) else (false, s)
  let digits := s.takeWhile Char.isDigit
  if digits.isEmpty then none
  else (digits.toNat?).map (fun n => if neg then -(Int.ofNat n) else Int.ofNat n)

/-- The `uN` bindings in a solver's model, in the order they appear. -/
def parseModel (names : List String) (out : String) : List (Nat × Int) :=
  names.filterMap fun u => do
    let k ← (u.drop 1).toNat?
    let after := (out.splitOn u).getD 1 ""
    -- `u1` is a prefix of nothing else in the list, and the binding's value follows its name
    let v ← intAfter after
    pure (k, v)

/-- Write the query, run the solver, and read the first line. On `sat` the query is sent a second
time with `(get-value …)` appended, because asking for a model after `unsat` is an error. -/
def solve (s : Solver) (q : Query) : IO Answer := do
  try
    let ask (text : String) : IO String := IO.FS.withTempFile fun h path => do
      h.putStr text
      h.flush
      let out ← IO.Process.output { cmd := s.exe, args := s.argsFor path.toString }
      pure (out.stdout ++ out.stderr)
    let first := (((← ask (q.render)).splitOn "\n").headD "").trimAscii.toString
    match first with
    | "unsat"   => pure .unsat
    | "unknown" => pure .unknown
    | "sat"     => pure (.sat (parseModel q.unknownNames (← ask (q.render (model := true)))))
    | other     => pure (.failed (if other.isEmpty then "no output" else other))
  catch e =>
    pure (.failed s!"'{s.exe}' could not be run: {e}")

/-- **The pair the model actually collides**, recomputed in Lean. A `sat` answer is a claim about
two cells, and this is the check of that claim rather than its acceptance: `none` means the model
does not in fact collide any pair, which is the solver's bug and reported as such. -/
def witness (pairs : List (SAddr × SAddr)) (m : List (Nat × Int)) : Option (SAddr × SAddr × Loc) :=
  let val := fun k => (m.lookup k).getD 0
  pairs.findSome? fun (a, b) =>
    let la := a.evalWith val
    if la == b.evalWith val then some (a, b, la) else none

end Paralever.Smt
