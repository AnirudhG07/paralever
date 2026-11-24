/-! # `--time` — processor time, not wall clock

Lean's `IO.monoMsNow` and `IO.monoNanosNow` are monotonic clocks whose own docstrings say they bear
no relation to wall clock time, and the toolchain binds no `clock`, `times` or `getrusage`. So the
figure comes from `/proc/self/stat`, whose fourteenth and fifteenth fields are the process's user
and system time in clock ticks. Where there is no `/proc` the wall clock answers instead, and the
line says which it was. -- ref: `docs/cli.md` § `--time` -/

namespace Paralever.Tool

/-- Clock ticks per second. `_SC_CLK_TCK` is 100 on every mainstream Linux, and reading it needs a C
call this project has no stub for. -/
private def tickHz : Nat := 100

/-- The two tick counts in `/proc/self/stat`, read *after the last `)`*: the second field is the
executable's name, which may hold spaces and parentheses of its own. -/
private def ticksOf (line : String) : Option (Nat × Nat) := do
  let rest ← (line.splitOn ")").getLast?
  let fs := (rest.splitOn " ").filter (· != "")
  -- field 3 is the first here, so `utime` and `stime` are the twelfth and thirteenth
  let u ← fs[11]?
  let s ← fs[12]?
  pure (← u.toNat?, ← s.toNat?)

/-- Processor time this process has used, in milliseconds. `none` where `/proc` is not there. -/
def cpuMs : BaseIO (Option Nat) := do
  match ← (IO.FS.readFile "/proc/self/stat").toBaseIO with
  | .error _   => pure none
  | .ok line   => pure ((ticksOf line).map (fun (u, s) => (u + s) * 1000 / tickHz))

/-- Where a timed command starts: the wall clock, for the fallback, and the processor clock. -/
def timeStart : BaseIO (Nat × Option Nat) := do pure (← IO.monoNanosNow, ← cpuMs)

/-- Milliseconds since `t0`: processor time where `/proc` has it, the wall clock otherwise. -/
def elapsedMs (t0 : Nat × Option Nat) : BaseIO Nat := do
  match t0.2, ← cpuMs with
  | some a, some b => pure (b - a)
  | _,      _      => do pure (((← IO.monoNanosNow) - t0.1) / 1000000)

/-- What `--time` prints. The `(wall)` suffix is the whole disclosure that this is not the
processor's own figure. -/
def timeLine (t0 : Nat × Option Nat) : BaseIO String := do
  let ms ← elapsedMs t0
  pure (s!"time: {ms}ms" ++ (if t0.2.isSome then "" else " (wall)"))

end Paralever.Tool
