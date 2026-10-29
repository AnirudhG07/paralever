import Lang.Report

namespace Paralever.Examples.Input
open Paralever Paralever.Lang

/-! ## 1 · A program that reads the shell

`prl_file` cannot read this one: it compiles while *Lean* elaborates, and Lean has no pipe
(`docs/prl.md` § Input). So the file is read as text and compiled with the input given here, which
is what `ofString`'s second argument is for. -/

def src : String := include_str "input.prl"

/-- The program, compiled against one line of input. A failure would be a compile error in the
file, so the fallback is the empty program and the reports below would show it. -/
def upcase : Compiled :=
  (ofString src "hello, world\n").toOption.getD ⟨⟨[]⟩, ParProg.block [], [], [], none⟩

/-! The input is consumed while the program compiles, so by the time there is a program the line is
already in the declaration — `buf s[16]` holds the bytes of `hello, world`. -/

#guard (upcase.layout.find? "s").map (fun p => p.init.take 5) == some [104, 101, 108, 108, 111]

/-! ## 2 · Sixteen threads, one cell each

Every thread reads and writes the one byte it owns, so Bernstein holds and the verdict needs no
hypothesis beyond the program text. -/

/--
info: input.prl
  memory    s[16] @0  (16 cells)
  reads     {s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7], s[8], s[9], … +6 more}
  writes    {s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7], s[8], s[9], … +6 more}
  threads   16
  rounds    2 parallel, 32 sequential
  verdict   every heap  Proved: Yes — wfB accepts: the threads' footprints are pairwise independent
-/
#guard_msgs in
#eval IO.println (checkReport "input.prl" upcase)

/-- The bytes of a buffer, read back as text — the heap is the program's output, and this one is a
string. -/
def textOf (c : Compiled) (nm : String) (σ : State) : String :=
  let r := c.layout.ref nm
  String.ofList ((List.range r.len).filterMap fun i =>
    match σ (r.base + i) with
    | .int n => if n == 0 then none else some (Char.ofNat n.toNat)
    | _      => none)

#guard textOf upcase "s" (heapAfter upcase false) == "HELLO, WORLD"

/-! Running the forks on real `Task`s gives the same string, which is what `par_seq_eq` says of a
program `wfB` accepts. -/

#guard textOf upcase "s" (heapAfter upcase true) == "HELLO, WORLD"

/-! ## 3 · The three forms

A register takes one word, a buffer takes one word per cell, and `input str` takes a line. `true`
and `false` read as `1` and `0`. -/

def forms : String :=
  "reg a, b\n%a := input\n%b := input\nbuf A[3] = input\nbuf s[4] = input str\n"

-- the register values land in the program, the buffer values in the declaration
#guard match ofString forms "7 true\n1 2 3\nhi\n" with
  | .ok c =>
      c.layout.bufs.map (fun p => (p.name, p.init))
        == [("A", [1, 2, 3]), ("s", [104, 105])]
      && ((toPrl c).splitOn "\n").contains "%0 := 7"
  | .error _ => false

/-! ## 4 · Where it is refused

The order values are read in has to be fixed by the program text, so a thread, a branch and a loop
with a run-time bound may not read. A `for` may: it is unrolled, so its count is in the text. -/

private def refuses (src : String) : Bool := (ofString src "1 2 3 4").toOption.isNone

#guard refuses "reg t\nparfor i in 2 { %t := input }"
#guard refuses "reg t\nparallel { %t := input } | { %t := 0 }"
#guard refuses "reg t\nif (1) { %t := input }"
#guard refuses "reg t\nwhile (1) in 2 { %t := input }"
#guard refuses "reg t\n%t := input + 1"
#guard refuses "reg t\nbuf A[input]"

-- a `for` reads once per iteration, in order
#guard match ofString "reg t\nbuf A[3]\nfor i in 3 { %t := input\nA[i] := %t }" "5 6 7" with
  | .ok c => ((toPrl c).splitOn "\n").contains "%0 := 6"
  | .error _ => false

/-! ## 5 · Proving one

A program that reads input is refused by `prove` for the same reason `prl_file` refuses it. The
route is to resolve the input first — `paralever to-prl input.prl < data` prints a `.prl` file
with the values written in, and that file proves like any other. -/

#guard (parse src).toOption.map File.usesInput == some true
#guard (parse (toPrl upcase)).toOption.map File.usesInput == some false

end Paralever.Examples.Input
