import Lang.Core.Kernels

/-! # Printing a `ParProg`, and writing one

Printing is purely syntactic — unlike `Lib/Render.lean`'s `codeStr`, this needs no state, because
the computations are data. The surface syntax `paralever { … }` elaborates to a `ParProg`. -/

namespace Paralever.Lang
open Paralever

/-! `%n` and `%name` denote register `n` on *either* side of a `:=`: as the destination of a load or
an assignment, and as an operand inside an expression. A named register is any identifier of type
`Reg`, so `abbrev rsp : Reg := 0` once buys `%rsp` everywhere.

`scoped`, deliberately. `%` is already a token, so this reserves nothing project-wide, but it does
add a *leading* parser for it, and in a leading position `f 7 % 2` reads as `f 7 (%2)`. Scoping the
notation to `Paralever.Lang` confines that to the files that write programs, where the workaround is
`(f 7) % 2`. -- ref: `CLAUDE.md` § Surface-syntax tokens are global -/
scoped syntax:max "%" num   : term
scoped syntax:max "%" ident : term
macro_rules | `(term| %$n:num)   => `(AExp.reg $n)
macro_rules | `(term| %$x:ident) => `(AExp.reg $x)

namespace ParProg

/-! ## Printing

Purely syntactic — unlike `Lib/Render.lean`'s `codeStr`, this needs no state, because the
computations are data. -/

private def ind (d : Nat) : String := String.ofList (List.replicate (2 * d) ' ')

/-- An expression in ordinary infix form. -/
def showExp : AExp → String
  | .lit n   => toString n
  | .reg r   => "%" ++ toString r
  | .add a b => "(" ++ showExp a ++ " + " ++ showExp b ++ ")"
  | .sub a b => "(" ++ showExp a ++ " - " ++ showExp b ++ ")"
  | .mul a b => "(" ++ showExp a ++ " * " ++ showExp b ++ ")"
  | .min a b => "min(" ++ showExp a ++ ", " ++ showExp b ++ ")"
  | .max a b => "max(" ++ showExp a ++ ", " ++ showExp b ++ ")"
  | .div a b => "(" ++ showExp a ++ " / " ++ showExp b ++ ")"

mutual

def render : ParProg → Nat → List String
  | .load r l,  d => [ind d ++ "%" ++ toString r ++ " := M[" ++ toString l ++ "];"]
  | .store l e, d => [ind d ++ "M[" ++ toString l ++ "] := " ++ showExp e ++ ";"]
  | .set r e,   d => [ind d ++ "%" ++ toString r ++ " := " ++ showExp e ++ ";"]
  | .seq a b,   d => render a d ++ render b d
  | .par ss,    d => (ind d ++ "parallel {") :: renderAll ss (d + 1) 0 ++ [ind d ++ "}"]
  | .label nm s, d =>
      (ind d ++ "-- " ++ nm) :: render s d
  | .loadAt r a e, d =>
      [ind d ++ "%" ++ toString r ++ " := A" ++ toString a.base ++ "[" ++ showExp e ++ "];"]
  | .storeAt a e v, d =>
      [ind d ++ "A" ++ toString a.base ++ "[" ++ showExp e ++ "] := " ++ showExp v ++ ";"]
  | .ifElse c t e, d =>
      ((ind d ++ "if " ++ showExp c ++ " {") :: render t (d + 1)) ++
      ((ind d ++ "} else {") :: render e (d + 1)) ++ [ind d ++ "}"]
  | .synchronize, d => [ind d ++ "synchronize;"]

def renderAll : List ParProg → Nat → Nat → List String
  | [],      _, _ => []
  | s :: ss, d, i =>
      ((ind d ++ "thread " ++ toString i ++ " {") :: render s (d + 1))
        ++ [ind d ++ "}"] ++ renderAll ss d (i + 1)

end

def renderProg (s : ParProg) : String := "\n".intercalate (render s 0)

/-- The program, its computed footprint, and whether the obligation holds — the whole story about a
program in one block of text. -/
def reportProg (s : ParProg) : String :=
  let f := footprintOf s
  renderProg s
    ++ "\n-- reads  " ++ toString f.reads
    ++ "\n-- writes " ++ toString f.writes
    ++ "\n-- independent: " ++ toString (wfB s)

/-! ## Surface syntax

The point of a first-order language is that you can write it. `paralever { … }` elaborates to a `ParProg`,
which `execPar` lowers into `ParM`:

```text
paralever {
  %0 := mem 0;
  %1 := mem 1;
  mem 2 := %0 + %1;
  parallel { %2 := mem 0;  mem 3 := %2 * 2 }
           | { %3 := mem 1;  mem 4 := %3 * 2 }
}
```

`for i in n {…}` and `parfor i in n {…}` are loops, unrolled when the term elaborates, and a
parallel form may be named with `:: "name"`. `[l]` is memory and `%i` a register; expressions are ordinary `AExp` terms, so `%0 + %1 * 2`
means what it looks like. Memory and registers are written differently so that a load, a store and a
register assignment are told apart by the parser rather than by elaboration.

Brackets rather than a `mem` keyword: `[` and `]` are tokens already, so this form reserves nothing
project-wide. -- ref: `CLAUDE.md` § Surface-syntax tokens are global -/

declare_syntax_cat impStmt
declare_syntax_cat impThread

/-- `%i := [l]` — load. -/
syntax "%" num " := " "[" term "]" : impStmt
/-- `[l] := e` — store. -/
syntax "[" term "]" " := " term : impStmt
/-- `%i := e` — register assignment, touches no memory. -/
syntax "%" num " := " term : impStmt
/-- `%name := [l]` — load into a named register. -/
syntax "%" ident " := " "[" term "]" : impStmt
/-- `%name := e` — assignment to a named register. -/
syntax "%" ident " := " term : impStmt
/-- One thread of a `parallel`: a braced, `;`-separated group. -/
syntax "{" sepBy1(impStmt, "; ") "}" : impThread
/-- `parallel {…} | {…}` — one thread per group. -/
syntax "parallel " sepBy1(impThread, "| ") : impStmt
/-- `if e {…} else {…}` — control flow. `0` is false, anything else true. The parser takes
`term:max`, so a bare register is fine (`if %0 {…}`) and a compound condition is parenthesised
(`if (%0 - %1) {…}`). -/
syntax "if " term:max impThread " else " impThread : impStmt
/-- `while e in n {…}` — guarded loop, at most `n` iterations. Uses the existing `in` token rather
than reserving a new keyword. -/
syntax "while " term:max " in " term:max impThread : impStmt
/-- `for i in n {…}` — a sequential loop, unrolled at elaboration. -/
syntax "for " ident " in " term:max impThread : impStmt
/-- `parfor i in n {…}` — one thread per index, the parallel loop. -/
syntax "parfor " ident " in " term:max impThread : impStmt
/-- `parfor i in n {…} :: "name"` — a named parallel loop. -/
syntax "parfor " ident " in " term:max impThread " :: " str : impStmt
/-- `parallel {…} | {…} :: "name"` — a named parallel block. -/
syntax "parallel " sepBy1(impThread, "| ") " :: " str : impStmt
/-- `synchronize` — end the phase. Statements before and after are never grouped into one fork.
This reserves `synchronize` project-wide, so no declaration may be named it; the constructor
`ParProg.synchronize` is unaffected. -- ref: `CLAUDE.md` § Surface-syntax tokens are global -/
syntax "synchronize" : impStmt

/-- A `;`-separated group of statements, as a single `ParProg`. -/
syntax "paralever " "{" sepBy1(impStmt, "; ") "}" : term

open Lean in
/-- Expand one surface statement into a `ParProg` term. -/
partial def expandProg : TSyntax `impStmt → MacroM (TSyntax `term)
  | `(impStmt| % $i:num := [$l:term]) => `(ParProg.load $i $l)
  | `(impStmt| [$l:term] := $e:term)  => `(ParProg.store $l $e)
  | `(impStmt| % $i:num := $e:term)     => `(ParProg.set $i $e)
  | `(impStmt| % $x:ident := [$l:term]) => `(ParProg.load $x $l)
  | `(impStmt| % $x:ident := $e:term)   => `(ParProg.set $x $e)
  | `(impStmt| synchronize)                   => `(ParProg.synchronize)
  | `(impStmt| for $i:ident in $n:term { $[$ss];* }) => do
      let body ← ss.mapM expandProg
      `(ParProg.block ((List.range $n).map (fun $i => ParProg.block [$[$body],*])))
  | `(impStmt| parfor $i:ident in $n:term { $[$ss];* }) => do
      let body ← ss.mapM expandProg
      `(ParProg.parFor $n (fun $i => ParProg.block [$[$body],*]))
  | `(impStmt| parfor $i:ident in $n:term { $[$ss];* } :: $nm:str) => do
      let body ← ss.mapM expandProg
      `(ParProg.label $nm (ParProg.parFor $n (fun $i => ParProg.block [$[$body],*])))
  | `(impStmt| while $c:term in $n:term { $[$ss];* }) => do
      let body ← ss.mapM expandProg
      `(ParProg.whileAtMost $n $c (ParProg.block [$[$body],*]))
  | `(impStmt| if $c:term { $[$ts];* } else { $[$fs];* }) => do
      let tb ← ts.mapM expandProg
      let fb ← fs.mapM expandProg
      `(ParProg.ifElse $c (ParProg.block [$[$tb],*]) (ParProg.block [$[$fb],*]))
  | `(impStmt| parallel $[$ts]|* :: $nm:str) => do
      let threads ← ts.mapM fun t =>
        match t with
        | `(impThread| { $[$ss];* }) => do
            let body ← ss.mapM expandProg
            `(ParProg.block [$[$body],*])
        | _ => Macro.throwUnsupported
      `(ParProg.label $nm (ParProg.par [$[$threads],*]))
  | `(impStmt| parallel $[$ts]|*) => do
      let threads ← ts.mapM fun t =>
        match t with
        | `(impThread| { $[$ss];* }) => do
            let body ← ss.mapM expandProg
            `(ParProg.block [$[$body],*])
        | _ => Macro.throwUnsupported
      `(ParProg.par [$[$threads],*])
  | _ => Macro.throwUnsupported

open Lean in
macro_rules
  | `(paralever { $[$ss];* }) => do
      let body ← ss.mapM expandProg
      `(ParProg.block [$[$body],*])

end ParProg

end Paralever.Lang
