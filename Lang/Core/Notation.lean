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

/-- Whether an expression answers in `0`/`1`: a `min` of two such is an `&&`, not a minimum. -/
def isCond : AExp → Bool
  | .lt _ _  => true
  | .eq _ _  => true
  | .not _   => true
  | .min a b => isCond a && isCond b
  | .max a b => isCond a && isCond b
  | _        => false

/-- An expression in ordinary infix form, with the derived conditions spelled as they are written.
-- ref: `docs/block-ir.md` § Conditions -/
def showExp : AExp → String
  | .not (.lt a b) => "(" ++ showExp a ++ " >= " ++ showExp b ++ ")"
  | .not (.eq a b) => "(" ++ showExp a ++ " != " ++ showExp b ++ ")"
  | .min a b => if isCond a && isCond b
                then "(" ++ showExp a ++ " && " ++ showExp b ++ ")"
                else "min(" ++ showExp a ++ ", " ++ showExp b ++ ")"
  | .max a b => if isCond a && isCond b
                then "(" ++ showExp a ++ " || " ++ showExp b ++ ")"
                else "max(" ++ showExp a ++ ", " ++ showExp b ++ ")"
  | .lit n   => toString n
  | .reg r   => "%" ++ toString r
  | .add a b => "(" ++ showExp a ++ " + " ++ showExp b ++ ")"
  | .sub a b => "(" ++ showExp a ++ " - " ++ showExp b ++ ")"
  | .mul a b => "(" ++ showExp a ++ " * " ++ showExp b ++ ")"
  | .div a b => "(" ++ showExp a ++ " / " ++ showExp b ++ ")"
  | .lt a b  => "(" ++ showExp a ++ " < " ++ showExp b ++ ")"
  | .eq a b  => "(" ++ showExp a ++ " == " ++ showExp b ++ ")"
  | .not a   => "!" ++ showExp a

/-- One `print` item, in the Lean form's own vocabulary. -/
def showItem : PrintItem → String
  | .text s        => "\"" ++ s ++ "\""
  | .exp e         => showExp e
  | .buf nm _ _    => nm
  | .at nm _ e     => nm ++ "[" ++ showExp e ++ "]"
  | .cell nm idx _ =>
      if idx.isEmpty then nm
      else nm ++ "[" ++ ", ".intercalate (idx.map toString) ++ "]"

/-- One affine subscript: the buffer's base, its coefficient per level, and its constant term. -/
def showAff (a : Nest.AffAccess) : String :=
  "A" ++ toString a.base ++ "[" ++ ", ".intercalate (a.coeffs.map toString) ++ "]"
    ++ (if a.off == 0 then "" else "+" ++ toString a.off)

/-- One statement of a nest body. -/
def showNestStmt : NestStmt → String
  | .rd r a => "%" ++ toString r ++ " := " ++ showAff a
  | .wr a e => showAff a ++ " := " ++ showExp e
  | .st r e => "%" ++ toString r ++ " := " ++ showExp e

/-- One level: its induction register and its trip count, with the first value and the stride when
they are not the normalized `0` and `1`. -/
def showLevels : List Reg → List Nat → List Int → List Int → List String
  | r :: rs, n :: ns, lo :: los, st :: sts =>
      ("%" ++ toString r ++ " in " ++ toString n
        ++ (if lo == 0 && st == 1 then ""
            else " from " ++ toString lo ++ " step " ++ toString st))
        :: showLevels rs ns los sts
  | _, _, _, _ => []

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
  | .print is, d => [ind d ++ "print " ++ ", ".intercalate (is.map showItem) ++ ";"]
  | .loop n, d =>
      (ind d ++ "parfor " ++ ", ".intercalate (showLevels n.ivs n.sizes n.lo n.step)
        ++ " fork " ++ toString n.parDepth ++ " {")
        :: n.body.map (fun s => ind (d + 1) ++ showNestStmt s ++ ";")
        ++ [ind d ++ "}"]

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
/-- `%i := [A, e]` — a **data-dependent** load: the cell of the range `A` at index `e`. `[l]` names
a cell by address, this one by range and index, which is the pair `ParProg.loadAt` takes. The index
wraps on `A.len`, so the access is confined to `A` (`ArrRef.addr_mem_cells`). -/
syntax "%" num " := " "[" term ", " term "]" : impStmt
/-- `%name := [A, e]` — the same, into a named register. -/
syntax "%" ident " := " "[" term ", " term "]" : impStmt
/-- `[A, e] := e'` — a data-dependent store. -/
syntax "[" term ", " term "]" " := " term : impStmt
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
/-- `{…} :: "name"` — a named region that is not a fork, which is `ParProg.label` in general.
`parallel` and `parfor` carry their own `::`; this is the form for everything else. -/
syntax "{" sepBy1(impStmt, "; ") "}" " :: " str : impStmt
/-- `synchronize` — end the phase. Statements before and after are never grouped into one fork.
This reserves `synchronize` project-wide, so no declaration may be named it; the constructor
`ParProg.synchronize` is unaffected. -- ref: `CLAUDE.md` § Surface-syntax tokens are global -/
syntax "synchronize" : impStmt

/-- `print [items]` — output, erased from both interpreters. The items are a Lean term rather than a
surface list: this is the Lean form of the constructor, and `.prl` text is where `print k` is spelled
the short way. Reserving `print` is why the `.prl` printer is `toPrl`.
-- ref: `CLAUDE.md` § Surface-syntax tokens are global -/
syntax "print " term : impStmt

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
  | `(impStmt| % $i:num := [$a:term, $e:term])   => `(ParProg.loadAt $i $a $e)
  | `(impStmt| % $x:ident := [$a:term, $e:term]) => `(ParProg.loadAt $x $a $e)
  | `(impStmt| [$a:term, $e:term] := $v:term)    => `(ParProg.storeAt $a $e $v)
  | `(impStmt| synchronize)                   => `(ParProg.synchronize)
  | `(impStmt| print $is:term)                => `(ParProg.print $is)
  | `(impStmt| { $[$ss];* } :: $nm:str) => do
      let body ← ss.mapM expandProg
      `(ParProg.label $nm (ParProg.block [$[$body],*]))
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
