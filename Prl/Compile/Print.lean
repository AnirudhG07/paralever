import Prl.Compile.Lower
import Prl.Lang.Analysis
import Paralever.AutoPar.Print

/-! # Printing a compiled file back out

`print` writes `.prl` text, addresses as the buffer names they fall in, and `roundTrips` is the gate
on the reader. `toLean` writes the `paralever { … }` block through `AutoPar.surface`, so the Lean
form has one printer. `highlight` is the same text with ANSI colour, in the editor grammar's token
classes. Loops and names are gone by now: what prints is the unrolled program `wfB` decides on. -/

namespace Paralever.Prl
open Paralever Paralever.Prl

-- Structural equality on programs, for the round-trip gate below. Not in the language's own
-- module: the theory never compares two programs, only runs them.
deriving instance BEq for Paralever.Prl.ParProg

/-! ## `.prl` out -/

private def ind (d : Nat) : String := String.ofList (List.replicate (2 * d) ' ')

/-- An address as the cell it names: `A[1, 2]` when exactly one buffer owns it, `[13]` otherwise.
A location with two owners is a range that was freed and placed again, and the name that was live
there is not recoverable from the program — the raw address is. -/
def addrStr (L : Layout) (l : Loc) : String :=
  let owners := L.bufs.filter (fun p => p.base ≤ l && l < p.base + p.toBuf.size)
  if owners.length == 1 then (L.nameOf l).getD ("[" ++ toString l ++ "]")
  else "[" ++ toString l ++ "]"

/-- The buffer holding this range, for a computed access. -/
private def refName (L : Layout) (a : ArrRef) : Option String :=
  (L.bufs.find? (fun p => p.base == a.base)).map (fun p => p.name)

/-- An expression, in the `.prl` grammar. -/
def expStr : AExp → String
  | .lit n   => toString n
  | .reg r   => "%" ++ toString r
  | .add a b => "(" ++ expStr a ++ " + " ++ expStr b ++ ")"
  | .sub a b => "(" ++ expStr a ++ " - " ++ expStr b ++ ")"
  | .mul a b => "(" ++ expStr a ++ " * " ++ expStr b ++ ")"
  | .div a b => "(" ++ expStr a ++ " / " ++ expStr b ++ ")"
  | .min a b => "min(" ++ expStr a ++ ", " ++ expStr b ++ ")"
  | .max a b => "max(" ++ expStr a ++ ", " ++ expStr b ++ ")"

mutual

/-- The lines of one statement, indented to depth `d`. -/
partial def stmtLines (L : Layout) (d : Nat) : ParProg → List String
  | .load r l      => [ind d ++ "%" ++ toString r ++ " := " ++ addrStr L l]
  | .store l e     => [ind d ++ addrStr L l ++ " := " ++ expStr e]
  | .set r e       => [ind d ++ "%" ++ toString r ++ " := " ++ expStr e]
  | .seq a b       => stmtLines L d a ++ stmtLines L d b
  | .par ss        => parLines L d ss none
  | .label nm s    =>
      match s with
      | .par ss => parLines L d ss (some nm)
      | _       => (ind d ++ "-- " ++ nm) :: stmtLines L d s
  | .loadAt r a e  =>
      [ind d ++ "%" ++ toString r ++ " := "
        ++ (refName L a).getD ("[" ++ toString a.base ++ "]") ++ "[" ++ expStr e ++ "]"]
  | .storeAt a e v =>
      [ind d ++ (refName L a).getD ("[" ++ toString a.base ++ "]")
        ++ "[" ++ expStr e ++ "] := " ++ expStr v]
  | .ifElse c t e  =>
      let eb := stmtLines L (d + 1) e
      (ind d ++ "if " ++ expStr c ++ " {") :: stmtLines L (d + 1) t
        ++ (if eb.isEmpty then [ind d ++ "}"] else (ind d ++ "} else {") :: eb ++ [ind d ++ "}"])

/-- `parallel {…} | {…}`, one thread per group, with an optional `:: "name"`. -/
partial def parLines (L : Layout) (d : Nat) (ss : List ParProg) (nm : Option String) :
    List String :=
  let bodies := ss.map (stmtLines L (d + 1))
  let tail := nm.elim "" (fun n => " :: \"" ++ n ++ "\"")
  match bodies with
  | []      => [ind d ++ "parallel {" ++ tail, ind d ++ "}"]
  | b :: bs =>
      (ind d ++ "parallel {") :: b
        ++ (bs.flatMap (fun c => (ind d ++ "} | {") :: c))
        ++ [ind d ++ "}" ++ tail]

end

/-- A buffer's declaration; `at` appears only when the base is not the allocator's. -/
def declStr (p : Placed) (expected : Loc) : String :=
  let shape := if p.shape.isEmpty then "" else "[" ++ ", ".intercalate (p.shape.map toString) ++ "]"
  let atPart := if p.base == expected then "" else " at " ++ toString p.base
  let init := if p.init.isEmpty then "" else " = " ++ ", ".intercalate (p.init.map toString)
  "buf " ++ p.name ++ shape ++ atPart ++ init

/-- Buffers a later declaration overlaps: these must have been freed before it. -/
def reused (L : Layout) : List String := go L.bufs []
where
  go : List Placed → List Placed → List String
    | [],      _    => []
    | p :: ps, live =>
        let hit := live.filter (fun q =>
          !(decide (q.base + q.toBuf.size ≤ p.base) || decide (p.base + p.toBuf.size ≤ q.base)))
        hit.map (fun q => q.name)
          ++ go ps ((live.filter (fun q => !(hit.map (fun r => r.name)).contains q.name)) ++ [p])

/-- Every declaration, in placement order, with a `free` wherever a later buffer reclaims an
earlier one's space — which is what a base below the allocator's cursor means. -/
def declLines (L : Layout) : List String := go L.bufs 0 []
where
  go : List Placed → Loc → List Placed → List String
    | [],      _,    _    => []
    | p :: ps, next, live =>
        let hit := live.filter (fun q =>
          !(decide (q.base + q.toBuf.size ≤ p.base) || decide (p.base + p.toBuf.size ≤ q.base)))
        hit.map (fun q => "free " ++ q.name)
          ++ declStr p next
          :: go ps (max next (p.base + p.toBuf.size))
               ((live.filter (fun q => !(hit.map (fun r => r.name)).contains q.name)) ++ [p])

/-- **A compiled file as `.prl` text.** A `free` that returned space is printed where the space is
claimed again; one that only ended a name's scope is printed after the program, where it has the
same effect and cannot shadow the statements that still use the name. -/
def print (c : Compiled) : String :=
  let ds := declLines c.layout
  let late := (c.dead.filter (fun n => !(reused c.layout).contains n)).map (fun n => "free " ++ n)
  "\n".intercalate (ds ++ (if ds.isEmpty then [] else [""]) ++ stmtLines c.layout 0 c.prog
                       ++ (if late.isEmpty then [] else "" :: late)) ++ "\n"

mutual

/-- Right-nest every `;`-chain, descending into forks and branches. `seq` is associative under
`execPar` (`bind` associativity), so this is the normal form the round trip is stated modulo —
`whileAtMost` nests its unrolling the other way. -/
partial def norm (p : ParProg) : ParProg := ParProg.block ((ParProg.flatten p).map normStmt)

partial def normStmt : ParProg → ParProg
  | .par ss       => .par (ss.map norm)
  | .label n s    => .label n (norm s)
  | .ifElse c t e => .ifElse c (norm t) (norm e)
  | s             => s

end

/-- **The round trip**: the printed form reads back as the same program, up to `;`-associativity,
and the same memory. -/
def roundTrips (src : String) : Bool :=
  match ofString src with
  | .error _ => false
  | .ok c    =>
      match ofString (print c) with
      | .error _ => false
      | .ok c'   => norm c'.prog == norm c.prog && c'.dead == c.dead
                      && c'.layout.bufs.map (fun p => p.base) == c.layout.bufs.map (fun p => p.base)
                      && c'.layout.data == c.layout.data

/-! ## Lean out -/

/-- The file as Lean: the `Layout` and the `paralever { … }` block, ready to paste. -/
def toLean (c : Compiled) : String :=
  let bufs := c.layout.bufs.map fun p =>
    "buf \"" ++ p.name ++ "\" " ++ toString p.shape
      ++ (if p.init.isEmpty then "" else " " ++ toString p.init)
  "def L : Layout := Layout.of\n  [ " ++ "\n  , ".intercalate bufs ++ " ]\n\ndef prog : ParProg := "
    ++ AutoPar.surface c.prog ++ "\n"

/-! ## Colour

A scan over the text, not the AST, so a file that does not compile still prints. -/

private def esc : String := String.ofList [Char.ofNat 27]
private def col (n : String) (s : String) : String := esc ++ "[" ++ n ++ "m" ++ s ++ esc ++ "[0m"

/-- ANSI colour for one token class. -/
def paint : String → String → String
  | "comment",  s => col "2"  s
  | "keyword",  s => col "35" s
  | "register", s => col "36" s
  | "number",   s => col "33" s
  | "string",   s => col "32" s
  | "assign",   s => col "1"  s
  | _,          s => s

/-- **`.prl` text with ANSI colour.** -/
partial def highlight (src : String) : String := go src.toList
where
  go : List Char → String
    | [] => ""
    | '-' :: '-' :: rest =>
        let (line, tail) := (rest.takeWhile (· != '\n'), rest.dropWhile (· != '\n'))
        paint "comment" ("--" ++ String.ofList line) ++ go tail
    | ':' :: '=' :: rest => paint "assign" ":=" ++ go rest
    | '"' :: rest =>
        let (body, tail) := (rest.takeWhile (· != '"'), rest.dropWhile (· != '"'))
        paint "string" ("\"" ++ String.ofList body ++ "\"") ++ go (tail.drop 1)
    | '%' :: rest =>
        let (nm, tail) := (rest.takeWhile P.isIdentCont, rest.dropWhile P.isIdentCont)
        paint "register" ("%" ++ String.ofList nm) ++ go tail
    | c :: rest =>
        if c.isDigit then
          let (ds, tail) := (rest.takeWhile Char.isDigit, rest.dropWhile Char.isDigit)
          paint "number" (c.toString ++ String.ofList ds) ++ go tail
        else if P.isIdentStart c then
          let (w, tail) := (rest.takeWhile P.isIdentCont, rest.dropWhile P.isIdentCont)
          let word := c.toString ++ String.ofList w
          (if keywords.contains word then paint "keyword" word else word) ++ go tail
        else c.toString ++ go rest

end Paralever.Prl
