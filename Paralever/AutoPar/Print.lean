import Paralever.AutoPar.Rewrite

/-! # A scheduled program, printed back as surface text

`surface` emits what `paralever { … }` parses, so the pass's output can be pasted into the language
its input was written in. Kept out of `Rewrite.lean` so that file is the algorithm and nothing else.
-- ref: docs/autopar-algorithm.md § Round trip -/

namespace Paralever.AutoPar
open Paralever Paralever.Lang Paralever.Lang.ParProg

/-! ## Statements

`surface` prints what `paralever { … }` parses, and every constructor has a form: a computed access
is `[A, e]` and a label on anything but a fork is `{ … } :: "name"`. A range prints as the pair it
is unless the caller knows its name — `Lang.toLean` does, and passes `L.ref "A"`.
-- ref: docs/prl.md § The Lean form -/

/-- How a range prints: a term the notation accepts in `[A, e]`. -/
abbrev RefStr := ArrRef → String

/-- The pair itself, for a caller with no layout to name it by. -/
def refPair : RefStr := fun a => "(ArrRef.mk " ++ toString a.base ++ " " ++ toString a.len ++ ")"

/-- An expression as a term the surface syntax accepts. -/
def surfaceExp : AExp → String
  | .lit n   => if n < 0 then "AExp.lit (" ++ toString n ++ ")" else toString n
  | .reg r   => "%" ++ toString r
  | .add a b => "(" ++ surfaceExp a ++ " + " ++ surfaceExp b ++ ")"
  | .sub a b => "(" ++ surfaceExp a ++ " - " ++ surfaceExp b ++ ")"
  | .mul a b => "(" ++ surfaceExp a ++ " * " ++ surfaceExp b ++ ")"
  | .min a b => "AExp.min (" ++ surfaceExp a ++ ") (" ++ surfaceExp b ++ ")"
  | .max a b => "AExp.max (" ++ surfaceExp a ++ ") (" ++ surfaceExp b ++ ")"
  | .div a b => "AExp.div (" ++ surfaceExp a ++ ") (" ++ surfaceExp b ++ ")"
  | .lt a b  => "AExp.lt (" ++ surfaceExp a ++ ") (" ++ surfaceExp b ++ ")"
  | .eq a b  => "AExp.eq (" ++ surfaceExp a ++ ") (" ++ surfaceExp b ++ ")"
  | .not a   => "AExp.not (" ++ surfaceExp a ++ ")"

/-- One `print` item, as the term the Lean form's `print` takes. `.prl` spells an item by name;
the notation takes a `List PrintItem`, so each one is written out. -/
def surfaceItem (rs : RefStr) : PrintItem → String
  | .text t        => "PrintItem.text \"" ++ t ++ "\""
  | .exp e         => "PrintItem.exp (" ++ surfaceExp e ++ ")"
  | .buf nm sh l   =>
      "PrintItem.buf \"" ++ nm ++ "\" " ++ toString sh ++ " " ++ toString l
  | .at nm a e     =>
      "PrintItem.at \"" ++ nm ++ "\" (" ++ rs a ++ ") (" ++ surfaceExp e ++ ")"
  | .cell nm idx l =>
      "PrintItem.cell \"" ++ nm ++ "\" " ++ toString idx ++ " " ++ toString l

/-- Two spaces per level. -/
private def ind (d : Nat) : String := String.ofList (List.replicate (2 * d) ' ')

/-- A braced body: the statements one per line, `;`-separated because `paralever { … }` parses
`sepBy1(impStmt, "; ")` and Lean's tokenizer does not see line breaks. -/
private def braced (d : Nat) (head : String) (body : List String) (tail : String) : String :=
  ind d ++ head ++ "\n" ++ ";\n".intercalate body ++ "\n" ++ ind d ++ tail

mutual

/-- The statements of one program, each indented to `d` and each possibly several lines. `partial`
because the `label` case looks at what it labels, as `Lang.stmtLines` does — printing, so nothing is
proved about it. -/
partial def surfaceStmts (rs : RefStr) (d : Nat) : ParProg → List String
  | .load r l      => [ind d ++ "%" ++ toString r ++ " := [" ++ toString l ++ "]"]
  | .store l e     => [ind d ++ "[" ++ toString l ++ "] := " ++ surfaceExp e]
  | .set r e       => [ind d ++ "%" ++ toString r ++ " := " ++ surfaceExp e]
  | .seq a b       => surfaceStmts rs d a ++ surfaceStmts rs d b
  | .par ss        => [surfaceFork rs d ss ""]
  | .label nm s    =>
      match s with
      | .par ss => [surfaceFork rs d ss (" :: \"" ++ nm ++ "\"")]
      | _       => [braced d "{" (surfaceStmts rs (d + 1) s) ("} :: \"" ++ nm ++ "\"")]
  | .synchronize   => [ind d ++ "synchronize"]
  | .print is      =>
      [ind d ++ "print [" ++ String.intercalate ", " (is.map (surfaceItem rs)) ++ "]"]
  | .loadAt r a e  => [ind d ++ "%" ++ toString r ++ " := [" ++ rs a ++ ", " ++ surfaceExp e ++ "]"]
  | .storeAt a e v => [ind d ++ "[" ++ rs a ++ ", " ++ surfaceExp e ++ "] := " ++ surfaceExp v]
  | .ifElse c t e  =>
      [ braced d ("if (" ++ surfaceExp c ++ ") {") (surfaceStmts rs (d + 1) t) "} else {"
          ++ "\n" ++ ";\n".intercalate (surfaceStmts rs (d + 1) e) ++ "\n" ++ ind d ++ "}" ]
  -- a rolled nest has no surface form yet; printed in the Lean form's vocabulary so the pass's
  -- output is still readable -- ref: `docs/loops.md`
  | .loop n        =>
      [ braced d ("parfor " ++ String.intercalate ", " (showLevels n.ivs n.sizes n.lo n.step)
                   ++ " fork " ++ toString n.parDepth ++ " {")
          (n.body.map (fun st => ind (d + 1) ++ showNestStmt st)) "}" ]

/-- A fork: each thread braced, the opening brace of the next on the closing brace of the last. -/
partial def surfaceFork (rs : RefStr) (d : Nat) (ss : List ParProg) (tail : String) : String :=
  ind d ++ "parallel {\n"
    ++ (("\n" ++ ind d ++ "} | {\n").intercalate
          (ss.map (fun t => ";\n".intercalate (surfaceStmts rs (d + 1) t))))
    ++ "\n" ++ ind d ++ "}" ++ tail

end

/-- **A program as surface text**, ready to paste back into `paralever { … }`. -/
def surface (p : ParProg) (rs : RefStr := refPair) : String :=
  "paralever {\n" ++ ";\n".intercalate (surfaceStmts rs 1 p) ++ "\n}"

/-- **The round trip.** `paralever { … }` in, `paralever { … }` out, with the plan's numbers. -/
def report (p : ParProg) : String :=
  let (d, l, s) := quality p
  surface (rewrite p)
    ++ "\n-- units      " ++ toString (units p).length
    ++ "\n-- stages     " ++ toString (planOf p).length
    ++ "\n-- threads    " ++ toString (threads (planOf p)).length
    ++ "\n-- depth      " ++ toString d ++ "  (sequential " ++ toString s
                          ++ ", lower bound " ++ toString l ++ ")"
    ++ "\n-- optimal    " ++ toString (optimalB p)
    ++ "\n-- committed  " ++ toString (rewriteOk p)

end Paralever.AutoPar
