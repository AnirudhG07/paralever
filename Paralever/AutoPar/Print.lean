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

/-- One `print` item, in the surface spelling. -/
def surfaceItem : PrintItem → String
  | .text t        => "\"" ++ t ++ "\""
  | .exp e         => surfaceExp e
  | .buf nm _ _    => nm
  | .at nm _ e     => nm ++ "[" ++ surfaceExp e ++ "]"
  | .cell nm idx _ =>
      if idx.isEmpty then nm
      else nm ++ "[" ++ String.intercalate ", " (idx.map toString) ++ "]"

mutual

/-- The statements of one program, as surface statements. `partial` because the `label` case looks
at what it labels, as `Lang.stmtLines` does — printing, so nothing is proved about it. -/
partial def surfaceStmts (rs : RefStr) : ParProg → List String
  | .load r l      => ["%" ++ toString r ++ " := [" ++ toString l ++ "]"]
  | .store l e     => ["[" ++ toString l ++ "] := " ++ surfaceExp e]
  | .set r e       => ["%" ++ toString r ++ " := " ++ surfaceExp e]
  | .seq a b       => surfaceStmts rs a ++ surfaceStmts rs b
  | .par ss        => ["parallel " ++ String.intercalate " | " (surfaceThreads rs ss)]
  | .label nm s    =>
      match s with
      | .par ss => ["parallel " ++ String.intercalate " | " (surfaceThreads rs ss)
                      ++ " :: \"" ++ nm ++ "\""]
      | _       => ["{ " ++ String.intercalate "; " (surfaceStmts rs s) ++ " } :: \"" ++ nm ++ "\""]
  | .synchronize   => ["synchronize"]
  | .print is      => ["print " ++ String.intercalate ", " (is.map surfaceItem)]
  | .loadAt r a e  => ["%" ++ toString r ++ " := [" ++ rs a ++ ", " ++ surfaceExp e ++ "]"]
  | .storeAt a e v => ["[" ++ rs a ++ ", " ++ surfaceExp e ++ "] := " ++ surfaceExp v]
  | .ifElse c t e  => ["if (" ++ surfaceExp c ++ ") { "
                        ++ String.intercalate "; " (surfaceStmts rs t)
                        ++ " } else { " ++ String.intercalate "; " (surfaceStmts rs e) ++ " }"]
  -- a rolled nest has no surface form yet; printed in the Lean form's vocabulary so the pass's
  -- output is still readable -- ref: `docs/loops.md`
  | .loop n        => ["parfor " ++ String.intercalate ", " (showLevels n.ivs n.sizes n.lo n.step)
                        ++ " fork " ++ toString n.parDepth ++ " { "
                        ++ String.intercalate "; " (n.body.map showNestStmt) ++ " }"]

/-- Each thread of a fork, braced. -/
partial def surfaceThreads (rs : RefStr) : List ParProg → List String
  | []      => []
  | s :: ss => ("{ " ++ String.intercalate "; " (surfaceStmts rs s) ++ " }") :: surfaceThreads rs ss

end

/-- **A program as surface text**, ready to paste back into `paralever { … }`. -/
def surface (p : ParProg) (rs : RefStr := refPair) : String :=
  "paralever {\n  " ++ String.intercalate ";\n  " (surfaceStmts rs p) ++ "\n}"

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
