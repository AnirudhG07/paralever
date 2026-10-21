import Paralever.AutoPar.Rewrite

/-! # A scheduled program, printed back as surface text

`surface` emits what `paralever { … }` parses, so the pass's output can be pasted into the language
its input was written in. Kept out of `Rewrite.lean` so that file is the algorithm and nothing else.
-- ref: docs/autopar-algorithm.md § Round trip -/

namespace Paralever.AutoPar
open Paralever Paralever.Prl Paralever.Prl.ParProg

/-! ## Statements

`surface` prints what `paralever { … }` parses. `loadAt`/`storeAt` have no surface form, so they
print as a marker rather than as something that would silently fail to parse. -/

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

mutual

/-- The statements of one program, as surface statements. -/
def surfaceStmts : ParProg → List String
  | .load r l      => ["%" ++ toString r ++ " := [" ++ toString l ++ "]"]
  | .store l e     => ["[" ++ toString l ++ "] := " ++ surfaceExp e]
  | .set r e       => ["%" ++ toString r ++ " := " ++ surfaceExp e]
  | .seq a b       => surfaceStmts a ++ surfaceStmts b
  | .par ss        => ["parallel " ++ String.intercalate " | " (surfaceThreads ss)]
  | .label nm s    => surfaceStmts s ++ ["-- " ++ nm]
  | .loadAt r a e  => ["/- loadAt %" ++ toString r ++ " A" ++ toString a.base
                        ++ "[" ++ surfaceExp e ++ "] : no surface form -/"]
  | .storeAt a e v => ["/- storeAt A" ++ toString a.base ++ "[" ++ surfaceExp e ++ "] := "
                        ++ surfaceExp v ++ " : no surface form -/"]
  | .ifElse c t e  => ["if (" ++ surfaceExp c ++ ") { " ++ String.intercalate "; " (surfaceStmts t)
                        ++ " } else { " ++ String.intercalate "; " (surfaceStmts e) ++ " }"]

/-- Each thread of a fork, braced. -/
def surfaceThreads : List ParProg → List String
  | []      => []
  | s :: ss => ("{ " ++ String.intercalate "; " (surfaceStmts s) ++ " }") :: surfaceThreads ss

end

/-- **A program as surface text**, ready to paste back into `paralever { … }`. -/
def surface (p : ParProg) : String :=
  "paralever {\n  " ++ String.intercalate ";\n  " (surfaceStmts p) ++ "\n}"

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
