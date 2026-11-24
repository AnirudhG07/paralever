import Lang.Report

/-! # `--json` — what `check` decided, as data

Hand-rolled, because the only dependency this project has is Mathlib and a JSON writer is forty
lines. Nothing here decides anything: every field is a value `Lang.checkReport` already computes,
so the text report and the JSON cannot disagree. -- ref: `docs/cli.md` § `--json` -/

namespace Paralever.Tool
open Paralever Paralever.Lang

/-! ## Writing it -/

/-- A string as a JSON literal: the five escapes the grammar requires, and `\uXXXX` for the rest of
the control range. The reports hold em dashes and arrows, which are legal UTF-8 and pass through. -/
def jsonStr (s : String) : String :=
  "\"" ++ (s.toList.map esc).foldl (· ++ ·) "" ++ "\""
where
  esc (c : Char) : String :=
    if c == '"' then "\\\""
    else if c == '\\' then "\\\\"
    else if c == '\n' then "\\n"
    else if c == '\r' then "\\r"
    else if c == '\t' then "\\t"
    else if c.toNat < 0x20 then
      let hex := Nat.toDigits 16 c.toNat
      "\\u" ++ "".intercalate (List.replicate (4 - hex.length) "0") ++ String.ofList hex
    else String.singleton c

/-- `[a, b, c]`. -/
def jsonArr (xs : List String) : String := "[" ++ ", ".intercalate xs ++ "]"

/-- `{"k": v, …}`, with the pairs already rendered. -/
def jsonObj (kvs : List (String × String)) : String :=
  "{" ++ ", ".intercalate (kvs.map (fun (k, v) => jsonStr k ++ ": " ++ v)) ++ "}"

def jsonNat (n : Nat) : String := toString n
def jsonBool (b : Bool) : String := if b then "true" else "false"

/-! ## What `check` found -/

/-- One declared buffer. -/
private def bufJson (c : Compiled) (p : Placed) : String :=
  jsonObj
    [ ("name",  jsonStr p.name)
    , ("shape", jsonArr (p.shape.map jsonNat))
    , ("base",  jsonNat p.base)
    , ("cells", jsonNat p.toBuf.size)
    , ("freed", jsonBool (c.dead.contains p.name)) ]

/-- The verdict's halves, each a scope and what holds under it. -/
private def verdictJson (c : Compiled) : String :=
  jsonArr ((verdictParts c).map (fun (scope, text) =>
    jsonObj [("scope", jsonStr scope), ("holds", jsonStr text)]))

/-- Which route settled it: `wfB` syntactically, the exact per-heap check, or neither. -/
private def routeJson (c : Compiled) : String :=
  if ParProg.wfB c.prog then jsonStr "wfB"
  else if (raceSites (ParProg.execPar c.prog (fun _ => 0)) c.layout.state).isEmpty then
    jsonStr "exact"
  else jsonStr "none"

/-- The file's claim, when it states one. -/
private def claimJson (c : Compiled) : String :=
  match c.claim with
  | none    => "null"
  | some cl =>
      let (stated, held) := claimParts c cl
      jsonObj
        [ ("stated", jsonStr stated)
        , ("holds",  jsonStr held)
        , ("agrees", jsonBool (claimHolds c)) ]

/-- **`paralever check --json`.** The same facts the text report prints, as one object per line so
that `grep` still works on it and `jq` does too. -/
def checkJson (name : String) (c : Compiled) (timeMs : Option String) : String :=
  let L := c.layout
  let nm := c.locName
  let f := ParProg.footprintOf c.prog
  let ρ : Regs := fun _ => 0
  let b := ParProg.stepBound c.prog
  let rounds :=
    if roundsCeiling < b then
      jsonObj [("measured", "false"), ("bound", jsonNat b)]
    else
      jsonObj
        [ ("measured",   "true")
        , ("parallel",   jsonNat (time (ParProg.execPar c.prog ρ) L.state))
        , ("sequential", jsonNat (time (ParProg.execSeq c.prog ρ) L.state)) ]
  "{\n  " ++ ",\n  ".intercalate (
    [ jsonStr "file"    ++ ": " ++ jsonStr name
    , jsonStr "memory"  ++ ": " ++ jsonArr (L.bufs.map (bufJson c))
    , jsonStr "cells"   ++ ": " ++ jsonNat L.size
    , jsonStr "reads"   ++ ": " ++ jsonArr ((nubLocs f.reads).map (fun l => jsonStr (nm l)))
    , jsonStr "writes"  ++ ": " ++ jsonArr ((nubLocs f.writes).map (fun l => jsonStr (nm l)))
    , jsonStr "stray"   ++ ": " ++ jsonArr ((L.strayLocs f).map jsonNat)
    , jsonStr "threads" ++ ": " ++ jsonNat (ParProg.threadCount c.prog)
    , jsonStr "rounds"  ++ ": " ++ rounds
    , jsonStr "route"   ++ ": " ++ routeJson c
    , jsonStr "proved"  ++ ": " ++ jsonBool (ParProg.wfB c.prog
        || (raceSites (ParProg.execPar c.prog ρ) L.state).isEmpty)
    , jsonStr "verdict" ++ ": " ++ verdictJson c
    , jsonStr "claim"   ++ ": " ++ claimJson c ]
    ++ (match timeMs with
        | none   => []
        | some t => [jsonStr "time_ms" ++ ": " ++ t])) ++ "\n}\n"

end Paralever.Tool
