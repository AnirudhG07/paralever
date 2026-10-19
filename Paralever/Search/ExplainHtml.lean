import Paralever.Search.Explain
import ProofWidgets.Component.HtmlDisplay

/-! # The counterexample as an infoview widget

The same `Report` as `Search/Explain.lean`, rendered through ProofWidgets. `reportOf` is shared, so
this file contributes a renderer and nothing else. -- ref: `docs/race-search.md` -/

namespace Paralever
open ProofWidgets
open scoped ProofWidgets.Jsx

/-! ### Styling

Inline, and that is forced: ProofWidgets renders a text node as a React Fragment, so a `<style>`
element never receives the string React needs and the stylesheet is silently dropped. Colours are
`--vscode-*` theme variables; `className` carries no weight but names the parts for the guards.
-- ref: `docs/race-search.md` -/

private def sRoot : Lean.Json :=
  json% {display: "flex", flexDirection: "column", gap: "4px", padding: "2px 0",
         fontFamily: "var(--vscode-editor-font-family, monospace)", fontSize: "0.95em"}

private def card (bad : Bool) : Lean.Json :=
  json% {borderRadius: "6px",
         background: "var(--vscode-editorWidget-background, transparent)",
         border: $(Lean.toJson <| if bad
           then "1px solid var(--vscode-inputValidation-errorBorder, #be1100)"
           else "1px solid var(--vscode-panel-border, #8884)")}

private def sHead : Lean.Json :=
  json% {display: "flex", alignItems: "baseline", gap: "10px", padding: "3px 9px",
         flexWrap: "wrap"}

private def sBody : Lean.Json :=
  json% {display: "flex", alignItems: "baseline", flexWrap: "wrap", gap: "3px 6px",
         padding: "3px 9px", borderTop: "1px solid var(--vscode-panel-border, #8884)"}

/-- The `step:thread` identifier, as a pill. The same on every card: a pending step is marked by
its border, and by nothing else. -/
private def pill (_bad : Bool) : Lean.Json :=
  json% {borderRadius: "999px", padding: "0 8px", whiteSpace: "nowrap", fontWeight: "600",
         background: "var(--vscode-activityBarBadge-background, #3794ff)",
         color: "var(--vscode-activityBarBadge-foreground, #ffffff)"}

private def sKey : Lean.Json :=
  json% {fontSize: "0.75em", letterSpacing: "0.08em", textTransform: "uppercase",
         opacity: "0.45", whiteSpace: "nowrap"}

private def cellStyle (changed : Bool) : Lean.Json :=
  json% {display: "inline-flex", gap: "3px", padding: "0 5px", borderRadius: "3px",
         opacity: $(Lean.toJson <| if changed then "1" else "0.65"),
         background: $(Lean.toJson <| if changed
           then "var(--vscode-editor-findMatchHighlightBackground, #ea5c0055)" else "transparent"),
         borderLeft: $(Lean.toJson <| if changed
           then "3px solid var(--vscode-activityBarBadge-background, #3794ff)"
           else "3px solid transparent")}

private def sAbort : Lean.Json :=
  json% {padding: "3px 9px", borderRadius: "6px", fontWeight: "600",
         border: "1px solid var(--vscode-inputValidation-errorBorder, #be1100)"}

private def sFinal : Lean.Json :=
  json% {display: "flex", gap: "10px", padding: "3px 9px", borderRadius: "6px",
         border: "1px dashed var(--vscode-panel-border, #8884)"}

private def sElided : Lean.Json := json% {padding: "1px 9px", opacity: "0.6", fontStyle: "italic"}

private def sNote : Lean.Json := json% {padding: "3px 9px"}

/-! ### Rendering a `Report`

A card per event: the `step:thread` pill, then the action, then the heap it left with the changed
cell picked out. The two actions that clash are cards too, at the same step number and with the
values they would have stored, marked by a red border and nothing else. The abort is the line below
them. -/

private def span_ (cls : String) (st : Lean.Json) (s : String) : Html :=
  <span className={cls} style={st}>{Html.text s}</span>

/-- One heap cell, highlighted when this step changed it. -/
private def cellHtml (c : Cell) : Html :=
  <span className={if c.changed then "pv-cell pv-changed" else "pv-cell"}
        style={cellStyle c.changed}>
    {...#[span_ "pv-loc" (json% {}) c.loc,
          span_ "pv-sep" (json% {opacity: "0.5"}) "↦",
          span_ "pv-val" (json% {}) c.value]}
  </span>

/-- One event: the `step:thread` pill, the action, then the heap. A pending one differs only in
its border. -/
private def stepHtml (s : Step) : Html :=
  <div className={if s.pending then "pv-card pv-pending" else "pv-card"} style={card s.pending}>
    <div className="pv-head" style={sHead}>
      {...#[span_ "pv-id" (pill s.pending) (toString s.time ++ ":" ++ s.thread),
            span_ "pv-act" (json% {whiteSpace: "pre-wrap"}) s.action]}
    </div>
    <div className="pv-body" style={sBody}>
      {...(#[span_ "pv-key" sKey "state"] ++ (s.state.map cellHtml).toArray)}
    </div>
  </div>

/-- A `Report` as a widget. -/
def renderHtml (r : Report) : Html :=
  <div className="pv" style={sRoot}>
    {...(r.map fun i =>
      match i with
      | .step s     => stepHtml s
      | .elided n t => <div className="pv-elided" style={sElided}>
            {Html.text ("⋮  " ++ toString n ++ " steps elided (" ++
              ", ".intercalate (t.map fun (c, k) => c ++ " ×" ++ toString k) ++ ")")}
          </div>
      | .abort n rs => <div className="pv-abort" style={sAbort}>
            {Html.text ("Parallel aborts at Step " ++ toString n ++ ". Reason: " ++ rs ++ ".")}
          </div>
      | .line k v   => <div className="pv-final" style={sFinal}>
            {...#[span_ "pv-key" sKey k, span_ "pv-act" (json% {}) v]}
          </div>
      | .note s     => <div className="pv-note" style={sNote}>{Html.text s}</div>).toArray}
  </div>

/-- The counterexample for a `ParM` program, as a widget. -/
def explainHtmlParM {τ : Type} (nm : LocName) (fuel : Nat) (p pseq : ParM τ) (σ : State)
    (ls : List Loc) : Html :=
  renderHtml (reportOf nm fuel p pseq σ ls)

/-- The counterexample for a `Prog`, as a widget. -/
def explainHtml (p : Prog) (σ : State) : Html :=
  explainHtmlParM rawName p.stepBound p.toParM p.toSeq σ p.locs

open Lean in
/-- `#race p σ` — `p`'s counterexample in the infoview. Arguments bind tightly, so a compound
program needs parentheses: `#race (lateRace 40) σ0`. -/
macro "#race " p:term:max σ:term:max : command => `(#html explainHtml $p $σ)

/-! ### Inspecting a rendered tree

`Html` has no `Repr`, so these walk it. Both ignore attributes: the guards pin structure and text,
not styling. -/

/-- Every `className`, in document order — the hooks the stylesheet selects on. -/
partial def htmlClasses : Html → List String
  | .element _ attrs cs =>
      (match attrs.find? (fun a => a.1 == "className") with
       | some (_, .str c) => [c]
       | _                => []) ++ cs.toList.flatMap htmlClasses
  | .text _             => []
  | .component _ _ _ cs => cs.toList.flatMap htmlClasses

/-- Every element's tag, in document order. -/
partial def htmlTags : Html → List String
  | .element t _ cs     => t :: cs.toList.flatMap htmlTags
  | .text _             => []
  | .component _ _ _ cs => cs.toList.flatMap htmlTags

/-- Every non-blank text node, in document order. -/
partial def htmlText : Html → List String
  | .text s             => if s.trimAscii.toString.isEmpty then [] else [s.trimAscii.toString]
  | .element _ _ cs     => cs.toList.flatMap htmlText
  | .component _ _ _ cs => cs.toList.flatMap htmlText

/-! ## Examples -/

section Examples

private def σ0 : State := fun _ => .int 0

private def late : Prog :=
  .par (.seq (.wr 10 1) (.wr 9 1)) (.seq (.wr 20 1) (.wr 9 2))

private def clean : Prog := .par (.seq (.rd 0) (.wr 1 1)) (.seq (.rd 0) (.wr 2 2))

/-- A **read-after-write** race. The heap ends the same either way, so the divergence is in what
`T0` observes — which is why `runPending` reports read observations and not just the heap. -/
private def raw : Prog := .par (.seq (.wr 1 1) (.rd 9)) (.seq (.wr 2 1) (.wr 9 2))

-- the content: every step, the abort, and the sequential state
/--
info: ["0:T0", "write [10] ← 1", "state", "10", "↦", "1", "9", "↦", "0", "20", "↦", "0", "1:T1", "write [20] ← 1", "state",
  "10", "↦", "1", "9", "↦", "0", "20", "↦", "1", "2:T1", "write [9] ← 2", "state", "10", "↦", "1", "9", "↦", "0", "20",
  "↦", "1", "2:T0", "write [9] ← 1", "state", "10", "↦", "1", "9", "↦", "0", "20", "↦", "1",
  "Parallel aborts at Step 2. Reason: T0, T1 write to: {9}.", "Parallel", "9↦1", "Sequential", "9↦2"]
-/
#guard_msgs in
#eval htmlText (explainHtml late σ0)

-- the parts that carry meaning: a card per executed step with exactly one changed cell, the two
-- pending cards that clash, and the abort line below them
/--
info: ["pv-card", "pv-cell pv-changed", "pv-card", "pv-cell pv-changed", "pv-card pv-pending", "pv-card pv-pending",
  "pv-abort"]
-/
#guard_msgs in
#eval (htmlClasses (explainHtml late σ0)).filter fun c =>
  c.startsWith "pv-card" || c == "pv-cell pv-changed" || c == "pv-abort"

-- no `<style>` element: ProofWidgets cannot deliver one (see above), so styling is inline
/-- info: 0 -/
#guard_msgs in
#eval ((htmlTags (explainHtml late σ0)).filter (fun t => t == "style")).length

-- the read/write case: identical card shapes, two red borders, and an outcome pair whose
-- difference is the value read rather than the heap
/--
info: ["0:T0", "write [1] ← 1", "state", "1", "↦", "1", "9", "↦", "0", "2", "↦", "0", "1:T1", "write [2] ← 1", "state", "1",
  "↦", "1", "9", "↦", "0", "2", "↦", "1", "2:T1", "write [9] ← 2", "state", "1", "↦", "1", "9", "↦", "0", "2", "↦", "1",
  "2:T0", "read [9]", "state", "1", "↦", "1", "9", "↦", "0", "2", "↦", "1",
  "Parallel aborts at Step 2. Reason: T0, T1 access: {9}.", "Parallel", "9↦2, T0 reads 2", "Sequential",
  "9↦2, T0 reads 0"]
-/
#guard_msgs in
#eval htmlText (explainHtml raw σ0)

-- a clean program has no trace, so no step cards at all
/--
info: ["pv", "pv-note", "pv-final", "pv-key", "pv-act"]
-/
#guard_msgs in
#eval htmlClasses (explainHtml clean σ0)

-- the shared model itself: both renderers walk this list of items
/--
info: ["step", "step", "step", "step", "abort", "line", "line"]
-/
#guard_msgs in
#eval (reportOf rawName late.stepBound late.toParM late.toSeq σ0 late.locs).map
  (fun i => match i with
    | .step _     => "step"
    | .elided _ _ => "elided"
    | .abort _ _  => "abort"
    | .line _ _   => "line"
    | .note _     => "note")

/-! ### The widget itself

Put the cursor on one to see the panel; `#html` produces no message, so a batch build shows nothing.
`late` is write/write, `raw` read-after-write, `clean` has nothing to report. -/

#race late σ0
#race raw σ0
#race clean σ0

-- `explainHtmlParM` for a hand-written `ParM`, with addresses named by any `Loc → String`
#html explainHtmlParM (fun l => if l == 9 then "flag" else toString l)
  late.stepBound late.toParM late.toSeq σ0 late.locs

end Examples

end Paralever
