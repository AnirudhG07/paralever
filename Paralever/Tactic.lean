import Paralever.Search.ExplainHtml
import Prl.Lang.Core
import Lean

/-! # Two tactics: the theorem first, the counterexample second

`paralever_race` is the `#race` command in tactic position. It takes no program: it reads the goal
in hand, runs the same search `Search/RaceSearch.lean` runs, and renders the same widget
`Search/ExplainHtml.lean` builds. The goal is left untouched — this is a diagnostic.

`paralever_check` is the two in the order a proof wants them. It tries to *prove* the goal first,
one route at a time, and only when none of them discharges the obligation does it run the search
and fail with the interleaving attached. A failure therefore says which of the two things happened:
no route proved it, or there is a race and no route could.

Both read the goal as a `ParSeqEq p q σ`. A goal quantified over its heap or its register file has
no values for the search to run on, so those are replaced by the zeros a compiled file's run starts
from — and the widget says which. -- ref: `docs/race-search.md`, `docs/cli.md` -/

namespace Paralever
open Lean Meta Elab Tactic ProofWidgets Server

/-! ## What the search needs and a goal does not carry

Three things: a heap, a register file, and a bound on the steps a schedule may take. The first two
are in the goal when the goal is about a particular heap, and are quantified variables otherwise.
The third is never in the goal. -/

/-- The register file every run of a compiled file starts from. -/
def zeroRegs : Regs := fun _ => 0

/-- The heap whose every cell is `0`. -/
def zeroHeap : State := fun _ => .int 0

/-- Steps the search may spend: the memory actions of the canonical run, twice over, with room for
the joins. A bound rather than a guess — a racy schedule aborts at a prefix of the canonical run,
so it cannot take more actions than that run takes. `ParProg.stepBound` is the exact count for a
compiled program; this is the form that also works for a `ParM` written by hand. -/
def fuelOf {α : Type} (p : ParM α) (σ : State) : Nat :=
  let f := accesses p σ
  2 * (f.reads.length + f.writes.length) + 16

/-- The cells the widget follows: every one the canonical run touches. -/
def cellsOf {α : Type} (p : ParM α) (σ : State) : List Loc :=
  let f := accesses p σ
  nubLocs (f.reads ++ f.writes)

/-- What the two tactics report. The widget is what the infoview shows; `text` is the same trace
rendered as text, which is what a terminal and a batch build see; `raced` is the exact check's
verdict, and it is the one thing that distinguishes "no proof found" from "no proof exists". -/
structure Findings where
  html  : Html
  text  : String
  line  : String
  raced : Bool

/-- **The goal's counterexample.** `notes` is what the tactic had to assume to run at all, and it
is rendered above the trace rather than dropped.

`raceSites` is complete for the obligation (`raceSites_nil_iff`), so an empty list means the
obligation really does hold at this heap and only the proof is missing. -/
def goalFindingsOf {α : Type} (notes : List String) (p q : ParM α) (σ : State) : Findings :=
  let r := notes.map Item.note ++ reportOf rawName (fuelOf p σ) p q σ (cellsOf p σ)
  let sites := raceSites p σ
  { html  := renderHtml r
  , text  := renderText r
  , line  :=
      if sites.isEmpty then
        "the exact check finds no conflicting access at this heap, so the obligation holds here"
      else
        toString sites.length ++ " conflicting fork(s), on "
          ++ clipLocs 8 (nubLocs (sites.flatMap (fun s => s.conflicts)))
  , raced := !sites.isEmpty }

/-! ## Reading the goal

`evalExpr` runs a closed term, which is what the search is: a function of the program and the heap,
both of which are data in the goal. -/

namespace Tactic

private unsafe def evalHtmlUnsafe (e : Expr) : MetaM Html :=
  evalExpr Html (mkConst ``Html) e

@[implemented_by evalHtmlUnsafe]
private opaque evalHtmlExpr (e : Expr) : MetaM Html

private unsafe def evalFindingsUnsafe (e : Expr) : MetaM Findings :=
  evalExpr Findings (mkConst ``Findings) e

@[implemented_by evalFindingsUnsafe]
private opaque evalFindingsExpr (e : Expr) : MetaM Findings

/-- A variable the goal quantifies over, replaced by the zeros a run starts from. A counterexample
at one heap is not a counterexample at every heap, so each substitution is recorded. -/
private def ground (e : Expr) (notes : Array String) : MetaM (Expr × Array String) := do
  let mut e := e
  let mut notes := notes
  for fv in (collectFVars {} e).fvarIds do
    let t ← instantiateMVars (← inferType (mkFVar fv))
    let nm := (← fv.getUserName).toString
    if ← isDefEq t (mkConst ``Regs) then
      e := e.replaceFVarId fv (mkConst ``zeroRegs)
      notes := notes.push s!"`{nm}` is a variable, so the registers are all 0 below"
    else if ← isDefEq t (mkConst ``State) then
      e := e.replaceFVarId fv (mkConst ``zeroHeap)
      notes := notes.push s!"`{nm}` is a variable, so the heap below is the one whose cells are all \
                             0: what it shows holds at that heap, not at every heap"
    else
      throwError "the goal depends on {mkFVar fv} : {t}, which the search has no value for"
  pure (e, notes)

/-- The search, run on the goal in hand. -/
def goalFindings : TacticM Findings := do
  let goal ← instantiateMVars (← whnfR (← getMainTarget))
  let_expr ParSeqEq _α p q σ := goal
    | throwError "paralever: the goal is not a `ParSeqEq p q σ`:{indentExpr goal}"
  let (p, notes) ← ground p #[]
  let (q, notes) ← ground q notes
  let (σ, notes) ← ground σ notes
  for e in [p, q, σ] do
    if e.hasMVar then
      throwError "the goal still has a metavariable in it, so there is nothing to \
                  run:{indentExpr e}"
  -- one note per assumption, not one per place the variable occurred
  let notesE ← mkListLit (mkConst ``String) (notes.toList.eraseDups.map mkStrLit)
  evalFindingsExpr (← mkAppM ``goalFindingsOf #[notesE, p, q, σ])

/-- The widget, in the infoview panel, where `#html` puts it. -/
def showHtml (h : Html) : TacticM Unit := do
  Widget.savePanelWidgetInfo (hash HtmlDisplayPanel.javascript)
    (return json% { html: $(← rpcEncode h) }) (← getRef)

/-- **`paralever_race`** — the interleaving that disagrees, for the goal in hand, as the infoview
widget. The goal is left alone; the line it logs is what a batch build sees, since a widget shows
nothing there. -/
elab (name := paraleverRace) "paralever_race" : tactic => do
  let f ← goalFindings
  showHtml f.html
  logInfo (f.line ++ "\n" ++ f.text)

/-! ## The routes to a proof

In the order they are tried. `grind` first, as asked of it; it will not discharge `wfB s = true`,
because `wfB s` is a closed Boolean computation and `grind` has nothing to rewrite it with — it
treats the application as an atom and reports the goal unproved. The two that follow evaluate it.
The fourth route is the per-heap one: `wfB` refuses a computed address, where `wellFormedB` at the
goal's heap does not (`docs/block-ir.md`). The fifth is the same for a `ParM` written by hand
rather than compiled. -/

private def routes : TacticM (List (TSyntax `tactic)) := do
  pure
    [ ← `(tactic| refine Prl.ParProg.par_seq_eq ?_ _ _ <;> grind)
    , ← `(tactic| refine Prl.ParProg.par_seq_eq ?_ _ _ <;> simp +decide)
    , ← `(tactic| refine Prl.ParProg.par_seq_eq ?_ _ _ <;> decide)
    , ← `(tactic| refine parSeqEq_of_runSeq_eq _ _ _
                    ((wellFormedB_iff _ _).1 ?_) ((wellFormedB_iff _ _).1 ?_)
                    (Prl.ParProg.execPar_runSeq_all.1 _ _ _) <;> decide)
    , ← `(tactic| refine par_seq_eq _ _ _ ((wellFormedB_iff _ _).1 ?_) <;> decide)
    , ← `(tactic| refine parSeqEq_of_runSeq_eq _ _ _
                    ((wellFormedB_iff _ _).1 ?_) ((wellFormedB_iff _ _).1 ?_) rfl <;> decide) ]

/-- **`paralever_check`** — prove the goal if any route does, and otherwise say why not, with the
interleaving. On failure the error names which of the two cases happened, because they call for
different things: a race means no theorem of this shape exists, and no race means the obligation
holds and only the proof is missing. -/
elab (name := paraleverCheck) "paralever_check" : tactic => do
  -- Two things a route has to clear. `withoutErrToSorry`, or an elaboration failure inside it
  -- becomes a hole whose error arrives after this tactic has returned; and no goal left, because
  -- `simp` counts rewriting `wfB s = true` to `False` as progress and would otherwise be taken
  -- for a proof.
  for t in ← routes do
    let st ← saveState
    let ok ← (do
      try
        Term.withoutErrToSorry (evalTactic t)
        pure (← getGoals).isEmpty
      catch _ => pure false)
    if ok then return () else st.restore
  let f ← goalFindings
  showHtml f.html
  -- the widget in the infoview, the same trace as text wherever a widget cannot render
  let md ← MessageData.ofHtml f.html f.text
  if f.raced then
    throwError "paralever_check: this program has a race, so no instance of `par_seq_eq` \
                exists for it — {f.line}.{indentD md}"
  else
    throwError "paralever_check: no route discharged the obligation, but {f.line}. The routes are \
                `par_seq_eq` with `grind`, with `simp +decide` and with `decide`, then the \
                per-heap `wellFormedB` route; a program this large can exhaust `maxRecDepth`, \
                which `set_option maxRecDepth` raises.{indentD md}"

end Tactic
end Paralever
