import VersoSlides
import Verso.Doc.Concrete
import Paralever
import Lang.Core.Cost
import Examples.Programs.MatMul
import Examples.Programs.MergeSort
import Examples.Programs.SumArray
import Examples.Language.NeuralNet
import Examples.Races.Caught

set_option verso.code.warnLineLength 500
set_option verso.slides.panel false
set_option linter.unusedVariables false
set_option verso.slides.warnOnImage false

open VersoSlides
open Paralever

#doc (Slides) "Paralever — ISP" =>
# paralever

%%%
state := "title"
%%%

:::class "subheader"
Verifying Equivalence of Parallel Program and its Sequential Counterpart — in Lean 4
:::

:::class "byline lead"
Anirudh Gupta
:::

:::class "byline"
4th-year B.Tech Mathematics and Computing
:::

:::class "byline"
Indian Institute of Science, Bengaluru
:::


:::class "event ruled"
ISP - I Presentation
:::

:::class "byline"
Advised by Prof. Siddhartha Gadgil
:::


:::class "links"
[github.com/AnirudhG07/paralever](https://github.com/AnirudhG07/paralever)
:::



# Overview

:::class "steps"
* *Motivation*
* *Independence and WellFormedness*
* *Language Framework*
* *Proof of Equivalence*
* *Parallel Programs are Faster*
* *Examples*
* *Autoparallelization*
* *Races and MLIR*
* *Performance of Paralever*
* *Limitations*
:::

# Motivation

%%%
state := "section"
%%%

:::class "steps"
* Consider the two jobs run sequentially separately or parallely(in arbitrary order).  Does the memory come out the same?
:::

```html
<div class="dgm col">
  <div class="dgm tight">
    <div class="nd mono good">[5] := 1</div>
    <div class="arr">∥</div>
    <div class="nd mono good">[8] := [<b>7</b>]</div>
    <div class="arr lbl2">→<small>touch different cells</small></div>
    <div class="nd key">one heap</div>
  </div>
  <div class="dgm tight">
    <div class="nd mono bad">[5] := 1</div>
    <div class="arr">∥</div>
    <div class="nd mono bad">[8] := [<b>5</b>]</div>
    <div class="arr lbl2">→<small>share cell 5</small></div>
    <div class="nd key">two heaps</div>
  </div>
</div>
```

```html
<div class="dgm col">
  <div class="dgm tight">
    <div class="nd plain">left first</div>
    <div class="nd mono">[5] := 1<em>[5] = 1  [8] = 0</em></div>
    <div class="arr">→</div>
    <div class="nd mono">[8] := [5]<em>[5] = 1  [8] = <b>1</b></em></div>
  </div>
  <div class="dgm tight">
    <div class="nd plain">right first</div>
    <div class="nd mono">[8] := [5]<em>[5] = 0  [8] = 0</em></div>
    <div class="arr">→</div>
    <div class="nd mono">[5] := 1<em>[5] = 1  [8] = <b>0</b></em></div>
  </div>
</div>
```

:::class "steps fragment"
* Clearly the two parallel executions do not yield the same heap.
* Under what conditions can we guarantee that the parallel execution is equivalent to the sequential execution?
:::

# Problem Statement

::::fragment

:::class "steps"
Some definitions to know:

* *State* — `σ : Loc → Val`, a total heap. A *configuration* is a program paired with a heap,
  `(p, σ)`, or `wrong`, which is terminal and absorbing.
* *Step* — `(p, σ) → c'` lists the successors of a configuration. A fork offers *every* ready
  child, so that list is the nondeterminism itself.
* *Interleaving* — a finite chain `c → c₁ → … → c'`. `Reaches c c'` holds when one joins them.
* *`seq p q`* — `p` to completion, then `q`: one chain, no choice. *`par p q`* — the fork,
  joined once every child is `pure`.
* *`WellFormed p σ`* — at *every* fork in `p`, against the heap that fork actually sees, the
  children's footprints are pairwise independent, and each child is itself well-formed. `Indep` is
  the clause at one fork; `WellFormed` is the recursive condition the theorem takes.
:::

::::

```html
<div class="fragment" style="padding-top: 2em">
  <div class="rulewrap"><div class="rule">
    <div class="prem">p : ParM α    q : ParM β    σ : State      WellFormed (par p q) σ</div>
    <div class="bar"></div>
    <div class="conc">∀ r σ'.   Reaches (par p q, σ) (pure r, σ')  ⇔  Reaches (seq p q, σ) (pure r, σ')</div>
    <span class="side">par_seq_eq — the conclusion is ParSeqEq (par p q) (seq p q) σ, unfolded</span>
  </div></div>
</div>
```


# Independence and WellFormedness

%%%
state := "section"
%%%

:::class "steps"
* Bernstein's condition of Independence
* Notion of WellFormedness
:::


# Bernstein's condition of Independence

```leanLibCode Paralever.Core.Access (package := paralever) (startLine := 65) (endLine := 66) -stretch
def Indep (f₁ f₂ : Footprint) : Prop :=
  Disjoint f₁.writes f₂.writes ∧ Disjoint f₁.writes f₂.reads ∧ Disjoint f₂.writes f₁.reads
```

```html
<div class="figwrap">
<svg viewBox="0 0 860 180" role="img" aria-label="the three Bernstein clauses as crossings between two footprints">
  <g font-family="ui-monospace, monospace" font-size="14" text-anchor="middle" fill="#0f172a">
    <rect x="40"  y="22" width="130" height="34" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="105" y="44">W₁</text>
    <rect x="40"  y="112" width="130" height="34" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="105" y="134">R₁</text>
    <rect x="690" y="22" width="130" height="34" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="755" y="44">W₂</text>
    <rect x="690" y="112" width="130" height="34" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="755" y="134">R₂</text>
  </g>
  <g stroke-width="2" fill="none">
    <path d="M 172 39 L 688 39"  stroke="#dc2626"/>
    <path d="M 172 44 L 688 125" stroke="#dc2626"/>
    <path d="M 172 125 L 688 44" stroke="#dc2626"/>
    <path d="M 172 131 L 688 131" stroke="#16a34a" stroke-dasharray="6 5"/>
  </g>
  <g font-size="13.5" font-family="var(--sans)" text-anchor="middle">
    <text x="430" y="30"  fill="#dc2626">C1 · W₁ ∩ W₂ = ∅</text>
    <text x="430" y="72"  fill="#dc2626">C2 · W₁ ∩ R₂ = ∅</text>
    <text x="430" y="100" fill="#dc2626">C3 · W₂ ∩ R₁ = ∅</text>
    <text x="430" y="152" fill="#16a34a">no clause on R₁ ∩ R₂ — shared reads are permitted</text>
  </g>
</svg>
</div>
```

:::class "steps"
* A footprint is two Lists of cells, `reads`(R(.)) and `writes`(W(.)). It is computed from the program.
* Independence is a decidable {lean}`Bool` over them.
:::

# Wellformedness: Independence is checked at every fork

%%%
state := "wf"
%%%

:::::hstack
::::vstack
```leanLibCode Paralever.Core.Access (package := paralever) (startLine := 236) (endLine := 242)
def WellFormed {τ : Type} : ParM τ → State → Prop
  | .pure _,      _ => True
  | .read l k,    σ => WellFormed (k (σ l)) σ
  | .write l v k, σ => WellFormed (k ()) (σ.update l v)
  | .par cs k,    σ =>
      let r := runChilds cs σ
      IndepAll (childFootprints cs σ) ∧ WellFormedChilds cs σ ∧ WellFormed (k r.1) r.2
```

:::class "steps"
* *`p` is well formed from heap `σ` if, at every fork reached while running `p` from `σ`, its
  children are pairwise independent, each child is well formed, and execution remains well formed
  after the fork joins.*
* Each child is checked against the heap the child before it left, not against `σ`. The threads are
  independent, so that is also the heap the parallel run reaches.
:::
::::

```html
<div class="figwrap">
<svg viewBox="0 0 430 330" role="img" aria-label="a program tree with an independence check at each of its two forks">
  <g font-family="var(--mono)" font-size="13" text-anchor="middle" fill="#0f172a">
    <rect x="150" y="10" width="110" height="30" rx="6" fill="#eff6ff" stroke="#0073a3" stroke-width="2"/><text x="205" y="30">par</text>
    <rect x="20"  y="105" width="130" height="30" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="85" y="125">write C[0]</text>
    <rect x="245" y="105" width="110" height="30" rx="6" fill="#eff6ff" stroke="#0073a3" stroke-width="2"/><text x="300" y="125">par</text>
    <rect x="185" y="205" width="110" height="30" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="240" y="225">write C[1]</text>
    <rect x="305" y="205" width="110" height="30" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="360" y="225">write C[2]</text>
  </g>
  <g stroke="#94a3b8" stroke-width="1.6" fill="none">
    <path d="M 180 40 L 85 105"/><path d="M 230 40 L 300 105"/>
    <path d="M 280 135 L 240 205"/><path d="M 320 135 L 360 205"/>
  </g>
  <g font-size="12.5" font-family="var(--sans)" fill="#0073a3" text-anchor="middle">
    <text x="205" y="65">IndepAll checked here</text>
    <text x="300" y="165">and here</text>
  </g>
  <text x="215" y="285" font-size="12.5" font-family="var(--sans)" fill="#dc2626" text-anchor="middle">the outermost check alone</text>
  <text x="215" y="305" font-size="12.5" font-family="var(--sans)" fill="#dc2626" text-anchor="middle">is unsound</text>
</svg>
</div>
```
:::::

# Language Framework

%%%
state := "section"
%%%

:::class "steps"
* `ParM`, and why `par` has to be our own constructor.
* The surface language, and the verdict the checker prints.
* `wfB s = true → ParSeqEq (execPar s) (execSeq s)`.
:::

# {lean}`ParM` Monad and `par` constructor

```leanLibCode Paralever.Core.ParM (package := paralever) (startLine := 82) (endLine := 89) -stretch
inductive ParM : Type → Type 1 where
  | pure  {α : Type}     : α → ParM α
  | read  {α : Type}     : Loc → (Val → ParM α) → ParM α
  | write {α : Type}     : Loc → Val → (Unit → ParM α) → ParM α
  /-- Fork every child at once, then continue with all their results. The only constructor whose
  meaning Lean does not already fix: `run` interprets it by interleaving, which is what makes the
  sequentialization theorem non-vacuous. -/
  | par   {β : Type} {αs : List Type} : Childs ParM αs → (Results αs → ParM β) → ParM β
```

:::class "steps"
* The program is a tree of {lean}`ParM` constructors. The tree is data we can inspect.
* {lean}`ParM` is inductive, so every program terminates: `while true` is unrepresentable, and that boundary is fixed by Lean having no coinductive types.
:::

:::class "steps"
* *Why not Lean's `Task`?* `(Task.spawn f).get = f ()` holds by `rfl`, so parallel and sequential
  would be the same term and the theorem vacuous. `Task` is a compilation target only.
:::

# Definitions

%%%
state := "defs"
%%%

:::::hstack
```leanLibCode Paralever.Core.Semantics (package := paralever) (startLine := 138) (endLine := 149) -stretch
def step {α : Type} : ParM α → State → List (Conf α)
  | .pure _,      _ => []
  | .read l k,    σ => [.run (k (σ l)) σ]
  | .write l v k, σ => [.run (k ()) (σ.update l v)]
  | .par cs k,    σ =>
      if racingAll (nextAccsChilds cs) then [.wrong]
      else match allPure cs with
        | some vs => [.run (k vs) σ]
        | none    => (stepChilds cs σ).map fun r =>
            match r with
            | some x => .run (.par x.1 k) x.2
            | none   => .wrong
```

::::vstack
```leanLibCode Paralever.Core.ParM (package := paralever) (startLine := 71) (endLine := 73)
inductive Childs (Node : Type → Type 1) : List Type → Type 1 where
  | nil  : Childs Node []
  | cons {α : Type} {αs : List Type} : Node α → Childs Node αs → Childs Node (α :: αs)
```

```html
<div class="nd mono plain wide">parPair p q  =  .par Π[ p q ] (fun r => .pure (r.1, r.2.1))
seqPair p q  =  bind p (fun a => bind q (fun b => .pure (a, b)))

parAll ps    =  .par (childsOf ps) (fun x => .pure (resultsToList ps x))
seqAll []       =  .pure []
seqAll (p :: ps) =  bind (seqPair p (seqAll ps)) (fun r => .pure (r.1 :: r.2))<em>parPair is parAll at two children, not the other way round</em></div>
```
::::
:::::

:::class "steps"
* `step` returns a *list*: empty is terminal, a singleton is deterministic, and a fork returns one
  entry per ready child. That list is where every schedule comes from.
* `racingAll` is checked before the children move, so a fork with two conflicting next actions goes
  to `wrong` and stays there.
:::

# Language Framework, and the verdict the checker prints

%%%
state := "lang"
%%%

:::::hstack
```html
<div class="nd mono prl">buf A[2, 3] = 1, 2, 3, 4, 5, 6
buf out[3]

%k := 10

parallel {
  %s := 0
  for j in 3 {
    %v := A[0, j]
    if %v &gt; 2 { %s := %s + %v * %k }
    else       { %s := %s + %v }
  }
  %k := 99
  out[0] := %s
} | {
  parallel {
    %a := A[1, 0]
    out[1] := %a
  } | {
    %b := A[1, 2]
    out[2] := %b * %k
  }
}

print out, %k</div>
```

::::vstack
```html
<div class="nd mono blue">reads    {A[0,0] … A[1,2]}
writes   {out[0], out[1], out[2]}
threads  2
rounds   4 parallel, 8 sequential
verdict  every heap  Proved: Yes

out = [33, 4, 60]   10<em>← <b>10</b>, not 99</em></div>
```

:::class "steps"
* Buffers are shared and registers are not: `out[i] := %s` is what `Indep` measures, `%s` and `%k`
  are invisible to it.
* Registers are firstprivate, at every depth. All four threads read `%k = 10` — which is why
  `out[2]` is 60. Thread 0 sets `%k := 99` and the join discards it.
* `if … else` branches per cell; `print` is erased from both interpreters, and is a barrier the
  parallelizer may not cross.
:::
::::
:::::

# The theorem

```leanLibCode Paralever.Theory.Sequentialize (package := paralever) (startLine := 18) (endLine := 19) -stretch
def ParSeqEq {α : Type} (p q : ParM α) (σ : State) : Prop :=
  ∀ r σ', Reaches (.run p σ) (.run (.pure r) σ') ↔ Reaches (.run q σ) (.run (.pure r) σ')
```

```leanLibCode Lang.Core.Prog (package := paralever) (startLine := 674) (endLine := 675) -stretch
theorem par_seq_eq {s : ParProg} (h : wfB s = true) (ρ : Regs) (σ : State) :
    ParSeqEq (execPar s ρ) (execSeq s ρ) σ := by
```

```html
<div class="dgm tight">
  <div class="nd key"><code>wfB s = true</code><em>decided by <code>decide</code>: list intersections on footprints</em></div>
  <div class="arr">→</div>
  <div class="nd key blue">every schedule of <code>s</code> ends where <code>execSeq s</code> ends<em>stated as an <i>iff</i> on reachable outcomes</em></div>
</div>
```

Every program below discharges its obligation by {lean}`decide` or by a size-free kernel lemma. No program
carries a proof about interleavings of its own.

# Proof of Equivalence

%%%
state := "section"
%%%

:::class "steps"
* The two sides are never compared to each other.
* Each collapses to a point; the points are equal by computation.
* {lean}`ParSeqEq` reduces to {lean}`WellFormed`, once and for all programs.
:::

# The successor list

%%%
state := "proof"
%%%

```leanLibCode Paralever.Core.Semantics (package := paralever) (startLine := 138) (endLine := 149) -stretch
def step {α : Type} : ParM α → State → List (Conf α)
  | .pure _,      _ => []
  | .read l k,    σ => [.run (k (σ l)) σ]
  | .write l v k, σ => [.run (k ()) (σ.update l v)]
  | .par cs k,    σ =>
      if racingAll (nextAccsChilds cs) then [.wrong]
      else match allPure cs with
        | some vs => [.run (k vs) σ]
        | none    => (stepChilds cs σ).map fun r =>
            match r with
            | some x => .run (.par x.1 k) x.2
            | none   => .wrong
```

```html
<div class="dgm col">
  <div class="nd key">the list <b>is</b> the nondeterminism<em>empty = terminal · one entry = no choice · a fork = <b>one entry per ready child</b></em></div>
  <div class="nd mono">stepChilds (p :: ps) σ  =  (step p σ).map …   ++   (stepChilds ps σ).map …<em>the head child moves, <b>appended to</b> every move the tail can make — that <b>++</b> is the fan-out</em></div>
</div>
```

:::class "steps"
* There is no scheduler in the development. A *schedule* is a path through these lists, and
  `Reaches` is the transitive closure of membership in them.
* So quantifying over schedules is quantifying over `∈`.
:::

# Naive comparison of schedules

%%%
state := "proof"
%%%

```html
<div class="dgm">
  <div class="nd bad wide">compare schedules<em>two arms of <code>n</code> statements · (2n)!/(n!)² interleavings · <b>184 756</b> at n = 10 · and the two sides do not even take the same number of steps</em></div>
  <div class="arr">≠</div>
  <div class="nd good wide">compare each side to a <b>third object</b><em><code>runSeq p σ</code> — a <b>function</b>, not a relation: no schedule, no choice, no <code>wrong</code></em></div>
</div>
```

```html
<div class="dgm col">
  <div class="nd mono">runSeq (par cs k) σ  =  runSeq (k r₁) r₂   where (r₁, r₂) = runChilds cs σ
runChilds (p :: ps) σ  =  run p, then run ps from the heap p left<em>a fork’s canonical value <b>is</b> its children run left to right</em></div>
  <div class="nd key">runSeq (par p q) σ = runSeq (seq p q) σ — by <code>rfl</code>, and <b>free</b><em>the measuring stick reads the same on both. It says nothing yet about either one under a scheduler.</em></div>
</div>
```

# The invariant: any child, not the left one

%%%
state := "proof"
%%%

```leanLibCode Paralever.Theory.WellFormedCanonical (package := paralever) (startLine := 902) (endLine := 906) -stretch
theorem step_combined {τ : Type} (P : ParM τ) :
    ∀ σ, WellFormed P σ → ∀ P3 σ3, Conf.run P3 σ3 ∈ stepC (Conf.run P σ) →
      runSeq P3 σ3 = runSeq P σ ∧
      (∀ F, FDisjoint F (accesses P σ) → FDisjoint F (accesses P3 σ3)) :=
  step_combined_all.1 P
```

:::::hstack
```html
<div class="nd key"><code>P3</code> is <b>any</b> member of the successor list, under <code>∀</code> — one statement per scheduler choice<em>the proof <b>rcases</b> on <code>List.mem_append</code>: <b>head moved</b>, 10 lines · <b>tail moved</b>, 45 lines and the hard case</em></div>
```

```html
<div class="figwrap">
<svg viewBox="0 0 470 250" role="img" aria-label="two schedules out of one fork meeting at the same outcome">
  <g font-family="ui-monospace, monospace" font-size="12" text-anchor="middle" fill="#0f172a">
    <rect x="115" y="8" width="240" height="30" rx="6" fill="#eff6ff" stroke="#0073a3" stroke-width="2"/><text x="235" y="28">par [a:=x, y:=7] · x5 y0 a0</text>
    <rect x="8" y="98" width="205" height="30" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="110" y="118">[done, y:=7] · x5 y0 a5</text>
    <rect x="257" y="98" width="205" height="30" rx="6" fill="#fff7ed" stroke="#b45309" stroke-width="2"/><text x="359" y="118">[a:=x, done] · x5 y7 a0</text>
    <rect x="120" y="188" width="230" height="30" rx="6" fill="rgba(22,163,74,0.09)" stroke="#16a34a" stroke-width="2"/><text x="235" y="208">x5 y7 a5</text>
  </g>
  <g stroke="#64748b" stroke-width="1.5" fill="none">
    <path d="M 200 38 L 110 96"/><path d="M 270 38 L 359 96"/>
    <path d="M 110 128 L 200 186"/><path d="M 359 128 L 270 186"/>
  </g>
  <g font-family="var(--sans)" font-size="11.5" fill="#475569">
    <text x="55" y="68">head moved</text>
    <text x="345" y="68" fill="#b45309">tail moved first</text>
    <text x="235" y="240" text-anchor="middle" fill="#16a34a">the same runSeq at all four</text>
  </g>
</svg>
</div>
```
:::::

:::class "steps"
* *Why the tail case commutes.* Its step changed one cell in `W₂`. By C3 that cell is outside `R₁`,
  so the head reads the same values — `accesses_runSeq_locality`. By C1 it is outside `W₁`, so the
  head does not overwrite it — `runSeq_frame`.
* *Why it can be done again.* The second conjunct: a step only shrinks a footprint, so the sibling
  is still independent of the residue, and the invariant chains.
:::

# The bridge

%%%
state := "proof"
%%%

```leanLibCode Paralever.Theory.WellFormedCanonical (package := paralever) (startLine := 1464) (endLine := 1466) -stretch
theorem wellFormed_canonical {τ : Type} (p : ParM τ) :
    ∀ σ r σ', WellFormed p σ → (Reaches (.run p σ) (.run (.pure r) σ') ↔ (r, σ') = runSeq p σ) :=
  wellFormed_canonical_all.1 p
```

```html
<div class="dgm">
  <div class="nd wide">{ outcomes of <code>p</code> from σ }<em>every terminating schedule, however the scheduler moved</em></div>
  <div class="arr lbl2">=<small>under WellFormed</small></div>
  <div class="nd key">{ runSeq p σ }<em>one element</em></div>
</div>
```

:::class "steps"
* The invariant chained along a `Reaches` derivation, with `WellFormed_preserved` re-establishing the
  hypothesis at each link. `runSeq` is constant along the chain, and at the end it is `(r, σ′)`.
* *Uniqueness* is `→`; *existence* is `←`, from `no_race_of_indep`. Without existence a racy program
  reaches nothing and would satisfy the theorem vacuously on both sides.
:::

# Four steps to ParSeqEq

%%%
state := "proof"
%%%

```html
<div class="dgm col">
  <div class="nd mono">1.  WellFormed (par p q) σ   →   WellFormed (seq p q) σ<em>wellFormed_of_seqPair · seq has no fork, so the Indep conjunct is dropped</em></div>
  <div class="nd mono key">2.  ⟨par p q, σ⟩ →* ⟨pure r, σ′⟩   ⇔   (r, σ′) = runSeq (par p q) σ<em><b>the bridge, on the left — every left-hand schedule is eliminated here</b></em></div>
  <div class="nd mono key">3.  ⟨seq p q, σ⟩ →* ⟨pure r, σ′⟩   ⇔   (r, σ′) = runSeq (seq p q) σ<em><b>the bridge, on the right</b> — available only because of 1</em></div>
  <div class="nd mono">4.  runSeq (par p q) σ  =  runSeq (seq p q) σ<em>rfl — free, and carrying none of the content</em></div>
  <div class="nd good">chain 2, 4, 3 — that is ParSeqEq</div>
</div>
```

:::class "steps"
* The theorem is *not* two left-to-right runs compared. That is step 4, and it is `rfl`. The work is
  in *2 and 3*: each is `wellFormed_canonical`, a whole set of schedules collapsing to a point.
* Nothing after step 1 mentioned `p` or `q`. *So `ParSeqEq` reduces to `WellFormed`* — proved once,
  for every program there will ever be.
:::

# Parallel Programs are Faster

%%%
state := "section"
%%%

```leanLibCode Lang.Core.Cost (package := paralever) (startLine := 103) (endLine := 104) -stretch
theorem time_le {s : ParProg} (h : wfB s = true) (ρ : Regs) (σ : State) :
    time (execPar s ρ) σ ≤ time (execSeq s ρ) σ := time_execPar_le_all.1 s ρ σ h
```

:::class "steps"
* `time` counts rounds: one round is every running thread taking one step. The same `Bool` that
  proves the two readings agree also orders their spans.
* Parallelism reorders memory operations and removes none, so `work` is unchanged and only `time`
  falls. The inequality is not conditional on a machine, a scheduler or a core count.
:::

# Examples

%%%
state := "section"
%%%

:::class "steps"
* Matrix multiply — disjoint writes over overlapping reads.
* Merge sort — the fork is the recursion.
* A neural net — layers in sequence, threads inside each.
* Summing an array — quantified over the chunk plan.
:::

# Matrix multiply

%%%
state := "matmul"
%%%

```html
<div class="two-col wide-left">
```

```html
<div class="nd mono plain wide prl">const n = 2

buf A[2, 2] = 1, 2, 3, 4
buf B[2, 2] = 5, 6, 7, 8
buf C[2, 2]

parfor i in n {
  for j in n {
    %acc := 0
    for k in n {
      %x := A[i, k]
      %y := B[k, j]
      %acc := %acc + %x * %y
    }
    C[i, j] := %acc
  }
} :: "matmul 2x2"</div>
```

```leanLibCode Examples.Programs.MatMul (package := paralever) (startLine := 216) (endLine := 222) -stretch
example : ParProg.wfB (matmul 2) = true := by decide
example : ParProg.wfB (matmul 3) = true := by decide

/-- …and the equivalence follows with nothing further to supply. -/
theorem par_seq_eq_2 (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar (matmul 2) ρ) (ParProg.execSeq (matmul 2) ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ
```

```html
</div>
```

Thread `i` writes row `i` of `C` and reads row `i` of `A` and all of `B`. (C1) holds because
`i ↦ i*n + j` is injective across threads; (C2) and (C3) hold because `A` and `B` are never written.
The file above carries the same theorem as `matmul_parseqeq`, read through `prl_file`.

# Merge sort

```html
<div class="figwrap">
<svg viewBox="0 0 820 220" role="img" aria-label="merge sort recursion tree splitting a range into disjoint halves">
  <g font-family="ui-monospace, monospace" font-size="13.5" text-anchor="middle" fill="#0f172a">
    <rect x="320" y="14" width="180" height="32" rx="6" fill="#eef2ff" stroke="#4f46e5" stroke-width="2.2"/><text x="410" y="35">sort [0, 8)</text>
    <rect x="150" y="90" width="160" height="32" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="230" y="111">sort [0, 4)</text>
    <rect x="510" y="90" width="160" height="32" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="590" y="111">sort [4, 8)</text>
    <rect x="60"  y="166" width="130" height="30" rx="5" fill="#f8fafc" stroke="#cbd5e1"/><text x="125" y="186">[0, 2)</text>
    <rect x="212" y="166" width="130" height="30" rx="5" fill="#f8fafc" stroke="#cbd5e1"/><text x="277" y="186">[2, 4)</text>
    <rect x="440" y="166" width="130" height="30" rx="5" fill="#f8fafc" stroke="#cbd5e1"/><text x="505" y="186">[4, 6)</text>
    <rect x="592" y="166" width="130" height="30" rx="5" fill="#f8fafc" stroke="#cbd5e1"/><text x="657" y="186">[6, 8)</text>
  </g>
  <g stroke="#64748b" stroke-width="1.5" fill="none">
    <path d="M 410 46 L 410 68 L 230 68 L 230 88"/>
    <path d="M 410 46 L 410 68 L 590 68 L 590 88"/>
    <path d="M 230 122 L 230 144 L 125 144 L 125 164"/>
    <path d="M 230 122 L 230 144 L 277 144 L 277 164"/>
    <path d="M 590 122 L 590 144 L 505 144 L 505 164"/>
    <path d="M 590 122 L 590 144 L 657 144 L 657 164"/>
  </g>
  <g font-size="13" font-style="italic" font-family="var(--sans)" fill="#475569" text-anchor="middle">
    <text x="410" y="214">at each level: <tspan font-family="ui-monospace, monospace">lo ≤ mid ≤ hi</tspan>, so <tspan font-family="ui-monospace, monospace">[lo, mid)</tspan> and <tspan font-family="ui-monospace, monospace">[mid, hi)</tspan> do not meet</text>
  </g>
</svg>
</div>
```

```leanLibCode Examples.Programs.MergeSort (package := paralever) (startLine := 474) (endLine := 475) -stretch
theorem seq_eq_par (N lo hi : Nat) (hhiN : hi ≤ N) (σ : State) :
    mergeSortPar N lo hi ∥≡ mergeSortSeq N lo hi from σ := by
```

Quantified over the array size and over every range, with no `decide`: each level's obligation is
one interval fact, and the recursion carries it down.

# Neural net

```html
<div class="figwrap">
<svg viewBox="0 0 880 180" role="img" aria-label="three layers in sequence, each forking over its own output cells">
  <defs>
    <marker id="nnar" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
      <path d="M 0 0 L 10 5 L 0 10 z" fill="#64748b"/>
    </marker>
  </defs>
  <g font-family="ui-monospace, monospace" font-size="13" text-anchor="middle" fill="#0f172a">
    <rect x="20"  y="66" width="90"  height="34" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="65"  y="88">x[8]</text>
    <rect x="170" y="26" width="140" height="30" rx="6" fill="#eef2ff" stroke="#4f46e5"/><text x="240" y="46">conv1d × 6</text>
    <rect x="370" y="26" width="140" height="30" rx="6" fill="#eef2ff" stroke="#4f46e5"/><text x="440" y="46">relu × 6</text>
    <rect x="570" y="26" width="140" height="30" rx="6" fill="#eef2ff" stroke="#4f46e5"/><text x="640" y="46">dense × 2</text>
    <rect x="770" y="66" width="90"  height="34" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="815" y="88">y[2]</text>
    <rect x="170" y="106" width="140" height="30" rx="6" fill="#f8fafc" stroke="#cbd5e1"/><text x="240" y="126">c[6]</text>
    <rect x="370" y="106" width="140" height="30" rx="6" fill="#f8fafc" stroke="#cbd5e1"/><text x="440" y="126">r[6]</text>
    <rect x="570" y="106" width="140" height="30" rx="6" fill="#f8fafc" stroke="#cbd5e1"/><text x="640" y="126">w2[2,6], b2[2]</text>
  </g>
  <g stroke="#64748b" stroke-width="1.5" fill="none" marker-end="url(#nnar)">
    <path d="M 110 83 L 140 83 L 140 41 L 167 41"/>
    <path d="M 310 41 L 367 41"/>
    <path d="M 510 41 L 567 41"/>
    <path d="M 710 41 L 740 41 L 740 83 L 767 83"/>
  </g>
  <g font-size="12.5" font-style="italic" font-family="var(--sans)" fill="#475569" text-anchor="middle">
    <text x="440" y="166">every thread of a layer reads the whole weight array; only the output cells are written</text>
  </g>
</svg>
</div>
```

```leanLibCode Examples.Language.NeuralNet (package := paralever) (decl := Paralever.Examples.NeuralNet.forward_par_seq_eq) -stretch
/-- **The theorem.** Under every schedule, the net with all its layers' threads running at once
reaches exactly the outcomes it reaches run thread-by-thread. -/
theorem forward_par_seq_eq (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar forward ρ) (ParProg.execSeq forward ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ
```

The weights are shared reads, so (C2) and (C3) are free inside a layer. Between layers the
composition is sequential, and `wfB` recurses into each arm.

# Sum of an array

```html
<div class="figwrap">
<svg viewBox="0 0 860 170" role="img" aria-label="an array split into chunks, each chunk summed by one thread, the partial sums combined">
  <g font-family="ui-monospace, monospace" font-size="13" text-anchor="middle" fill="#0f172a">
    <rect x="40"  y="20" width="180" height="32" rx="5" fill="#eff6ff" stroke="#2563eb"/><text x="130" y="41">A[0, 4)</text>
    <rect x="240" y="20" width="180" height="32" rx="5" fill="#eff6ff" stroke="#2563eb"/><text x="330" y="41">A[4, 9)</text>
    <rect x="440" y="20" width="180" height="32" rx="5" fill="#eff6ff" stroke="#2563eb"/><text x="530" y="41">A[9, 13)</text>
    <rect x="640" y="20" width="180" height="32" rx="5" fill="#eff6ff" stroke="#2563eb"/><text x="730" y="41">A[13, 16)</text>

    <rect x="70"  y="90" width="120" height="30" rx="5" fill="#eef2ff" stroke="#4f46e5"/><text x="130" y="110">s₀</text>
    <rect x="270" y="90" width="120" height="30" rx="5" fill="#eef2ff" stroke="#4f46e5"/><text x="330" y="110">s₁</text>
    <rect x="470" y="90" width="120" height="30" rx="5" fill="#eef2ff" stroke="#4f46e5"/><text x="530" y="110">s₂</text>
    <rect x="670" y="90" width="120" height="30" rx="5" fill="#eef2ff" stroke="#4f46e5"/><text x="730" y="110">s₃</text>
  </g>
  <g stroke="#64748b" stroke-width="1.4" fill="none">
    <path d="M 130 52 L 130 88"/><path d="M 330 52 L 330 88"/>
    <path d="M 530 52 L 530 88"/><path d="M 730 52 L 730 88"/>
  </g>
  <g font-size="13" font-style="italic" font-family="var(--sans)" fill="#475569" text-anchor="middle">
    <text x="430" y="152">no thread writes the array, so C1–C3 hold vacuously — for <i>any</i> split</text>
  </g>
</svg>
</div>
```

```leanLibCode Examples.Programs.SumArray (package := paralever) (startLine := 106) (endLine := 108) -stretch
theorem seq_eq_par (chunks : ChunkPlan) (σ : State) :
    sumRangePar chunks ∥≡ sumRangeSeq chunks from σ :=
  parAll_par_seq_eq (chunks.map sumRange) σ (wellFormed_sumRangePar chunks σ)
```

Universally quantified over the chunk plan and the heap. This is the shape `∗`-disjointness cannot
state at all: four threads reading one array.

# Autoparallelization

%%%
state := "section"
%%%

:::class "steps"
* A sequential program is a right-leaning spine of `seq` nodes.
* Where the parallelism is: five units, four dependences.
* The spine rebuilt as three forks, proved with no hypothesis.
:::

# The sequential spine

%%%
state := "spine"
%%%

```html
<div class="two-col">
```

```html
<div class="nd mono plain wide prl">buf a[5]

a[0] := 3
a[1] := 4
%0 := a[0]
a[2] := %0 * %0
%1 := a[1]
a[3] := %1 * %1
%2 := a[2]
%3 := a[3]
a[4] := %2 + %3<em>chain.prl — ten lines, nine of them statements</em></div>
```

```html
<div class="figwrap">
<svg viewBox="0 0 520 320" role="img" aria-label="the nine statements of chain.prl as a right-leaning spine of seq nodes, one statement hanging off each">
  <g stroke="#64748b" stroke-width="1.3" fill="none">
    <path d="M 310 29 L 310 34.5 L 150 34.5 L 150 40"/>
    <path d="M 310 29 L 310 35 L 310 35 L 310 41"/>
    <path d="M 310 63 L 310 68.5 L 150 68.5 L 150 74"/>
    <path d="M 310 63 L 310 69 L 310 69 L 310 75"/>
    <path d="M 310 97 L 310 102.5 L 150 102.5 L 150 108"/>
    <path d="M 310 97 L 310 103 L 310 103 L 310 109"/>
    <path d="M 310 131 L 310 136.5 L 150 136.5 L 150 142"/>
    <path d="M 310 131 L 310 137 L 310 137 L 310 143"/>
    <path d="M 310 165 L 310 170.5 L 150 170.5 L 150 176"/>
    <path d="M 310 165 L 310 171 L 310 171 L 310 177"/>
    <path d="M 310 199 L 310 204.5 L 150 204.5 L 150 210"/>
    <path d="M 310 199 L 310 205 L 310 205 L 310 211"/>
    <path d="M 310 233 L 310 238.5 L 150 238.5 L 150 244"/>
    <path d="M 310 233 L 310 239 L 310 239 L 310 245"/>
    <path d="M 310 267 L 310 272.5 L 150 272.5 L 150 278"/>
    <path d="M 310 267 L 310 273 L 310 273 L 310 279"/>
  </g>
  <g font-family="ui-monospace, monospace" text-anchor="middle" fill="#0f172a">
    <rect x="288" y="7" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="310" y="22" font-size="12" fill="#0f172a">seq</text>
    <rect x="288" y="41" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="310" y="56" font-size="12" fill="#0f172a">seq</text>
    <rect x="288" y="75" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="310" y="90" font-size="12" fill="#0f172a">seq</text>
    <rect x="288" y="109" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="310" y="124" font-size="12" fill="#0f172a">seq</text>
    <rect x="288" y="143" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="310" y="158" font-size="12" fill="#0f172a">seq</text>
    <rect x="288" y="177" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="310" y="192" font-size="12" fill="#0f172a">seq</text>
    <rect x="288" y="211" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="310" y="226" font-size="12" fill="#0f172a">seq</text>
    <rect x="288" y="245" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="310" y="260" font-size="12" fill="#0f172a">seq</text>
    <rect x="75" y="40" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="150" y="56" font-size="11.5">a[0] := 3</text>
    <rect x="75" y="74" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="150" y="90" font-size="11.5">a[1] := 4</text>
    <rect x="75" y="108" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="150" y="124" font-size="11.5">%0 := a[0]</text>
    <rect x="75" y="142" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="150" y="158" font-size="11.5">a[2] := %0 * %0</text>
    <rect x="75" y="176" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="150" y="192" font-size="11.5">%1 := a[1]</text>
    <rect x="75" y="210" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="150" y="226" font-size="11.5">a[3] := %1 * %1</text>
    <rect x="75" y="244" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="150" y="260" font-size="11.5">%2 := a[2]</text>
    <rect x="75" y="278" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="150" y="294" font-size="11.5">%3 := a[3]</text>
    <rect x="235" y="278" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="310" y="294" font-size="11.5">a[4] := %2 + %3</text>
  </g>
  <g font-size="12.5" font-family="var(--sans)" fill="#475569">
    <text x="345" y="92">the spine is the order</text>
    <text x="345" y="112">the text was written in;</text>
    <text x="345" y="132">depth 9, one statement</text>
    <text x="345" y="152">per round</text>
  </g>
</svg>
</div>
```

```html
</div>
```

`ParProg.block [s₀, …, s₈]` is `seq s₀ (seq s₁ (…))`, so the order the statements were written in is
the tree's right spine. The pass first cuts that spine into five register-closed units — `%0 := a[0]`
and `a[2] := %0 * %0` may not be separated, because a register is thread-private — and one scoreboard
pass reads every dependence off them: `[[], [], [0], [1], [2, 3]]`.

# The dependence DAG

```html
<div class="figwrap">
<svg viewBox="0 0 1180 376" role="img" aria-label="the ten lines bracketed into five register-closed units, and the four dependences between them laid out in three rounds">
  <rect x="548" y="50" width="500" height="72" rx="10" fill="#eef2ff" stroke="#4f46e5" stroke-width="1" stroke-dasharray="5 5"/><text x="1062" y="92" font-size="12.5" font-family="var(--sans)" fill="#4f46e5">1 round</text>
  <rect x="548" y="150" width="500" height="72" rx="10" fill="#eff6ff" stroke="#2563eb" stroke-width="1" stroke-dasharray="5 5"/><text x="1062" y="192" font-size="12.5" font-family="var(--sans)" fill="#2563eb">2 rounds</text>
  <rect x="548" y="250" width="500" height="72" rx="10" fill="#f0fdf4" stroke="#16a34a" stroke-width="1" stroke-dasharray="5 5"/><text x="1062" y="292" font-size="12.5" font-family="var(--sans)" fill="#16a34a">3 rounds</text>
  <g stroke="#94a3b8" stroke-width="1.6" fill="none" stroke-linejoin="round">
    <path d="M 680 109 L 680 135 L 680 135 L 680 161"/>
    <path d="M 900 109 L 900 135 L 900 135 L 900 161"/>
    <path d="M 680 209 L 680 235 L 790 235 L 790 261"/>
    <path d="M 900 209 L 900 235 L 790 235 L 790 261"/>
  </g>
  <g font-family="ui-monospace, monospace" font-size="13" fill="#0f172a">
    <text x="92" y="58">a[0] := 3</text>
    <text x="92" y="87">a[1] := 4</text>
    <text x="92" y="116">%0 := a[0]</text>
    <text x="92" y="145">a[2] := %0 * %0</text>
    <text x="92" y="174">%1 := a[1]</text>
    <text x="92" y="203">a[3] := %1 * %1</text>
    <text x="92" y="232">%2 := a[2]</text>
    <text x="92" y="261">%3 := a[3]</text>
    <text x="92" y="290">a[4] := %2 + %3</text>
  </g>
  <g font-family="ui-monospace, monospace">
    <rect x="64" y="43" width="7" height="22" rx="3.5" fill="#4f46e5"/><text x="52" y="58" font-size="12" fill="#4f46e5" text-anchor="end">u0</text>
    <rect x="64" y="72" width="7" height="22" rx="3.5" fill="#4f46e5"/><text x="52" y="87" font-size="12" fill="#4f46e5" text-anchor="end">u1</text>
    <rect x="64" y="101" width="7" height="51" rx="3.5" fill="#2563eb"/><text x="52" y="130.5" font-size="12" fill="#2563eb" text-anchor="end">u2</text>
    <rect x="64" y="159" width="7" height="51" rx="3.5" fill="#2563eb"/><text x="52" y="188.5" font-size="12" fill="#2563eb" text-anchor="end">u3</text>
    <rect x="64" y="217" width="7" height="80" rx="3.5" fill="#16a34a"/><text x="52" y="261" font-size="12" fill="#16a34a" text-anchor="end">u4</text>
  </g>
  <g font-family="ui-monospace, monospace" text-anchor="middle">
    <rect x="582" y="63" width="196" height="46" rx="7" fill="#ffffff" stroke="#4f46e5" stroke-width="2"/><text x="680" y="82" font-size="13" fill="#4f46e5">u0</text><text x="680" y="100" font-size="11" fill="#475569">w a[0]</text>
    <rect x="802" y="63" width="196" height="46" rx="7" fill="#ffffff" stroke="#4f46e5" stroke-width="2"/><text x="900" y="82" font-size="13" fill="#4f46e5">u1</text><text x="900" y="100" font-size="11" fill="#475569">w a[1]</text>
    <rect x="582" y="163" width="196" height="46" rx="7" fill="#ffffff" stroke="#2563eb" stroke-width="2"/><text x="680" y="182" font-size="13" fill="#2563eb">u2</text><text x="680" y="200" font-size="11" fill="#475569">r a[0] · w a[2]</text>
    <rect x="802" y="163" width="196" height="46" rx="7" fill="#ffffff" stroke="#2563eb" stroke-width="2"/><text x="900" y="182" font-size="13" fill="#2563eb">u3</text><text x="900" y="200" font-size="11" fill="#475569">r a[1] · w a[3]</text>
    <rect x="692" y="263" width="196" height="46" rx="7" fill="#ffffff" stroke="#16a34a" stroke-width="2"/><text x="790" y="282" font-size="13" fill="#16a34a">u4</text><text x="790" y="300" font-size="11" fill="#475569">r a[2],a[3] · w a[4]</text>
  </g>
  <g font-size="12.5" font-family="var(--sans)" fill="#475569">
    <text x="40" y="26">the ten lines, cut into units</text>
    <text x="548" y="26">what each unit touches, and what it must wait for</text>
    <text x="40" y="350">a unit is a run of statements no live register crosses</text>
    <text x="548" y="350">depth 6 against a sequential 9, and 6 is the lower bound</text>
  </g>
</svg>
</div>
```

A register is thread-private, so `%0 := a[0]` and `a[2] := %0 * %0` may not be separated: the unit,
not the statement, is what a thread is built from. One left-to-right scoreboard pass then reads
every dependence off the units' footprints — `[[], [], [0], [1], [2, 3]]`. Four of the ten pairs
carry one; `u0, u1` share no cell, as do `u2, u3`. That is the whole of the parallelism this program has.

# The parallel plan

```html
<div class="two-col">
```

```html
<div class="figwrap">
<svg viewBox="0 0 520 320" role="img" aria-label="the nine statements of chain.prl as a right-leaning spine of seq nodes, one statement hanging off each">
  <g stroke="#64748b" stroke-width="1.3" fill="none">
    <path d="M 310 29 L 310 34.5 L 150 34.5 L 150 40"/>
    <path d="M 310 29 L 310 35 L 310 35 L 310 41"/>
    <path d="M 310 63 L 310 68.5 L 150 68.5 L 150 74"/>
    <path d="M 310 63 L 310 69 L 310 69 L 310 75"/>
    <path d="M 310 97 L 310 102.5 L 150 102.5 L 150 108"/>
    <path d="M 310 97 L 310 103 L 310 103 L 310 109"/>
    <path d="M 310 131 L 310 136.5 L 150 136.5 L 150 142"/>
    <path d="M 310 131 L 310 137 L 310 137 L 310 143"/>
    <path d="M 310 165 L 310 170.5 L 150 170.5 L 150 176"/>
    <path d="M 310 165 L 310 171 L 310 171 L 310 177"/>
    <path d="M 310 199 L 310 204.5 L 150 204.5 L 150 210"/>
    <path d="M 310 199 L 310 205 L 310 205 L 310 211"/>
    <path d="M 310 233 L 310 238.5 L 150 238.5 L 150 244"/>
    <path d="M 310 233 L 310 239 L 310 239 L 310 245"/>
    <path d="M 310 267 L 310 272.5 L 150 272.5 L 150 278"/>
    <path d="M 310 267 L 310 273 L 310 273 L 310 279"/>
  </g>
  <g font-family="ui-monospace, monospace" text-anchor="middle" fill="#0f172a">
    <rect x="288" y="7" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="310" y="22" font-size="12" fill="#0f172a">seq</text>
    <rect x="288" y="41" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="310" y="56" font-size="12" fill="#0f172a">seq</text>
    <rect x="288" y="75" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="310" y="90" font-size="12" fill="#0f172a">seq</text>
    <rect x="288" y="109" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="310" y="124" font-size="12" fill="#0f172a">seq</text>
    <rect x="288" y="143" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="310" y="158" font-size="12" fill="#0f172a">seq</text>
    <rect x="288" y="177" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="310" y="192" font-size="12" fill="#0f172a">seq</text>
    <rect x="288" y="211" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="310" y="226" font-size="12" fill="#0f172a">seq</text>
    <rect x="288" y="245" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="310" y="260" font-size="12" fill="#0f172a">seq</text>
    <rect x="75" y="40" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="150" y="56" font-size="11.5">a[0] := 3</text>
    <rect x="75" y="74" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="150" y="90" font-size="11.5">a[1] := 4</text>
    <rect x="75" y="108" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="150" y="124" font-size="11.5">%0 := a[0]</text>
    <rect x="75" y="142" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="150" y="158" font-size="11.5">a[2] := %0 * %0</text>
    <rect x="75" y="176" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="150" y="192" font-size="11.5">%1 := a[1]</text>
    <rect x="75" y="210" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="150" y="226" font-size="11.5">a[3] := %1 * %1</text>
    <rect x="75" y="244" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="150" y="260" font-size="11.5">%2 := a[2]</text>
    <rect x="75" y="278" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="150" y="294" font-size="11.5">%3 := a[3]</text>
    <rect x="235" y="278" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="310" y="294" font-size="11.5">a[4] := %2 + %3</text>
  </g>
  <g font-size="12.5" font-family="var(--sans)" fill="#475569">
    <text x="345" y="92">the spine is the order</text>
    <text x="345" y="112">the text was written in;</text>
    <text x="345" y="132">depth 9, one statement</text>
    <text x="345" y="152">per round</text>
  </g>
</svg>
</div>
```

```html
<div class="figwrap">
<svg viewBox="0 0 570 292" role="img" aria-label="the same program after the rewrite: three forks in sequence, two threads then two threads then one">
  <g stroke="#64748b" stroke-width="1.3" fill="none">
    <path d="M 258 31 L 258 49 L 117.5 49 L 117.5 67"/>
    <path d="M 258 31 L 258 49 L 398.5 49 L 398.5 67"/>
    <path d="M 117.5 89 L 117.5 106.5 L 60 106.5 L 60 124"/>
    <path d="M 117.5 89 L 117.5 106.5 L 175 106.5 L 175 124"/>
    <path d="M 398.5 89 L 398.5 107 L 302 107 L 302 125"/>
    <path d="M 398.5 89 L 398.5 107 L 495 107 L 495 125"/>
    <path d="M 302 147 L 302 171.5 L 240 171.5 L 240 196"/>
    <path d="M 302 147 L 302 171.5 L 365 171.5 L 365 196"/>
    <path d="M 495 147 L 495 171.5 L 495 171.5 L 495 196"/>
  </g>
  <g font-family="ui-monospace, monospace" text-anchor="middle" fill="#0f172a">
    <rect x="236" y="9" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="258" y="24" font-size="12" fill="#0f172a">seq</text>
    <rect x="95.5" y="67" width="44" height="22" rx="5" fill="#eef2ff" stroke="#4f46e5" stroke-width="2.2"/><text x="117.5" y="82" font-size="12" fill="#312e81">par</text>
    <rect x="376.5" y="67" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="398.5" y="82" font-size="12" fill="#0f172a">seq</text>
    <rect x="10" y="124" width="100" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="60" y="140" font-size="11.5">a[0] := 3</text>
    <rect x="125" y="124" width="100" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="175" y="140" font-size="11.5">a[1] := 4</text>
    <rect x="280" y="125" width="44" height="22" rx="5" fill="#eef2ff" stroke="#4f46e5" stroke-width="2.2"/><text x="302" y="140" font-size="12" fill="#312e81">par</text>
    <rect x="473" y="125" width="44" height="22" rx="5" fill="#eef2ff" stroke="#4f46e5" stroke-width="2.2"/><text x="495" y="140" font-size="12" fill="#312e81">par</text>
    <rect x="181" y="196" width="118" height="48" rx="5" fill="#eff6ff" stroke="#2563eb" stroke-width="1.2"/><text x="240" y="214" font-size="11">%0 := a[0]</text><text x="240" y="231" font-size="11">a[2] := %0 * %0</text>
    <rect x="306" y="196" width="118" height="48" rx="5" fill="#eff6ff" stroke="#2563eb" stroke-width="1.2"/><text x="365" y="214" font-size="11">%1 := a[1]</text><text x="365" y="231" font-size="11">a[3] := %1 * %1</text>
    <rect x="436" y="196" width="118" height="65" rx="5" fill="#eff6ff" stroke="#2563eb" stroke-width="1.2"/><text x="495" y="214" font-size="11">%2 := a[2]</text><text x="495" y="231" font-size="11">%3 := a[3]</text><text x="495" y="248" font-size="11">a[4] := %2 + %3</text>
  </g>
  <g font-size="12.5" font-family="var(--sans)" fill="#475569">
    <text x="20" y="206">depth 6:</text>
    <text x="20" y="224">1 + 2 + 3</text>
    <text x="20" y="242">rounds, and</text>
    <text x="20" y="260">6 is the bound</text>
  </g>
</svg>
</div>
```

```html
</div>
```

```leanLibCode Examples.AutoPar.Pass (package := paralever) (startLine := 128) (endLine := 135) -stretch
example (ρ : Regs) (σ : State) :
    (runSeq (ParProg.execPar (rewrite p) ρ) σ).2 = (runSeq (ParProg.execSeq p ρ) σ).2 :=
  rewrite_sound p ρ σ

-- and because the rewrite stays well-formed, `par_seq_eq` lifts that from one schedule to all
example (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar (rewrite p) ρ) (ParProg.execSeq (rewrite p) ρ) σ :=
  rewrite_parSeqEq p (by decide) ρ σ
```

`rewrite` checks its own gate and hands back the program unchanged when it fails, which is why
`rewrite_sound` carries no hypothesis. Nothing is ever reordered, so no commutation lemma is needed.

# Races and MLIR

%%%
state := "section"
%%%

:::class "steps"
* What the checker returns when it refuses: the schedule that disagrees.
* A whole MLIR module in, a whole paralever program out.
:::

# A race, and what the checker returns

%%%
state := "race"
%%%

```html
<div class="dgm top">
  <div class="nd mono prl">buf x[1]
buf log[2]

parallel {
  log[0] := 1
  x[0] := 7
} | {
  log[1] := 1
  x[0] := 9
}<em>Examples/Language/race.prl</em></div>
  <div class="figwrap" style="flex:1">
  <svg viewBox="0 0 440 230" role="img" aria-label="the program tree: one par with two arms, whose last writes both target cell x of 0">
    <g font-family="var(--mono)" font-size="12.5" text-anchor="middle" fill="#0f172a">
      <rect x="160" y="8" width="120" height="28" rx="6" fill="#eff6ff" stroke="#0073a3" stroke-width="2"/><text x="220" y="27">par</text>
      <rect x="30"  y="88" width="150" height="26" rx="5" fill="#f8fafc" stroke="#94a3b8"/><text x="105" y="106">log[0] := 1</text>
      <rect x="260" y="88" width="150" height="26" rx="5" fill="#f8fafc" stroke="#94a3b8"/><text x="335" y="106">log[1] := 1</text>
      <rect x="30"  y="146" width="150" height="26" rx="5" fill="rgba(220,38,38,0.09)" stroke="#dc2626" stroke-width="2"/><text x="105" y="164">x[0] := 7</text>
      <rect x="260" y="146" width="150" height="26" rx="5" fill="rgba(220,38,38,0.09)" stroke="#dc2626" stroke-width="2"/><text x="335" y="164">x[0] := 9</text>
    </g>
    <g stroke="#94a3b8" stroke-width="1.6" fill="none">
      <path d="M 190 36 L 105 88"/><path d="M 250 36 L 335 88"/>
      <path d="M 105 114 L 105 146"/><path d="M 335 114 L 335 146"/>
    </g>
    <path d="M 180 159 L 260 159" stroke="#dc2626" stroke-width="2" stroke-dasharray="5 4" fill="none"/>
    <text x="220" y="200" font-size="12.5" font-family="var(--sans)" fill="#dc2626" text-anchor="middle">W₁ ∩ W₂ = {x[0]} — clause C1 fails</text>
    <text x="220" y="220" font-size="12.5" font-family="var(--sans)" fill="#16a34a" text-anchor="middle">log[0], log[1] disjoint — not the problem</text>
  </svg>
  </div>
</div>
```

```html
<div class="trace">
<table class="dgmt ruled-table">
<thead><tr><th>step</th><th>thread</th><th>action</th><th>heap after</th></tr></thead>
<tbody>
<tr><td>0</td><td>T0</td><td>write log[0] ← 1</td><td>log ↦ [1, 0], x ↦ [0]</td></tr>
<tr><td>1</td><td>T1</td><td>write log[1] ← 1</td><td>log ↦ [1, 1], x ↦ [0]</td></tr>
<tr class="racing"><td>2</td><td>T1</td><td>write x[0] ← 9</td><td>pending</td></tr>
<tr class="racing"><td>2</td><td>T0</td><td>write x[0] ← 7</td><td>pending</td></tr>
</tbody>
</table>
<div class="verdict">
  <div class="refusal">aborts at step 2 — <b>T0, T1 write to {x[0]}</b></div>
  <div class="readings"><span class="reading">parallel <b>x[0] ↦ 7</b></span><span class="reading">sequential <b>x[0] ↦ 9</b></span></div>
  <em>paralever race Examples/Language/race.prl</em>
</div>
</div>
```

# How the schedule is found

%%%
state := "sched"
%%%

:::::hstack
```html
<div class="map"><pre>findWrongFrom fuel p σ:                      -- phase 1
  sites ← raceSites p σ                      every par node failing Bernstein,
  if sites = [] then none                     measured along the canonical run
  else findWrongGuided (targetsOf sites) fuel (run p σ)

findWrongGuided targets fuel c:               -- phase 2
  if 0 then none
  if some successor of c is wrong then [its index]
  else let (keep, hold) = partition (successors of c)
         by "does this step move a thread PAST a flagged cell?"
       first i in keep ++ hold with
         findWrongGuided targets (fuel-1) c′ = some s  ⇒  i :: s</pre></div>
```

```html
<div class="dgm">
  <div class="figwrap">
  <svg viewBox="0 0 620 160" role="img" aria-label="the search tree, with target-consuming branches tried last">
    <g font-family="var(--sans)" font-size="12" text-anchor="middle" fill="#475569">
      <circle cx="310" cy="20" r="9" fill="#eff6ff" stroke="#0073a3" stroke-width="2"/>
      <circle cx="170" cy="75" r="8" fill="#f0fdf4" stroke="#16a34a" stroke-width="2"/>
      <circle cx="310" cy="75" r="8" fill="#f0fdf4" stroke="#16a34a" stroke-width="2"/>
      <circle cx="470" cy="75" r="8" fill="#f8fafc" stroke="#cbd5e1"/>
      <circle cx="170" cy="132" r="9" fill="rgba(220,38,38,0.12)" stroke="#dc2626" stroke-width="2"/>
      <circle cx="300" cy="132" r="8" fill="#f8fafc" stroke="#cbd5e1"/>
      <circle cx="470" cy="132" r="8" fill="#f8fafc" stroke="#cbd5e1"/>
    </g>
    <g stroke="#94a3b8" stroke-width="1.5" fill="none">
      <path d="M 300 29 L 175 66"/><path d="M 310 29 L 310 66"/><path d="M 322 29 L 462 66"/>
      <path d="M 170 83 L 170 123"/><path d="M 310 83 L 301 123"/><path d="M 470 83 L 470 123"/>
    </g>
    <g font-family="var(--sans)" font-size="12" fill="#475569">
      <text x="110" y="52" fill="#16a34a">tried first: keeps its position</text>
      <text x="486" y="52" fill="#94a3b8">tried last: consumes a target</text>
      <text x="112" y="156" fill="#dc2626">wrong</text>
    </g>
  </svg>
  </div>
</div>
```
:::::

:::class "steps"
* Phase 1 names the cells; phase 2 is depth-first over `step`'s successor list, trying last any
  step that moves a thread *past* one of them — a reordering, so nothing becomes unfindable.
* Whatever comes back is re-run by `follow` and turned into a `Reaches` proof by `follow_sound`,
  so the counterexample is checked rather than trusted.
:::

# MLIR in, paralever out

%%%
state := "mlir"
%%%

```html
<div class="two-col">
```

```html
<div class="nd mono plain wide mlir">memref.global "private" @A : memref&lt;3xi64&gt; = dense&lt;[2, 3, 4]&gt;
func.func @main() {
  %A = memref.get_global @A : memref&lt;3xi64&gt;
  affine.parallel (%i) = (0) to (3) {
    %0 = affine.load %A[%i] : memref&lt;3xi64&gt;
    %1 = arith.muli %0, %0 : i64
    affine.store %1, %A[%i] : memref&lt;3xi64&gt;
  }
  return
}<em>square-no.mlir — the whole module</em></div>
```

```html
<div class="nd mono plain wide blue prl">buf A[3] = 2, 3, 4

parallel {
  %0 := A[0]
  A[0] := (%0 * %0)
} | {
  %0 := A[1]
  A[1] := (%0 * %0)
} | {
  %0 := A[2]
  A[2] := (%0 * %0)
}<em>paralever to-prl — the whole program</em></div>
```

```html
</div>
```

```leanLibCode Examples.Mlir.Files (package := paralever) (decl := Paralever.Examples.Mlir.square_par_seq_eq) -stretch
-- and the theorem the verdict stands for, on the program the deck prints
theorem square_par_seq_eq (ρ : Regs) (σ : State) :
    ParSeqEq (Lang.ParProg.execPar square.prog ρ) (Lang.ParProg.execSeq square.prog ρ) σ :=
  Lang.ParProg.par_seq_eq (by decide) ρ σ
```

A `memref.global` becomes a buffer, an `affine.map` is already a footprint function, and the three
iterations become three threads of one fork. Nine labelled pilots are `#guard`ed as a confusion
matrix — `tp = 3, fp = 0, fn = 0, tn = 4` over the seven generic-form ones — and emitting the
program back as MLIR compares memory, footprint, verdict and heap.

# Performance of Paralever

%%%
state := "section"
%%%

:::class "steps"
* How long the check takes on matrix multiply, and the speedup it certifies.
* A program with no structure: the pass runs, and finds almost nothing.
* A counterexample at the very bottom of a run, and what reaching it costs.
:::

# Matrix multiply: the check, and the speedup it certifies

```html
<table class="dgmt ruled-table">
<thead><tr><th><code>n</code></th><th>cells</th><th>threads</th><th>rounds par</th><th>rounds seq</th><th>speedup</th><th>check</th></tr></thead>
<tbody>
<tr><td>2</td><td>12</td><td>2</td><td>10</td><td>20</td><td><b>2×</b></td><td>0 ms</td></tr>
<tr><td>4</td><td>48</td><td>4</td><td>36</td><td>144</td><td><b>4×</b></td><td>0 ms</td></tr>
<tr><td>8</td><td>192</td><td>8</td><td>136</td><td>1 088</td><td><b>8×</b></td><td>20 ms</td></tr>
<tr><td>12</td><td>432</td><td>12</td><td>300</td><td>3 600</td><td><b>12×</b></td><td>120 ms</td></tr>
<tr><td>16</td><td>768</td><td>16</td><td>528</td><td>8 448</td><td><b>16×</b></td><td>520 ms</td></tr>
<tr><td>20</td><td>1 200</td><td>20</td><td>820</td><td>16 400</td><td><b>20×</b></td><td>1 600 ms</td></tr>
</tbody>
</table>
```

:::class "steps"
* The verdict is *every heap · Proved: Yes* at every size: `wfB` accepts, so the threads'
  footprints are pairwise independent whatever the heap holds.
* The speedup is exactly `n`, the thread count, and it is certified rather than measured —
  these are the two `time` values the cost theorem orders, not a wall clock.
* The check grows with the iteration space it writes out, not with the speedup: `n = 20` is 1 200
  cells and 1.6 s.
:::

# A program with no structure

:::class "steps"
* `equiv.prl` — 36 lines, 224 sequential rounds, a serial chain of dependences rather than a
  loop nest.
* `autopar` takes *1.63 s* and returns 2 threads at *196* parallel rounds: a speedup of
  *1.14×*, against 4× on `phases.prl`, which is the same length and *does* split.
* The pass is sound either way. Where the dependences forbid a split it finds nothing, and says so,
  rather than reporting a parallelism that is not there.
:::

```html
<div class="dgm">
  <div class="nd mono">phases.prl<em>16 seq rounds → 4 threads, 4 par · <b>4×</b></em></div>
  <div class="nd mono bad">equiv.prl<em>224 seq rounds → 2 threads, 196 par · <b>1.14×</b></em></div>
  <div class="nd mono bad">tally.prl, strength.prl<em>loop-carried → no split at all · <b>1×</b></em></div>
</div>
```

# A counterexample at the bottom

:::class "steps"
* Two arms each do `k` independent writes, then both write one shared cell: the only race is the
  very last statement either arm runs, at step `2k`.
* The search reaches it in every case — it replays the schedule against the semantics rather
  than guessing, so the depth is the cost.
:::

```html
<table class="dgmt ruled-table">
<thead><tr><th><code>k</code></th><th>race at step</th><th>found</th><th>search</th></tr></thead>
<tbody>
<tr><td>2</td><td>4</td><td>yes</td><td>0 ms</td></tr>
<tr><td>8</td><td>16</td><td>yes</td><td>0 ms</td></tr>
<tr><td>32</td><td>64</td><td>yes</td><td>0 ms</td></tr>
<tr><td>128</td><td>256</td><td>yes</td><td>80 ms</td></tr>
<tr><td>512</td><td>1 024</td><td>yes</td><td>3 420 ms</td></tr>
</tbody>
</table>
```

:::class "notation"
On `race.prl` the two readings are separated as well as refused: parallel leaves `x[0] ↦ 7`,
sequential leaves `x[0] ↦ 9`, and the refusal names the cells and the threads —
`T0, T1 write to: {x[0]}`.
:::

# Limitations

%%%
state := "section"
%%%

:::class "steps"
* *Non-terminating programs are unrepresentable.*
  * `ParM` is an inductive type, so every program it can express terminates.
* *Locks and atomics are out of scope.*
  * The semantics sends a race to `wrong` and leaves it there, which is what makes the atomic grain irrelevant; a lock would make it relevant again.
* *A computed address widens the footprint.*
  * `A[B[i]]` has a subscript the text does not determine, so the syntactic footprint might claim all of `A`.
* *A solver's `unsat` is not a proof.*
  * z3 and cvc5 are not the Lean kernel, and neither is a build dependency.
  * It is reported as *discharged by* the named solver. A `sat` is recomputed in Lean before it is
    believed.
:::

# Thank you

%%%
state := "thanks"
%%%

Any questions?

:::class "refs"
* Bernstein, *Analysis of Programs for Parallel Processing*, IEEE TEC 1966.
* Reynolds, *Toward a Grainless Semantics for Shared-Variable Concurrency*, FSTTCS 2004.
* Brookes, *A Semantics for Concurrent Separation Logic*, CONCUR 2004.
* de Moura and Ullrich, *The Lean 4 Theorem Prover and Programming Language*, CADE 28, 2021.
:::
