import VersoSlides
import Verso.Doc.Concrete
import Paralever
import Examples.MatMul
import Examples.ParMapDemo
import Examples.PureToParM

set_option verso.code.warnLineLength 500
set_option verso.slides.panel false
set_option linter.unusedVariables false
set_option verso.slides.warnOnImage false

open VersoSlides
open Paralever

/- A `timeDay` inline role: renders the wall-clock date at the moment this doc is built (elaborated),
e.g. "21 July 2026" — invoke as `{timeDay}`·``. It re-runs whenever this file is recompiled, so a
fresh `lake build` / `lake exe slides` refreshes it. -/
open Verso Doc Elab ArgParse in
open Lean Elab Widget in
open Lean.Doc.Syntax in
@[role]
meta def timeDay : RoleExpanderOf Unit
  | (), _ => do
    let out ← IO.Process.run { cmd := "date", args := #["+%d %B %Y"] }
    let html := Verso.Output.Html.text false out.trimAscii.toString
    ``(Verso.Doc.Inline.other (VersoSlides.InlineExt.ofHtml $(quote html)) #[])

#doc (Slides) "Paralever" =>

# paralever

%%%
state := "title"
%%%

:::class "subheader"
Proving output equivalence of _parallel_ programs with _sequential_ programs — in Lean 4
:::

:::class "byline"
*Anirudh Gupta*
:::

:::class "event"
IISc Bengaluru · ISP-I · 4th-year BTech
:::

:::class "links"
[github.com/AnirudhG07/paralever](https://github.com/AnirudhG07/paralever)
:::

:::class "timeDay"
{timeDay}`·`
:::

# Overview

* the problem: a parallel program and a sequential one, do they agree
* Hoare logic, and where it runs out on a shared heap
* what the literature proves: O'Hearn, Brookes, Vafeiadis, Apt & Olderog, DPJ, PolCert, Blom
* the statement nobody mechanized, and our theorem for it
* how we say "independent": Bernstein, `ParM`, `WellFormed`
* the proof, in four parts
* programs: sorting, images, matmul, a bank, a merge sort

# Do these two programs produce the same output?

```html
<div class="dgm">
  <div class="nd mono blue">sum = 0
for i in 0..n:
    sum += A[i]<em>sequential</em></div>
  <div class="arr lbl2">≟<small>same output?</small></div>
  <div class="nd mono blue">split A into k chunks
sum each chunk on its own thread
add the partial sums<em>parallel</em></div>
</div>
```

Everyone writes the second one and assumes it matches the first. We want that checked by a machine.

:::class "steps"
* `k` threads of `m` steps each give `(km)! / (m!)^k` interleavings
* we cannot test them, and we do not want one proof per program
:::


```html
<div class="dgm col tight">
  <div class="nd bad wide">one proof per parallel program<em>what you do today — and it scales with your codebase</em></div>
  <div class="arr">▼</div>
  <div class="nd key wide">one theorem, proved once &nbsp;+&nbsp; one small check per program<em>the check should be arithmetic, not a proof about schedules</em></div>
</div>
```

If the branches do not interfere, every interleaving gives the sequential answer. Non-interference is
proved once; after that the schedule does not enter the obligation.

# Hoare triples compose in sequence, and break on a heap

`{P} C {Q}` means: if `P` holds before `C` runs, and `C` terminates, `Q` holds after.

```html
<div class="dgm tight">
  <div class="nd mono">{x = 5}   x := x + 1   {x = 6}</div>
  <div class="nd mono thm">{P} C₁ {R}   {R} C₂ {Q}
──────────────────────────
      {P} C₁ ; C₂ {Q}<em>sequencing: verify the pieces, glue them</em></div>
</div>
```

The same gluing for `∥` would verify each branch alone, then combine.


```html
<div class="dgm col tight">
  <div class="nd mono bad">{x = 5}   [p] := 7   {x = 5}<em>only valid if p does not point at x</em></div>
  <div class="arr">▼</div>
  <div class="nd wide">every assignment through a pointer drags along a side condition for every other pointer<em>the frame problem</em></div>
</div>
```

For parallelism it is worse. `{P} C₁ {R}` and `{R} C₂ {Q}` only need `R` to hold at the boundary.
`C₁ ∥ C₂` needs `C₁`'s reasoning to survive `C₂` writing at *every* point in between.

:::class "cite"
Owicki–Gries (1976) handles exactly that, by checking every statement against every other — a
quadratic in the number of statements
:::

# Theorem (O'Hearn, CONCUR 2004): own the cells you touch

:::class "steps"
* `l ↦ v` — the heap is *exactly* one cell, at `l`, holding `v`. An ownership claim, not a fact.
* `P ∗ Q` — the heap splits in two *disjoint* halves, one for `P`, one for `Q`
* so `l₁ ↦ 3 ∗ l₂ ↦ 4` already tells you `l₁ ≠ l₂`
:::

```html
<div class="dgm tight">
  <div class="nd mono thm">      {P} C {Q}
─────────────────────────
   {P ∗ R} C {Q ∗ R}<em>frame rule — R is untouched</em></div>
  <div class="nd key">footprint<em>the set of cells C reads, paired with the set it writes</em></div>
</div>
```

:::class "gbox" "thm"
If `C₁` satisfies `{P₁} C₁ {Q₁}`, and `C₂` satisfies `{P₂} C₂ {Q₂}`, and the heap splits as
`P₁ ∗ P₂`, then `C₁ ∥ C₂` satisfies `{P₁ ∗ P₂} C₁ ∥ C₂ {Q₁ ∗ Q₂}`.
:::

Each premise talks about one thread alone. O'Hearn's *Ownership Hypothesis*: a component touches
only what it owns.

# Lemma (Brookes, CONCUR 2004, §5–§7)

Brookes proved O'Hearn's rule sound, with a trace semantics where a racing step becomes a
catastrophic error.

:::class "gbox" "thm"
*Parallel Decomposition.* If a trace of `C₁ ∥ C₂` runs from a state split as `σ₁ ∗ σ₂`, and the two
components' footprints stay separate, then that trace is an *interleaving* of a trace of `C₁` from
`σ₁` and a trace of `C₂` from `σ₂` — and the final states recombine as `σ₁' ∗ σ₂'`.
:::

```html
<div class="dgm tight">
  <div class="nd blue">a run of <code>C₁ ∥ C₂</code></div>
  <div class="arr lbl2">▶<small>factors into</small></div>
  <div class="nd">a solo run of <code>C₁</code></div>
  <div class="nd plain">+</div>
  <div class="nd">a solo run of <code>C₂</code></div>
</div>
```

The interleaving contributes nothing: the two solo runs determine the result.

# What we state, at a strength nobody states it

```html
<div class="bigclaim">
  For <b>any</b> program of <code>read</code>, <code>write</code> and <code>par</code> &mdash;
  branches free to <b>share reads</b> &mdash; if independence holds at <b>every</b> fork, then
  <code>p &#8741; q</code> and <code>p ; q</code> reach <b>exactly the same</b>
  (result, final&nbsp;heap) pairs, under <b>every</b> schedule.
  <span class="bigclaim-sub">Machine-checked in Lean&nbsp;4 &nbsp;&#183;&nbsp; <code>par_seq_eq</code></span>
</div>
```

Four things at once: an *outcome equality* rather than correctness transfer; *shared reads* allowed;
*any* program rather than one loop shape; and *kernel-checked*.

# The separation-logic line: soundness, not equality

```html
<div class="lineage">
  <div class="le">
    <div class="who">O'Hearn<span>CONCUR'04</span></div>
    <div class="thm"><code>{P₁}C₁{Q₁}</code> and <code>{P₂}C₂{Q₂}</code> &rArr; <code>{P₁∗P₂} C₁∥C₂ {Q₁∗Q₂}</code></div>
    <div class="miss">a rule about <i>triples</i> &mdash; says nothing about program equality</div>
  </div>
  <div class="le">
    <div class="who">Brookes<span>CONCUR'04 §5–7</span></div>
    <div class="thm">a trace of <code>C₁∥C₂</code> from <code>σ₁∗σ₂</code> with separate footprints <b>is an interleaving</b> of a trace of <code>C₁</code> from <code>σ₁</code> and one of <code>C₂</code> from <code>σ₂</code>; finals recombine as <code>σ₁′∗σ₂′</code></div>
    <div class="miss">projects <i>one</i> trace &mdash; not equality of outcome <i>sets</i></div>
  </div>
  <div class="le">
    <div class="who">Vafeiadis<span>MFPS'11</span></div>
    <div class="thm"><code>{P}C{Q}</code> derivable &rArr; from any <code>σ⊨P</code>, for every <code>n</code>, <code>C</code> is safe for <code>n</code> steps: no abort, no race, <code>Q</code> on termination</div>
    <div class="miss">soundness of the logic, mechanized &mdash; equivalence never stated</div>
  </div>
  <div class="le">
    <div class="who">Apt &amp; Olderog<span>textbook</span></div>
    <div class="thm"><code>C₁</code>, <code>C₂</code> share <b>no variables</b> &rArr; <code>C₁∥C₂ = C₁;C₂</code> semantically</div>
    <div class="miss">excludes shared reads, so excludes matmul; on paper</div>
  </div>
</div>
```

# The compiler line: restricted, or not kernel-checked

```html
<div class="lineage">
  <div class="le">
    <div class="who">DPJ<span>OOPSLA'09</span></div>
    <div class="thm">in a well-typed program, two expressions with non-interfering effects evaluate in <b>either order</b> with the same values, effects and final heap</div>
    <div class="miss">a Java-like calculus; on paper</div>
  </div>
  <div class="le">
    <div class="who">PolCert<span>TASE'24</span></div>
    <div class="thm">if the validator accepts a candidate affine schedule after checking Bernstein's conditions, the transformed program <b>is equivalent</b> to the original</div>
    <div class="miss">affine loop nests only</div>
  </div>
  <div class="le">
    <div class="who">Blom et al.<span>STTT'21</span></div>
    <div class="thm">given per-block and per-iteration contracts encoding data dependences, functional correctness of the sequential program <b>implies</b> correctness of the parallelised one</div>
    <div class="miss">correctness <i>transfer</i>, not equality; VerCors/Viper, not a kernel</div>
  </div>
  <div class="le ours">
    <div class="who">paralever<span>this work</span></div>
    <div class="thm"><code>WellFormed (par p q) σ</code> &rArr; <code>par p q</code> and <code>p;q</code> reach <b>exactly the same</b> <code>(r, σ′)</code> pairs, under every schedule</div>
    <div class="miss">any <code>ParM</code> program &middot; shared reads allowed &middot; Lean&nbsp;4 kernel</div>
  </div>
</div>
```

# Deterministic parallelism, not concurrency

```html
<table class="dgmt">
  <thead><tr><th></th><th>in scope</th><th>out of scope</th></tr></thead>
  <tbody>
    <tr><th>shared reads</th><td><span class="vd ok">YES</span> — the point of Bernstein</td><td></td></tr>
    <tr><th>shared writes, write/read overlap</th><td></td><td>steps to <code>wrong</code></td></tr>
    <tr><th>locks, ownership transfer, atomics</th><td></td><td>no constructor for them</td></tr>
    <tr><th>unstructured <code>fork</code></th><td></td><td><code>par</code> is fork&ndash;join only</td></tr>
    <tr><th>non-termination</th><td></td><td><code>ParM</code> is inductive</td></tr>
  </tbody>
</table>
```

The exclusions are *structural*, not assumed: there is nothing in `ParM` to write a lock with.

:::class "punch"
Branches that need to talk to each other are a different problem. Branches that do not are common,
and in a proof assistant they are underserved.
:::

# Simuliris is more general; this is cheaper in one case

:::class "gbox" "thm"
*Simuliris* (POPL 2022). If the source is data-race-free, the transformation is sound:
termination-preserving refinement under a fair scheduler. In a real sense this **generalises** our
theorem — it covers interference, we do not.
:::

What we give up: locks, ownership transfer, inter-branch communication, non-termination.

What the restriction buys:

* a **two-sided equality** on outcome sets, not a one-sided refinement
* the per-program obligation is **decidable arithmetic** — often `by decide` — not a
  separation-logic proof
* a cost theorem on the same object: `max` at a fork, *derived*
* Lean 4 — ReLoC and Simuliris are Coq, with no port

:::class "cite"
*Gäher et al.*, _Simuliris_, *POPL 2022* · *Frumin, Krebbers, Birkedal*, _ReLoC Reloaded_, *LMCS 2021* ·
Iris's `∗` is exclusive heap-split, stronger than Bernstein — it rejects matmul without fractional permissions
:::

# Equality is not false — it is false for *their* language

```html
<div class="dgm col tight">
  <div class="nd bad wide">full CSL has locks and ownership transfer<em>two threads legitimately communicate through shared state, so <code>C₁∥C₂</code> and <code>C₁;C₂</code> genuinely differ — the equality is <b>not</b> a theorem of their system</em></div>
  <div class="arr">▼</div>
  <div class="nd good wide">it holds in the lock-free, no-transfer fragment (DCSL)<em>which is exactly our scope — but isolating that fragment was not their goal</em></div>
</div>
```

* *soundness* is about derivable triples: if you proved `{P} C {Q}`, the program satisfies it
* *equality* is about the programs: it transfers *every* spec, including ones nobody wrote,
  and in both directions
* Apt & Olderog *do* state an equality — for programs sharing nothing at all

:::class "punch"
So the gap is not "equality is unproved". It is: nobody states it at Bernstein strength, for an
arbitrary program, checked by a kernel.
:::

# Blom et al. have our architecture; we have a different theorem

```html
<table class="dgmt">
  <thead><tr><th></th><th>Blom et al., STTT 2021</th><th>paralever</th></tr></thead>
  <tbody>
    <tr><th>what is proved</th><td>functional correctness of the sequential program ⇒ correctness of the parallelised one</td><td><code>par_seq_eq</code>: the two reach the <b>same outcome set</b></td></tr>
    <tr><th>strength</th><td>transfers the contract you wrote</td><td>transfers <b>every</b> spec, and rules out extra outcomes</td></tr>
    <tr><th>obligation</th><td>per-block and per-iteration contracts recording dependences</td><td><code>WellFormed</code> — Bernstein at every fork</td></tr>
    <tr><th>checked by</th><td>VerCors / Viper + SMT<em>tool and backend trusted</em></td><td>Lean 4 kernel<em>no axioms beyond Lean's own</em></td></tr>
  </tbody>
</table>
```

Their composition algebra is the sanity check our constructors were designed against, and their
OpenMP pragma work is the direct precedent for ours. The difference is the shape of the theorem and
who checks it.

# A race is a shared cell with at least one write

```html
<table class="dgmt">
  <tbody>
    <tr><td>write / write</td><td>the final value depends on who went last</td><td><span class="vd no">RACE</span></td></tr>
    <tr><td>read&nbsp;&nbsp;/ write</td><td>the reader sees the old or the new value</td><td><span class="vd no">RACE</span></td></tr>
    <tr><td>read&nbsp;&nbsp;/ read</td><td>both see the same value, whatever the order</td><td><span class="vd ok">FINE</span></td></tr>
  </tbody>
</table>
```

Read/read is not a race. That one row is why `∗`-disjointness is the wrong criterion for us.


:::class "gbox" "thm"
Two statements can be run in either order, or at the same time, with the same result exactly when
neither writes a cell the other touches. Writing the read set `R` and the write set `W`:
`W₁∩W₂ = ∅`, `W₁∩R₂ = ∅`, `W₂∩R₁ = ∅`. Nothing is required of `R₁∩R₂`.
:::

```leanLibCode Paralever.Core.Access (package := paralever) (startLine := 62) (endLine := 64) -stretch
@[simp, grind .]
def Indep (f₁ f₂ : Footprint) : Prop :=
  Disjoint f₁.writes f₂.writes ∧ Disjoint f₁.writes f₂.reads ∧ Disjoint f₂.writes f₁.reads
```

# Matrix multiply needs the missing clause

```html
<div class="dgm col tight">
  <div class="nd mono blue">for i, j in parallel:   C[i][j] = Σₖ A[i][k] * B[k][j]</div>
  <table class="dgmt">
    <tbody>
      <tr><th>writes</th><td>C[i][j]</td><td>one cell per task, all different</td><td><span class="vd ok">OK</span></td></tr>
      <tr><th>reads</th><td>row i of A, col j of B</td><td>every task in row i reads the same row</td><td><span class="vd no">HUGE OVERLAP</span></td></tr>
    </tbody>
  </table>
  <div class="dgm tight">
    <div class="nd bad"><code>∗</code>-disjointness <span class="vd no">REJECTS</span><em>there is no heap split</em></div>
    <div class="nd good">Bernstein <span class="vd ok">ACCEPTS</span><em>it never looks at R∩R</em></div>
  </div>
</div>
```

# A program is a tree, so an interpreter can read its accesses

Here is a bank transfer. `readInt` and `ParM.wr` are the read and write nodes; `do` just builds the
tree.

```lean -stretch
def balA : Loc := 0
def balB : Loc := 1
def balC : Loc := 2
def auditLog : Loc := 10

def transfer (src dst : Loc) (amt : Int) : ParM Unit := do
  let s ← readInt src
  let d ← readInt dst
  ParM.wr src (.int (s - amt))
  ParM.wr dst (.int (d + amt))

-- what it touches, whatever the balances happen to be
theorem transfer_accesses (src dst : Loc) (amt : Int) (σ : State) :
    accesses (transfer src dst amt) σ = ⟨[src, dst], [src, dst]⟩ := rfl
```

Nothing runs when you write that. `transfer` *is* a tree, and `accesses` folds over it.

# Every path down the tree ends in `pure`

```html
<div class="treewrap">
<pre>read  A[0] -> x
read  A[1] -> y
if x &lt; y then write A[2] &lt;- x+y
         else write A[2] &lt;- x-y</pre>
<svg viewBox="0 0 580 400" role="img" aria-label="program tree">
  <defs>
    <marker id="treetip" viewBox="0 0 10 10" refX="9" refY="5"
            markerWidth="6" markerHeight="6" orient="auto-start-reverse">
      <path d="M 0 0 L 10 5 L 0 10 z" fill="#64748b"/>
    </marker>
  </defs>
  <g stroke="#64748b" stroke-width="1.6" marker-end="url(#treetip)" fill="none">
    <line x1="290" y1="54"  x2="290" y2="86"/>
    <line x1="275" y1="134" x2="150" y2="178"/>
    <line x1="305" y1="134" x2="430" y2="178"/>
    <line x1="150" y1="226" x2="150" y2="286"/>
    <line x1="430" y1="226" x2="430" y2="286"/>
  </g>
  <g font-size="15" text-anchor="middle">
    <rect x="200" y="14" width="180" height="40" rx="7" fill="#eff6ff" stroke="#2563eb"/>
    <text x="290" y="39">read A[0]</text>

    <rect x="200" y="86" width="180" height="40" rx="7" fill="#eff6ff" stroke="#2563eb"/>
    <text x="290" y="111">read A[1]</text>

    <rect x="34"  y="186" width="232" height="40" rx="7" fill="#fff7ed" stroke="#c2410c"/>
    <text x="150" y="211">write A[2] &#8592; x+y</text>

    <rect x="314" y="186" width="232" height="40" rx="7" fill="#fff7ed" stroke="#c2410c"/>
    <text x="430" y="211">write A[2] &#8592; x&#8722;y</text>

    <rect x="104" y="286" width="92" height="38" rx="7" fill="#f0fdfa" stroke="#0f766e"/>
    <text x="150" y="311">pure</text>

    <rect x="384" y="286" width="92" height="38" rx="7" fill="#f0fdfa" stroke="#0f766e"/>
    <text x="430" y="311">pure</text>
  </g>
  <g font-size="13" fill="#64748b" font-style="italic">
    <text x="299" y="76">x</text>
    <text x="178" y="150" text-anchor="end">x &lt; y</text>
    <text x="402" y="150">x &#8805; y</text>
  </g>
</svg>
</div>
```

* a `read` node has one child *per value it could return* --- that is why this branches
* arithmetic happens inside a node, so `x+y` never appears in the tree's shape
* `accesses` folds this tree; `runSeq` walks one path down it

# Four constructors, and `par` is one of them

::::::hstack
:::::vstack
```leanLibCode Paralever.Core.ParM (package := paralever) (startLine := 84) (endLine := 91) -stretch
inductive ParM : Type → Type 1 where
  | pure  {α : Type}     : α → ParM α
  | read  {α : Type}     : Loc → (Val → ParM α) → ParM α
  | write {α : Type}     : Loc → Val → (Unit → ParM α) → ParM α
  /-- Fork every child at once, then continue with all their results. The only constructor whose
  meaning Lean does not already fix: `run` interprets it by interleaving, which is what makes the
  sequentialization theorem non-vacuous. -/
  | par   {β : Type} {αs : List Type} : Childs ParM αs → (Results αs → ParM β) → ParM β
```

* `pure a` — stop here and hand back `a`
* `read l k` — look at cell `l`; what is in it is handed to `k`
* `write l v k` — put `v` into cell `l`, then carry on with `k`
* `par cs k` — start *every* child in `cs`, wait for all, hand all results to `k`
:::::
:::::vstack
The last argument of each is a *function*: the rest of the program, waiting for a value. So
`read 5 k` is "read cell 5, then do `k` of what you found". That is why the top of the tree is
always the next thing to run.

`par` is N-ary. `Childs ParM αs` is the list of children, indexed by the types they return, and
`Results αs` is the matching tuple of their values:

```
Childs ParM [Unit, Val]   two children, returning Unit and Val
Results    [Unit, Val]  = Unit × Val × Unit
```

Nothing says which child goes first, or whether they alternate. `run` decides, and may decide
differently every time; `k` runs only after all of them finish.
:::::
::::::

:::notes
Lean's Task cannot host this: (Task.spawn f).get = f () by rfl, so parallel and sequential would be
the same term and there would be no theorem. Task stays as the compilation target.
:::

# A `par` node holds a list of children and one continuation

`sumRangePar [[0,1],[2,3],[4,5]]` — three chunks of a six-cell array, one fork.

```html
<div class="dgm col tight">
  <div class="nd key">par&nbsp; cs&nbsp; k</div>
  <div class="dgm tight top">
    <div class="nd mono blue">read  [0] → 0
read  [1] → 1
pure<em>child [0] &nbsp;: ParM Int</em></div>
    <div class="nd mono blue">read  [2] → 2
read  [3] → 3
pure<em>child [1] &nbsp;: ParM Int</em></div>
    <div class="nd mono blue">read  [4] → 4
read  [5] → 5
pure<em>child [2] &nbsp;: ParM Int</em></div>
  </div>
  <div class="arr lbl2">▼<small>join — every child finished</small></div>
  <div class="nd mono">k vs = pure (resultsToList vs)<em>continuation &nbsp;k : Results αs → ParM γ</em></div>
</div>
```

* three children, **one** fork node — not a staircase of nested binary forks
* every child reads two cells and writes none, so they are trivially independent
* `k` runs once *all* children finish, and receives one result from each

:::class "cite"
printed by `render`, the same walk `accesses` does — `Lib/Render.lean`
:::

# `parPair` is `N = 2`; `parAll` is the same node, any length

Only `par` is primitive. Both pairings are it, at different arities.

```leanLibCode Paralever.Core.ParM (package := paralever) (startLine := 205) (endLine := 206) -stretch
def parPair (p : ParM α) (q : ParM β) : ParM (α × β) :=
  .par Π[ p q ] (fun r => .pure (r.1, r.2.1))
```

```leanLibCode Paralever.Core.ParM (package := paralever) (startLine := 235) (endLine := 236) -stretch
def parAll {α : Type} (ps : List (ParM α)) : ParM (List α) :=
  .par (childsOf ps) (fun x => .pure (resultsToList ps x))
```

```leanLibCode Paralever.Core.ParM (package := paralever) (startLine := 210) (endLine := 212) -stretch
@[simp, grind .]
def seqPair (p : ParM α) (q : ParM β) : ParM (α × β) :=
  bind p (fun a => bind q (fun b => .pure (a, b)))
```

So the theorem is proved **N-arily**, by induction on the children list, and `parPair`'s case is
`N = 2`. There is no binary theorem for it to be a corollary of.

# `step` is nondeterministic; `runSeq` is the reference run

`step` returns a *list* of successors — a `par` node can go either way. A racing `par` node steps to
`wrong`.

```html
<div class="dgm tight">
  <div class="nd mono defbox">Loc   := Nat
Val   := int | bool | unit
State := Loc → Val</div>
  <div class="nd mono defbox">inductive Conf (α) where
  | run   : ParM α → State → Conf α
  | wrong : Conf α</div>
</div>
```

```leanLibCode Paralever.Core.Semantics (package := paralever) (startLine := 173) (endLine := 175) -stretch
inductive Reaches {α : Type} : Conf α → Conf α → Prop where
  | refl {c} : Reaches c c
  | tail {c c' c''} : Reaches c c' → c'' ∈ stepC c' → Reaches c c''
```

`runSeq p σ` is the other half: one fixed left-to-right run, a function rather than a relation. It is
the reference the theorem compares against.

# `WellFormed`: check Bernstein at every `par`, not just the top

::::::hstack
:::::vstack
```leanLibCode Paralever.Core.Access (package := paralever) (startLine := 184) (endLine := 190) -stretch
def WellFormed {τ : Type} : ParM τ → State → Prop
  | .pure _,      _ => True
  | .read l k,    σ => WellFormed (k (σ l)) σ
  | .write l v k, σ => WellFormed (k ()) (σ.update l v)
  | .par cs k,    σ =>
      let r := runChilds cs σ
      IndepAll (childFootprints cs σ) ∧ WellFormedChilds cs σ ∧ WellFormed (k r.1) r.2
```

It walks the whole tree; only `par` checks anything.

* `pure` — nothing to check
* `read l k` — walk into `k` with the value in cell `l`
* `write l v k` — walk into `k` with `l` now holding `v`
* `par cs k` — the three conjuncts opposite
:::::
:::::vstack
At a `par` node, in order:

* `Indep (accesses p σ) (accesses q σ₁)` — the branches' footprints satisfy Bernstein
* `WellFormed p σ` — `p` is clean all the way down
* `WellFormed q σ₁` — and so is `q`
* `WellFormed (k (a,b)) σ₂` — and so is everything after the join

The `let` lines name states: `σ₁` is the heap after `p`, `σ₂` after `q` as well, and `a`, `b` are the
results the join hands to `k`. Footprints must be measured against *some* state; these are the ones
the reference run reaches.

`p` being independent of `q` says nothing about a `par` buried inside `p`, so checking only the
outermost node would be unsound.
:::::
::::::

# A top-level check passes this racy program

```html
<div class="treewrap">
<pre>par ( par  write A[0]
           write A[0] )
    (      write A[9] )</pre>
<svg viewBox="0 0 600 400" role="img" aria-label="nested par tree">
  <defs>
    <marker id="nesttip" viewBox="0 0 10 10" refX="9" refY="5"
            markerWidth="6" markerHeight="6" orient="auto-start-reverse">
      <path d="M 0 0 L 10 5 L 0 10 z" fill="#64748b"/>
    </marker>
  </defs>
  <g stroke="#64748b" stroke-width="1.6" marker-end="url(#nesttip)" fill="none">
    <line x1="275" y1="46"  x2="165" y2="96"/>
    <line x1="325" y1="46"  x2="455" y2="96"/>
    <line x1="140" y1="144" x2="70"  y2="196"/>
    <line x1="190" y1="144" x2="260" y2="196"/>
    <line x1="70"  y1="244" x2="70"  y2="296"/>
    <line x1="260" y1="244" x2="260" y2="296"/>
    <line x1="455" y1="144" x2="455" y2="296"/>
  </g>
  <g font-size="15" text-anchor="middle">
    <rect x="258" y="10" width="84" height="36" rx="7" fill="#eef2ff" stroke="#4f46e5"/>
    <text x="300" y="34">par</text>

    <rect x="123" y="96" width="84" height="48" rx="7" fill="#fef2f2" stroke="#dc2626" stroke-width="2"/>
    <text x="165" y="126">par</text>

    <rect x="395" y="96" width="120" height="48" rx="7" fill="#fff7ed" stroke="#c2410c"/>
    <text x="455" y="126">write A[9]</text>

    <rect x="10"  y="196" width="120" height="48" rx="7" fill="#fff7ed" stroke="#c2410c"/>
    <text x="70"  y="226">write A[0]</text>

    <rect x="200" y="196" width="120" height="48" rx="7" fill="#fff7ed" stroke="#c2410c"/>
    <text x="260" y="226">write A[0]</text>

    <rect x="28"  y="296" width="84" height="36" rx="7" fill="#f0fdfa" stroke="#0f766e"/>
    <text x="70"  y="320">pure</text>
    <rect x="218" y="296" width="84" height="36" rx="7" fill="#f0fdfa" stroke="#0f766e"/>
    <text x="260" y="320">pure</text>
    <rect x="413" y="296" width="84" height="36" rx="7" fill="#f0fdfa" stroke="#0f766e"/>
    <text x="455" y="320">pure</text>
  </g>
  <g font-size="13" font-style="italic">
    <text x="300" y="70" fill="#15803d" text-anchor="middle">outer: {0} vs {9} &#8212; disjoint &#10003;</text>
    <text x="165" y="176" fill="#b91c1c" text-anchor="middle">inner: 0 written twice &#10007;</text>
  </g>
</svg>
</div>
```

The outer pair is independent: the left branch touches only cell `0`, the right only cell `9`. The
inner pair writes cell `0` twice. Checking the outermost node alone accepts this; `WellFormed`
recurses, reaches the red node, and rejects it.

# Independent branches reach the same outcomes as `p; q`

Four parts to the claim:

* "never touch each other's data" means *Bernstein*: neither writes a cell the other reads or writes
* sharing *reads* is allowed, so matrix multiply counts as independent
* it must hold for *every* schedule, not one measured run
* and it must hold for `par` nodes nested inside, not only the outermost one

That is exactly `WellFormed`, and the conclusion is `ParSeqEq`:

:::class "gbox" "thm"
If `parPair p q` is well-formed in `σ`, then `parPair p q` and `seqPair p q` reach exactly the same
`(result, final state)` pairs from `σ`.
:::

```lean -stretch
theorem the_metatheorem {α β : Type} (p : ParM α) (q : ParM β) (σ : State)
    (h : WellFormed (ParM.parPair p q) σ) :
    ParM.parPair p q ∥≡ ParM.seqPair p q from σ :=
  par_seq_eq p q σ h
```

```leanLibCode Paralever.Theory.Sequentialize (package := paralever) (startLine := 17) (endLine := 18) -stretch
def ParSeqEq {α : Type} (p q : ParM α) (σ : State) : Prop :=
  ∀ r σ', Reaches (.run p σ) (.run (.pure r) σ') ↔ Reaches (.run q σ) (.run (.pure r) σ')
```

# Bernstein and Brookes combine into `par_seq_eq`

```html
<div class="dgm col tight">
  <div class="dgm tight">
    <div class="nd">Bernstein 1966<em>when two statements commute</em></div>
    <div class="arr">▶</div>
    <div class="nd blue"><code>Indep</code><em>on footprints</em></div>
    <div class="arr">▶</div>
    <div class="nd blue"><code>WellFormed</code><em><code>Indep</code> at every <code>par</code> node</em></div>
  </div>
  <div class="arr">▼</div>
  <div class="dgm tight">
    <div class="nd">Brookes §5–7<em>traces factor</em></div>
    <div class="arr">▶</div>
    <div class="nd blue"><code>wellFormed_canonical</code><em>only one outcome is reachable</em></div>
  </div>
  <div class="arr">▼</div>
  <div class="nd key wide"><code>par_seq_eq</code><em>apply uniqueness to both sides; they share one <code>runSeq</code> value</em></div>
  <div class="arr lbl2">▼<small>left for the user, per program</small></div>
  <div class="nd good wide"><code>WellFormed</code> — bound each footprint, then arithmetic</div>
</div>
```


# Three proofs compose into `pure = par`

```html
<div class="pipewrap">
<svg viewBox="0 0 920 430" role="img" aria-label="proof pipeline">
  <defs>
    <marker id="pipetip" viewBox="0 0 10 10" refX="9" refY="5"
            markerWidth="7" markerHeight="7" orient="auto-start-reverse">
      <path d="M 0 0 L 10 5 L 0 10 z" fill="#475569"/>
    </marker>
  </defs>

  <!-- the three representations -->
  <g font-size="19" text-anchor="middle">
    <rect x="20"  y="40" width="250" height="72" rx="9" fill="#f0fdfa" stroke="#0f766e" stroke-width="2"/>
    <text x="145" y="72">pure function</text>
    <text x="145" y="96" font-size="15" font-style="italic" fill="#475569">+ its proof (ordinary Lean)</text>

    <rect x="335" y="40" width="250" height="72" rx="9" fill="#eff6ff" stroke="#2563eb" stroke-width="2"/>
    <text x="460" y="72">fooSeq : ParM</text>
    <text x="460" y="96" font-size="15" font-style="italic" fill="#475569">sequential representation</text>

    <rect x="650" y="40" width="250" height="72" rx="9" fill="#eef2ff" stroke="#4f46e5" stroke-width="2"/>
    <text x="775" y="72">fooPar : ParM</text>
    <text x="775" y="96" font-size="15" font-style="italic" fill="#475569">parallel representation</text>
  </g>

  <!-- chain arrows -->
  <g stroke="#475569" stroke-width="2" marker-end="url(#pipetip)" fill="none">
    <line x1="272" y1="76" x2="331" y2="76"/>
    <line x1="587" y1="76" x2="646" y2="76"/>
  </g>

  <!-- the three obligations -->
  <g font-size="16" text-anchor="middle">
    <rect x="35"  y="150" width="220" height="56" rx="8" fill="#ffffff" stroke="#0f766e"/>
    <text x="145" y="172" font-weight="bold">1 &#183; prove pure</text>
    <text x="145" y="194" font-size="14" fill="#475569">no concurrency in it</text>

    <rect x="350" y="150" width="220" height="56" rx="8" fill="#ffffff" stroke="#2563eb"/>
    <text x="460" y="172" font-weight="bold">2 &#183; pure = seq</text>
    <text x="460" y="194" font-size="14" fill="#475569">pure_eq_seq</text>

    <rect x="665" y="150" width="220" height="56" rx="8" fill="#ffffff" stroke="#4f46e5"/>
    <text x="775" y="172" font-weight="bold">3 &#183; seq = par</text>
    <text x="775" y="194" font-size="14" fill="#475569">par_seq_eq &#8212; proved once</text>
  </g>
  <g stroke="#94a3b8" stroke-width="1.4" stroke-dasharray="4 3" fill="none">
    <line x1="145" y1="114" x2="145" y2="148"/>
    <line x1="460" y1="114" x2="460" y2="148"/>
    <line x1="775" y1="114" x2="775" y2="148"/>
  </g>

  <!-- composition into the conclusion -->
  <g stroke="#475569" stroke-width="2" marker-end="url(#pipetip)" fill="none">
    <path d="M 145 208 C 145 300, 330 300, 400 322"/>
    <path d="M 460 208 C 460 290, 460 300, 460 318"/>
    <path d="M 775 208 C 775 300, 590 300, 520 322"/>
  </g>
  <text x="625" y="285" font-size="15" font-style="italic" fill="#475569">by transitivity</text>

  <rect x="265" y="322" width="390" height="72" rx="10" fill="#fefce8" stroke="#a16207" stroke-width="2.5"/>
  <text x="460" y="352" font-size="22" text-anchor="middle" font-weight="bold">pure = par</text>
  <text x="460" y="378" font-size="15" text-anchor="middle" font-style="italic" fill="#475569">the parallel program computes the specification</text>
</svg>
</div>
```

Step 3 is proved once, for every program. Steps 1 and 2 are the user's, and step 1 is the ordinary
verification problem they would have had anyway.

# Races stop at `wrong`, so the step size does not matter

```html
<div class="dgm col tight">
  <div class="nd blue wide">a racy program steps to <code>wrong</code>, and <code>wrong</code> is terminal</div>
  <div class="arr">▼</div>
  <div class="nd good wide">for race-free programs, every choice of atomic step agrees</div>
  <div class="arr">▼</div>
  <div class="nd key wide">so the hypothesis <i>throws out</i> racy programs instead of guessing what they do</div>
</div>
```

:::class "cite"
*Reynolds*, _Toward a Grainless Semantics for Shared-Variable Concurrency_, *FSTTCS 2004*
:::


:::class "steps"
* `accesses p σ` is about `p` running *alone*
* the conclusion is about `p` running *interleaved* with `q`
* and a footprint depends on values read, which inside `p ∥ q` may come from `q`
:::

:::class "gbox" "thm"
*Invariant.* At every point of the interleaved run, the heap restricted to `p`'s footprint looks
exactly as it would in `p`'s solo run.
:::

When `q` takes a step it writes inside `q`'s footprint, which `Indep` keeps away from `p`'s reads — so
`p`'s view does not move. `step_combined` does one step; `WellFormed_preserved` lets you take the
next.

# Each program shape has its own one-shot theorem

```html
<table class="dgmt">
  <thead><tr><th>Program</th><th>Shape</th><th>Route</th><th>What you prove</th></tr></thead>
  <tbody>
    <tr><td>sort several batches</td><td>pure, over values</td><td><code>parMap</code></td><td><span class="vd ok">nothing</span></td></tr>
    <tr><td>brighten an image</td><td><code>Out[i] = f(In[i])</code></td><td><code>mapArray</code></td><td>equal lengths, one <code>omega</code></td></tr>
    <tr><td>matrix multiply</td><td><code>C[i,j] = Σₖ …</code></td><td><code>reduceArray</code></td><td>3 arithmetic facts</td></tr>
    <tr><td>row sums</td><td><code>Out[i] = Σⱼ A[i,j]</code></td><td><code>reduceArray</code></td><td>3 arithmetic facts</td></tr>
    <tr><td>chunked array sum</td><td>read-only folds</td><td><code>indep_of_no_writes</code></td><td>the writes are empty</td></tr>
    <tr><td>odd-even transposition sort</td><td>disjoint compare-swaps</td><td><code>parAll_…_indexed_rw</code></td><td>pairwise disjointness</td></tr>
    <tr><td>parallel merge sort</td><td>recursive, with scratch</td><td><code>TouchesOnly</code></td><td>range disjointness</td></tr>
    <tr><td>a subsystem you do not own</td><td>opaque body</td><td><code>opaqueOp</code></td><td>declared R/W disjoint</td></tr>
    <tr><td>a straight-line block</td><td><code>load</code>/<code>store</code></td><td><code>Block</code> IR</td><td><code>by decide</code></td></tr>
  </tbody>
</table>
```

Every row is a worked file in `Examples/`, built alongside this deck.

# Sum: chunked reduction

```leanLibCode Examples.SumArray (package := paralever) (decl := Paralever.Examples.SumArray.sumRangePure) -stretch
def sumRangePure (σ : State) : List Loc → Int
  | []      => 0
  | l :: ls =>
      match σ l with
      | .int n => n + sumRangePure σ ls
      | _      => sumRangePure σ ls
```

```leanLibCode Examples.SumArray (package := paralever) (decl := Paralever.Examples.SumArray.sumRangeSeq) -stretch
def sumRangeSeq (chunks : ChunkPlan) : ParM (List Int) := ParM.seqAll (chunks.map sumRange)
```

```leanLibCode Examples.SumArray (package := paralever) (decl := Paralever.Examples.SumArray.sumRangePar) -stretch
def sumRangePar (chunks : ChunkPlan) : ParM (List Int) := ParM.parAll (chunks.map sumRange)
```

```leanLibCode Examples.SumArray (package := paralever) (decl := Paralever.Examples.SumArray.seq_eq_par) -stretch
theorem seq_eq_par (chunks : ChunkPlan) (σ : State) :
    sumRangePar chunks ∥≡ sumRangeSeq chunks from σ :=
  parAll_par_seq_eq (chunks.map sumRange) σ (wellFormed_sumRangePar chunks σ)
```


# Sort: a round of compare-exchanges

```leanLibCode Examples.Sort (package := paralever) (decl := Paralever.Examples.Sort.swapRoundPure) -stretch
def swapRoundPure (plan : SwapPlan) (σ : State) : State :=
  plan.foldl (fun σ p => swapPure p.1 p.2 σ) σ
```

```leanLibCode Examples.Sort (package := paralever) (decl := Paralever.Examples.Sort.swapRoundSeq) -stretch
def swapRoundSeq (plan : SwapPlan) : ParM (List Unit) :=
  ParM.seqAll (plan.map (fun (i, j) => compareSwap i j))
```

```leanLibCode Examples.Sort (package := paralever) (decl := Paralever.Examples.Sort.swapRoundPar) -stretch
def swapRoundPar (plan : SwapPlan) : ParM (List Unit) :=
  ParM.parAll (plan.map (fun (i, j) => compareSwap i j))
```

```leanLibCode Examples.Sort (package := paralever) (decl := Paralever.Examples.Sort.seq_eq_par) -stretch
theorem seq_eq_par (plan : SwapPlan) (σ : State) (h : plan.locs.Nodup) :
    swapRoundPar plan ∥≡ swapRoundSeq plan from σ :=
  parAll_par_seq_eq _ σ (wellFormed_swapRoundPar plan σ h)
```


# Matrix multiply: one output cell per task

```leanLibCode Examples.MatMul (package := paralever) (decl := Paralever.Examples.MatMul.matmulPure) -stretch
/-- `C[p]` as a function of the heap. -/
def matmulPure (n : Nat) (σ : State) (p : Nat) : Int := foldPure σ (dotLocs n p) dotCombine n 0 0
```

```leanLibCode Examples.MatMul (package := paralever) (decl := Paralever.Examples.MatMul.matmulSeq) -stretch
def matmulSeq (n : Nat) : ParM (List Unit) :=
  reduceArrayPureS (n * n) n (dotLocs n) dotCombine 0 Val.int (cellLoc n)
```

```leanLibCode Examples.MatMul (package := paralever) (decl := Paralever.Examples.MatMul.matmulPar) -stretch
def matmulPar (n : Nat) : ParM (List Unit) :=
  reduceArrayPureP (n * n) n (dotLocs n) dotCombine 0 Val.int (cellLoc n)
```

```leanLibCode Examples.MatMul (package := paralever) (decl := Paralever.Examples.MatMul.seq_eq_par) -stretch
theorem seq_eq_par (n : Nat) (σ : State) : matmulPar n ∥≡ matmulSeq n from σ :=
  reduceArrayPure_par_seq_eq (n * n) n (dotLocs n) dotCombine 0 Val.int (cellLoc n) (InputRegion n)
    (hlocs n) (hdstinj n) (hdstout n) σ
```


# Straight-line blocks: footprints computed, not proved

An IR of two instructions. `AExp` has no memory operand, so every heap value goes through a `load`,
and the footprint is a fold over the list.

:::class "gbox" "defbox"
```
inductive AExp  | lit | reg | add | sub | mul
inductive Instr | load  : Reg → Loc → Instr      -- r := M[l]
                | store : Loc → AExp → Instr     -- M[l] := e
abbrev   Block  := List Instr
```
:::

```lean -stretch
example (b : Block) (ρ : Regs) (σ : State) :
    accesses (exec b ρ) σ = footprintOf b :=
  exec_accesses b ρ σ
```

Registers never enter a footprint — the same split LLVM's `mem2reg` makes.


`procP` works over `a = [0,4)` and `b = [4,8)`; `procQ` over `c` and `d`. Each reads back a cell it
just wrote, so neither is a plain elementwise map.

```html
<div class="dgm tight">
  <div class="nd mono">footprintOf procP = ⟨[0,1,4], [4,2,7]⟩<em>by rfl</em></div>
  <div class="nd good mono">block_par_seq_eq_of_indepB … (by decide)<em>the whole proof</em></div>
</div>
```

# Parallelise a region, not the whole program

```html
<div class="pipewrap">
<svg viewBox="0 0 950 320" role="img" aria-label="region substitution">
  <defs>
    <marker id="regtip" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7"
            orient="auto-start-reverse"><path d="M 0 0 L 10 5 L 0 10 z" fill="#475569"/></marker>
  </defs>
  <g font-size="18" text-anchor="middle">
    <rect x="20"  y="30" width="200" height="56" rx="8" fill="#f8fafc" stroke="#94a3b8"/>
    <text x="120" y="56">markStart</text>
    <text x="120" y="76" font-size="13" fill="#475569" font-style="italic">sequential</text>

    <rect x="290" y="22" width="310" height="72" rx="9" fill="#eef2ff" stroke="#4f46e5" stroke-width="2.5"/>
    <text x="445" y="52">sumInto &#8741; prodInto</text>
    <text x="445" y="76" font-size="13" fill="#475569" font-style="italic">the region</text>

    <rect x="670" y="30" width="200" height="56" rx="8" fill="#f8fafc" stroke="#94a3b8"/>
    <text x="770" y="56">markDone</text>
    <text x="770" y="76" font-size="13" fill="#475569" font-style="italic">sequential</text>
  </g>
  <g stroke="#475569" stroke-width="2" marker-end="url(#regtip)" fill="none">
    <line x1="222" y1="58" x2="286" y2="58"/>
    <line x1="602" y1="58" x2="666" y2="58"/>
  </g>

  <g stroke="#94a3b8" stroke-width="1.4" stroke-dasharray="4 3" fill="none">
    <line x1="445" y1="96" x2="445" y2="138"/>
    <line x1="120" y1="88" x2="120" y2="214"/>
    <line x1="770" y1="88" x2="770" y2="214"/>
  </g>

  <g font-size="15" text-anchor="middle">
    <rect x="276" y="138" width="338" height="54" rx="8" fill="#ffffff" stroke="#4f46e5"/>
    <text x="445" y="159" font-weight="bold">WellFormed &#8212; here and nowhere else</text>
    <text x="445" y="180" font-size="13" fill="#475569">same reads, different writes: one `decide`</text>

    <text x="120" y="228" font-size="13" fill="#475569">trivial</text>
    <text x="770" y="228" font-size="13" fill="#475569">trivial</text>
  </g>

  <g stroke="#475569" stroke-width="2" marker-end="url(#regtip)" fill="none">
    <path d="M 445 192 C 445 240, 445 246, 445 256"/>
  </g>
  <rect x="222" y="258" width="446" height="52" rx="9" fill="#fefce8" stroke="#a16207" stroke-width="2.5"/>
  <text x="445" y="282" font-size="18" text-anchor="middle" font-weight="bold">par_seq_eq_region</text>
  <text x="445" y="302" font-size="13" text-anchor="middle" fill="#475569">the whole program's outcomes are unchanged</text>
</svg>
</div>
```

```leanLibCode Examples.Region (package := paralever) (startLine := 64) (endLine := 74) -stretch
def wholeSeq : ParM Unit :=
  doₚ
    markStart
    let (_s, _p) ← sumInto ;; prodInto
    markDone

def wholePar : ParM Unit :=
  doₚ
    markStart
    let (_s, _p) ← sumInto ∥ prodInto
    markDone
```

# The pure proofs compose, and the region is invisible to them

```html
<div class="pipewrap">
<svg viewBox="0 0 950 260" role="img" aria-label="Computes assembly">
  <defs>
    <marker id="cmptip" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7"
            orient="auto-start-reverse"><path d="M 0 0 L 10 5 L 0 10 z" fill="#475569"/></marker>
  </defs>
  <g font-size="15" text-anchor="middle">
    <rect x="10"  y="14"  width="196" height="36" rx="7" fill="#f0fdfa" stroke="#0f766e"/>
    <text x="108" y="38">Computes markStart</text>
    <rect x="10"  y="68"  width="196" height="36" rx="7" fill="#f0fdfa" stroke="#0f766e"/>
    <text x="108" y="92">Computes sumInto</text>
    <rect x="10"  y="122" width="196" height="36" rx="7" fill="#f0fdfa" stroke="#0f766e"/>
    <text x="108" y="146">Computes prodInto</text>
    <rect x="10"  y="176" width="196" height="36" rx="7" fill="#f0fdfa" stroke="#0f766e"/>
    <text x="108" y="200">Computes markDone</text>

    <rect x="286" y="95" width="210" height="52" rx="8" fill="#eef2ff" stroke="#4f46e5" stroke-width="2"/>
    <text x="391" y="117" font-weight="bold">Computes.parPair</text>
    <text x="391" y="137" font-size="12" fill="#475569">or .seqPair &#8212; same result</text>

    <rect x="566" y="95" width="180" height="52" rx="8" fill="#ffffff" stroke="#475569"/>
    <text x="656" y="117" font-weight="bold">Computes.bind</text>
    <text x="656" y="137" font-size="12" fill="#475569">chains the pieces</text>

    <rect x="790" y="88" width="150" height="66" rx="9" fill="#fefce8" stroke="#a16207" stroke-width="2.5"/>
    <text x="865" y="112" font-weight="bold">wholePure</text>
    <text x="865" y="133" font-size="12" fill="#475569">one pure</text>
    <text x="865" y="148" font-size="12" fill="#475569">state transformer</text>
  </g>
  <g stroke="#475569" stroke-width="1.7" marker-end="url(#cmptip)" fill="none">
    <path d="M 208 86  C 250 100, 260 110, 282 115"/>
    <path d="M 208 140 C 250 132, 260 128, 282 124"/>
    <line x1="498" y1="121" x2="562" y2="121"/>
    <path d="M 208 32  C 540 32, 600 70, 650 91"/>
    <path d="M 208 194 C 540 194, 600 158, 650 151"/>
    <line x1="748" y1="121" x2="786" y2="121"/>
  </g>
</svg>
</div>
```

```leanLibCode Examples.Region (package := paralever) (startLine := 87) (endLine := 96) -stretch
theorem seq_computes : Computes wholeSeq (fun _ => ()) wholePure :=
  (markStart_computes.bind (fun _ =>
    (sumInto_computes.seqPair prodInto_computes).bind (fun _ => markDone_computes)))

/-- **The parallel program computes the same pure function.** Identical proof, with
`Computes.parPair` in place of `Computes.seqPair` — no independence hypothesis is needed here,
because this is a statement about the canonical run. -/
theorem par_computes : Computes wholePar (fun _ => ()) wholePure :=
  (markStart_computes.bind (fun _ =>
    (sumInto_computes.parPair prodInto_computes).bind (fun _ => markDone_computes)))
```

# `A[i] := A[i-1] + 1` fails the check, as it must

```html
<div class="dgm col tight">
  <div class="nd mono blue">let x := a[i];  x += 1;  let y := a[i+1];  a[i+2] := x + y</div>
  <div class="arr">▼</div>
  <div class="nd">reads <code>{i, i+1}</code> &nbsp; writes <code>{i+2}</code><em><code>x += 1</code> is register work and makes no node</em></div>
  <div class="arr">▼</div>
  <div class="nd bad wide">iteration <code>i</code> writes <code>a[i+2]</code>; iterations <code>i+1</code> and <code>i+2</code> read it</div>
  <table class="dgmt">
    <tbody>
      <tr><td>indepB (body 0) (body 1) = false</td><td>distance 1</td><td><span class="vd no">REJECTED</span></td></tr>
      <tr><td>indepB (body 0) (body 2) = false</td><td>distance 2</td><td><span class="vd no">REJECTED</span></td></tr>
      <tr><td>indepB (body 0) (body 3) = true</td><td>distance 3</td><td><span class="vd ok">OK</span></td></tr>
    </tbody>
  </table>
  <div class="nd key">the dependence only reaches two iterations, so the loop runs in parallel at stride 3</div>
</div>
```

Each row is `rfl`. A theorem that accepted this loop would be worthless, so we check that it does not.

# Equivalence says nothing about being faster

```html
<div class="dgm col tight">
  <div class="nd blue wide"><code>par_seq_eq</code><em>same answer as the sequential program</em></div>
  <div class="nd bad wide">no claim about time at all<em>a correct parallel program could be slower</em></div>
  <div class="arr">▼</div>
  <div class="nd key wide">two more interpreters over the same tree</div>
</div>
```

* `work p σ` — how many memory operations run in total
* `time p σ` — how many *parallel rounds* the program needs

Work is what stays fixed; a chunked sum performs `n` additions either way. Rounds are what shrink.

```lean -stretch
example {α β : Type} (p : ParM α) (q : ParM β) (σ : State) :
    work (ParM.parPair p q) σ = work (ParM.seqPair p q) σ := work_par_eq_seq p q σ
```

:::class "gbox" "bad"
Defining `time (par p q) = max (time p) (time q) + …` makes "parallel is faster" unfold a definition
written to say so, with `Indep` nowhere in it. A cost model that cannot tell a racy fork from a safe
one is not measuring parallelism.
:::

# One round advances every ready branch

```leanLibCode Paralever.Lib.Cost (package := paralever) (startLine := 172) (endLine := 179) -stretch
def pstep {τ : Type} : ParM τ → State → Option (ParM τ × List (Loc × Val))
  | .pure _,      _ => none
  | .read l k,    σ => some (k (σ l), [])
  | .write l v k, _ => some (k (), [(l, v)])
  | .par cs k,    σ =>
      match pstepChilds cs σ with
      | some (cs', ws) => some (.par cs' k, ws)
      | none           => pstep (k (runChilds cs σ).1) σ  -- join: every child has finished
```

```leanLibCode Paralever.Lib.Cost (package := paralever) (startLine := 189) (endLine := 193) -stretch
match pstep p σ, pstepChilds ps σ with
      | some (p', wp), some (ps', wq) => some (.cons p' ps', wp ++ wq)
      | some (p', wp), none           => some (.cons p' ps,  wp)
      | none,          some (ps', wq) => some (.cons p  ps',  wq)
      | none,          none           => none
```

```lean -stretch
example {α β : Type} (p : ParM α) (q : ParM β) (σ : State)
    (hwf : WellFormed (ParM.parPair p q) σ) :
    time (ParM.parPair p q) σ = max (time p σ) (time q σ) := time_parPair_eq_max p q σ hwf

example {α β : Type} (p : ParM α) (q : ParM β) (σ : State)
    (hwf : WellFormed (ParM.parPair p q) σ) (hp : 0 < time p σ) (hq : 0 < time q σ) :
    time (ParM.parPair p q) σ < time (ParM.seqPair p q) σ := time_par_lt_seq p q σ hwf hp hq
```

Both hypotheses are load-bearing: forking against a `pure` buys nothing.

# Independence is what earns the `max`

The proof is a fuel induction with four cases at a `par` node. All the content sits in one place:

:::class "punch"
A branch's remaining rounds must come out the same whether or not the *other* branch's writes from
this same round have already landed.
:::

```html
<div class="dgm col tight">
  <div class="nd mono bad wide">racyQ writes cell 0 &nbsp;·&nbsp; racyP reads cell 0 one round later</div>
  <table class="dgmt">
    <tbody>
      <tr><th>alone</th><td><code>time racyP σz = 2</code></td><td><code>time racyQ σz = 1</code></td></tr>
      <tr><th>in parallel</th><td colspan="2"><code>3</code>, not <code>max 2 1 = 2</code><span class="vd no">max FAILS</span></td></tr>
    </tbody>
  </table>
</div>
```

`Indep` fails here, so the theorem correctly refuses to apply. Branches that conflict share no round.

# Data-dependent footprints are the boundary

:::class "steps"
* `A[B[i]]` — the address comes from a value read at runtime, so there is no static read set
* `Block` is straight-line; branches would need `footprintOf` to union both arms
* splitting *one* `Σ` across threads needs the operator to be associative
* `ParM` is inductive, so a non-terminating program cannot be written down
:::

```html
<div class="dgm col tight">
  <div class="nd bad key wide">Lean has no heap</div>
  <div class="nd wide"><code>Array.set</code> returns a <i>new</i> array<em>so a pure Lean function has no aliasing and no memory traffic to read off; the heap is something we built</em></div>
  <div class="arr lbl2">▼<small>so reading Lean's own Expr/LCNF would still need</small></div>
  <div class="dgm tight">
    <div class="nd">a layout decision<em>by hand</em></div>
    <div class="nd bad">a refinement proof<em>the array tracks the heap region across every get and set</em></div>
  </div>
</div>
```

:::class "cite"
*Lammich*, _Refinement of Parallel Algorithms down to LLVM_, *ITP 2022* — that descent needs
pointer-inequality tracking inside a refinement calculus
:::


# Next: detect the split, and take it from LLVM

```html
<div class="dgm col tight">
  <div class="dgm tight">
    <div class="nd mono">LLVM IR / MLIR<em>affine dialect, dependence analysis</em></div>
    <div class="arr lbl2">▶<small>JSON</small></div>
    <div class="nd mono blue">Block<em>loads, stores, AExp</em></div>
    <div class="arr">▶</div>
    <div class="nd key"><code>footprintOf</code> + <code>decide</code><em>a certificate per loop nest</em></div>
  </div>
  <div class="nd wide">nothing is trusted across the boundary — the JSON is a <i>proposal</i>, and a wrong one fails to typecheck</div>
</div>
```

* *detect*, not just check: report a dependence distance when refusing — `A[i+2] := A[i]+A[i+1]`
  is rejected at distance 1 and 2, accepted at 3
* *differential test* first: our verdict against LLVM's own analysis, over a corpus of loops
* *examples that stress it*: quicksort (data-dependent partition ⇒ `Logic/`), stencils,
  histogram and sparse mat-vec (`A[B[i]]`), `reduction` clauses (associativity)

:::class "cite"
Verdicts above are `rfl` in `Test/DependenceDistance.lean` · *Li, Liang, Feng*, _TASE 2024_ — a
validator generic over the instruction language · *Lammich*, _ITP 2022_ — the cost of the
refinement route instead
:::

# Summary

```html
<div class="dgm col tight">
  <div class="nd wide">O'Hearn<em>disjoint heaps cannot interfere — premises mention one thread each</em></div>
  <div class="arr">▼</div>
  <div class="nd wide">Brookes<em>a parallel trace factors into solo traces</em></div>
  <div class="arr">▼</div>
  <div class="nd blue wide"><code>wellFormed_canonical</code><em>mechanized as: only one outcome is reachable</em></div>
  <div class="arr">▼</div>
  <div class="nd key wide"><code>par_seq_eq</code><em>well-formed ⟹ parallel and sequential agree, under every schedule</em></div>
  <div class="dgm tight">
    <div class="nd">Bernstein, not <code>∗</code><em>shared reads allowed, so matmul works</em></div>
    <div class="nd"><code>par</code> is our constructor<em><code>Task</code> would make it <code>rfl</code></em></div>
    <div class="nd">races ↦ <code>wrong</code><em>step size stops mattering</em></div>
  </div>
</div>
```


:::class "finale"
paralever
:::

:::class "links"
[github.com/AnirudhG07/paralever](https://github.com/AnirudhG07/paralever)
:::

# References

:::class "refs"
* Bernstein. *Analysis of Programs for Parallel Processing.* IEEE Trans. Electronic Computers, 1966.
* Owicki & Gries. *Verifying properties of parallel programs: an axiomatic approach.* CACM, 1976.
* O'Hearn. *Resources, Concurrency and Local Reasoning.* CONCUR 2004 / TCS 375(1–3), 2007.
* Brookes. *A Semantics for Concurrent Separation Logic.* CONCUR 2004 / TCS 375(1–3), 2007.
* Apt & Olderog. *Verification of Sequential and Concurrent Programs* — disjoint parallelism.
* Vafeiadis. *Concurrent Separation Logic and Operational Semantics.* MFPS 2011. Coq: `vafeiadis/cslsound`.
* Reynolds. *Toward a Grainless Semantics for Shared-Variable Concurrency.* FSTTCS 2004.
* Bocchino, Adve et al. *A Type and Effect System for Deterministic Parallel Java.* OOPSLA 2009.
* Blom, Darabi, Huisman, Safari. *Correct Program Parallelisations.* STTT 23(5), 2021.
* Li, Liang, Feng. *Verified Validation for Affine Scheduling in Polyhedral Compilation.* TASE 2024. Coq: `verif-scop/PolCert`.
* Blelloch & Greiner. *A Provable Time and Space Efficient Implementation of NESL.* ICFP 1996.
* Niu, Sterling, Grodin, Harper. *A Cost-Aware Logical Framework* (calf). POPL 2022.
:::

`github.com/AnirudhG07/paralever`
