import VersoSlides
import Verso.Doc.Concrete
import Paralever

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

:::class "steps"
* `k` threads of `m` steps each admit `(km)! / (m!)^k` interleavings
* the comparison relates a *nondeterministic* program to a *deterministic* one
* one theorem for all such pairs, not one proof per program
:::

:::notes
The target is a single metatheorem with a small per-program side condition. Enumerating schedules is
infeasible even for small k and m.
:::

# Non-interference makes the schedule irrelevant

```html
<div class="dgm col">
  <div class="nd blue wide">the threads do not interfere</div>
  <div class="arr">▼</div>
  <div class="nd blue wide"><i>every</i> interleaving gives the same answer as the sequential order</div>
  <div class="arr">▼</div>
  <div class="nd key wide">one proof of non-interference replaces all schedule reasoning</div>
</div>
```

The remaining work is to make "do not interfere" precise, and to prove the implication.

# Hoare triples compose sequentially, but not across a heap

`{P} C {Q}` — if `P` holds and `C` terminates, `Q` holds after.

```html
<div class="dgm">
  <div class="nd mono">{P} C₁ {R}   {R} C₂ {Q}
──────────────────────────
      {P} C₁ ; C₂ {Q}<em>sequencing composes</em></div>
  <div class="nd mono bad">{x = 5}  [p] := 7  {x = 5}<em>valid only if p does not alias x</em></div>
</div>
```

The second triple needs a side condition per pointer pair: the *frame problem*.

:::notes
Owicki–Gries handles interference by cross-checking every statement against every other — quadratic.
That cost is what separation logic removes.
:::

# Separation logic: ownership, and the footprint

:::class "steps"
* `l ↦ v` — the heap is *exactly* one cell, at `l`, holding `v` (ownership, not a fact)
* `P ∗ Q` — the heap splits into two *disjoint* parts satisfying `P` and `Q`
* `l₁ ↦ 3 ∗ l₂ ↦ 4` entails `l₁ ≠ l₂`
:::

```html
<div class="dgm">
  <div class="nd mono thm">      {P} C {Q}
─────────────────────────
   {P ∗ R} C {Q ∗ R}<em>frame rule — R is untouched</em></div>
  <div class="nd key">footprint of `C`<em>the set of locations C reads, paired with the set it writes</em></div>
</div>
```

`C` is verified against its footprint; the rest of the heap carries through unchanged.

:::class "cite"
*Reynolds*; *O'Hearn*; *Ishtiaq* — separation logic, ~2001
:::

# Theorem (O'Hearn, CONCUR 2004)

:::class "gbox" "thm"
If `C₁` satisfies `{P₁} C₁ {Q₁}` and `C₂` satisfies `{P₂} C₂ {Q₂}`, and the initial heap splits as
`P₁ ∗ P₂`, then the parallel composition `C₁ ∥ C₂` satisfies `{P₁ ∗ P₂} C₁ ∥ C₂ {Q₁ ∗ Q₂}`.
:::

```html
<div class="dgm col tight">
  <div class="nd mono">{P₁} C₁ {Q₁}       {P₂} C₂ {Q₂}
────────────────────────────────
   {P₁ ∗ P₂}  C₁ ∥ C₂  {Q₁ ∗ Q₂}</div>
  <div class="nd good wide">each premise mentions one thread — no interleaving appears in the rule</div>
</div>
```

*Ownership Hypothesis*: a component accesses only cells it owns. The `∗` forces a heap split before
the fork.

# A data race is a same-location access pair with one write

```html
<table class="dgmt">
  <tbody>
    <tr><td>write / write</td><td>final value depends on order</td><td><span class="vd no">RACE</span></td></tr>
    <tr><td>read&nbsp;&nbsp;/ write</td><td>reader sees old or new value</td><td><span class="vd no">RACE</span></td></tr>
    <tr><td>read&nbsp;&nbsp;/ read</td><td>both see the same value</td><td><span class="vd ok">FINE</span></td></tr>
  </tbody>
</table>
```

Read/read is excluded. Every independence criterion below inherits that asymmetry.

:::class "cite"
`Label.conflicts` in `Core/Semantics.lean` is this definition: same location, at least one write
:::

# Theorem (Bernstein, 1966) — and its Lean counterpart

:::class "gbox" "thm"
Two statements `S₁`, `S₂` may be executed in either order, or concurrently, with the same result
precisely when their write sets are disjoint from each other and from the other's read set. The read
sets may overlap freely.
:::

```html
<div class="dgm">
  <div class="nd mono">W(S₁) ∩ W(S₂) = ∅
W(S₁) ∩ R(S₂) = ∅
W(S₂) ∩ R(S₁) = ∅
                 ↑ no R∩R clause<em>Bernstein's three conditions</em></div>
  <div class="nd mono defbox">def Indep (f₁ f₂ : Footprint) : Prop :=
  Disjoint f₁.writes f₂.writes ∧
  Disjoint f₁.writes f₂.reads  ∧
  Disjoint f₂.writes f₁.reads<em>Core/Access.lean</em></div>
</div>
```

`Indep` is strictly weaker than `∗`-disjointness, which also forbids shared reads.

# Definition: `WellFormed` — independence at every `par` node

:::class "gbox" "thm"
A program is *well-formed* in a state when, at every `par` node occurring anywhere in it, the two
branches have independent footprints, measured against the state that node sees along the canonical
run.
:::

:::class "gbox" "defbox"
```
def WellFormed : ParM τ → State → Prop
  | .pure _,      _ => True
  | .read l k,    σ => WellFormed (k (σ l)) σ
  | .write l v k, σ => WellFormed (k ()) (σ.update l v)
  | .par p q k,   σ => Indep (accesses p σ) (accesses q σ₁)
                     ∧ WellFormed p σ ∧ WellFormed q σ₁ ∧ WellFormed (k (a,b)) σ₂
```
:::

Independence of `p` against `q` constrains nothing about `par` nodes nested inside `p`. A single
top-level check is unsound.

# Lemma (Brookes, CONCUR 2004, §5–§7)

:::class "gbox" "thm"
*Parallel Decomposition.* If a trace of `C₁ ∥ C₂` runs from a state split as `σ₁ ∗ σ₂`, and the
components' footprints stay separate, then that trace is an interleaving of a trace of `C₁` from `σ₁`
and a trace of `C₂` from `σ₂`, and the final states recombine as `σ₁' ∗ σ₂'`.
:::

```html
<div class="dgm col tight">
  <div class="nd blue">a parallel execution of <code>C₁ ∥ C₂</code></div>
  <div class="arr lbl2">▼<small>factors into</small></div>
  <div class="dgm tight">
    <div class="nd">a solo run of <code>C₁</code></div>
    <div class="nd plain">+</div>
    <div class="nd">a solo run of <code>C₂</code></div>
  </div>
  <div class="arr">▼</div>
  <div class="nd key">every interleaving agrees — the sequential order among them</div>
</div>
```

Brookes states race-freedom and soundness as the headline results.

# Deriving the equivalence from the decomposition lemma

The mechanized form of the lemma is a *uniqueness* statement: a well-formed program reaches exactly
one outcome, the canonical one.

:::class "gbox" "thm"
`wellFormed_canonical` — if `p` is well-formed in `σ`, then `p` can reach `(r, σ')` if and only if
`(r, σ') = runSeq p σ`.
:::

Apply it twice, to `parPair p q` and to `seqPair p q`, then use `runSeq (parPair p q) σ = runSeq
(seqPair p q) σ`:

```lean -stretch
theorem corollary_derivation {α β : Type} (p : ParM α) (q : ParM β) (σ : State)
    (h : WellFormed (ParM.parPair p q) σ) (r : α × β) (σ' : State) :
    Reaches (.run (ParM.parPair p q) σ) (.run (.pure r) σ')
      ↔ (r, σ') = runSeq (ParM.seqPair p q) σ := by
  rw [wellFormed_canonical _ σ r σ' h, runSeq_par_eq_seq]
```

The step is routine once uniqueness is available. It appears in neither Brookes nor Vafeiadis; both
stop at soundness.

# Theorem (this work) — and its Lean counterpart

:::class "gbox" "thm"
If `parPair p q` is well-formed in `σ`, then `parPair p q` and `seqPair p q` reach exactly the same
`(result, final-state)` pairs from `σ`, under every schedule.
:::

```lean -stretch
theorem the_metatheorem {α β : Type} (p : ParM α) (q : ParM β) (σ : State)
    (h : WellFormed (ParM.parPair p q) σ) :
    ParM.parPair p q ∥≡ ParM.seqPair p q from σ :=
  par_seq_eq p q σ h
```

`p ∥≡ q from σ` abbreviates `ParSeqEq p q σ`, which is

:::class "gbox" "defbox"
```
∀ r σ', Reaches (run p σ) (run (pure r) σ') ↔ Reaches (run q σ) (run (pure r) σ')
```
:::

# How the results connect

```html
<div class="dgm col tight">
  <div class="dgm tight">
    <div class="nd">Bernstein 1966<em>reordering criterion</em></div>
    <div class="arr">▶</div>
    <div class="nd blue"><code>Indep</code><em>on footprints</em></div>
    <div class="arr">▶</div>
    <div class="nd blue"><code>WellFormed</code><em><code>Indep</code> at every <code>par</code> node</em></div>
  </div>
  <div class="arr">▼</div>
  <div class="dgm tight">
    <div class="nd">Brookes §5–7<em>decomposition lemma</em></div>
    <div class="arr">▶</div>
    <div class="nd blue"><code>wellFormed_canonical</code><em>uniqueness of the outcome</em></div>
  </div>
  <div class="arr">▼</div>
  <div class="nd key wide"><code>par_seq_eq</code> &nbsp;·&nbsp; <code>parAll_par_seq_eq</code><em>binary, then N-ary by induction on the list</em></div>
  <div class="arr lbl2">▼<small>per program, discharge</small></div>
  <div class="nd good wide"><code>WellFormed</code> — by footprint confinement plus arithmetic</div>
</div>
```

The N-ary case is a corollary of the binary one, since `parAll` is right-nested binary `par`.

# `ParM`: a program is an inductive tree of effects

:::class "gbox" "defbox"
```
inductive ParM : Type → Type 1 where
  | pure  : α → ParM α
  | read  : Loc → (Val → ParM α) → ParM α
  | write : Loc → Val → (Unit → ParM α) → ParM α
  | par   : ParM α → ParM β → (α × β → ParM γ) → ParM γ
```
:::

Each effect node carries its continuation, so `bind` is a defined graft rather than a constructor,
and the root of the tree is always the next action.

:::class "steps"
* `par` is a constructor; its meaning is fixed by `run`, not by Lean
* no `parN` — `List (ParM α)` is an illegal nested inductive
* no loop constructor, so every value is a finite tree
:::

:::class "cite"
freer representation — *Xia et al.*, _Interaction Trees_, *POPL 2020*, without coinduction
:::

# `Task` cannot host the theorem

Lean's `Task` is a one-field structure with a real body:

```html
<div class="dgm col tight">
  <div class="nd mono bad">(Task.spawn f).get = f ()<em>holds by rfl — parallel and sequential are the same term</em></div>
  <div class="arr">▼</div>
  <div class="nd key wide">nothing to state, and no independence hypothesis to discharge</div>
</div>
```

:::class "steps"
* `Task` — compilation target only, never the object of study
* a deep syntax embedding would make Lean's binders, types and termination our problem
* a shallow `σ → Set (α × σ)` offers no structure to induct on
:::

The decomposition lemma is an induction, so the model must support one.

:::notes
Lean's effectful task API is worse: BaseIO.asTask and friends are opaque with no equations, so
proving there means axiomatising the runtime.
:::

# One tree, five interpreters

```html
<table class="dgmt">
  <thead><tr><th>Interpreter</th><th>Yields</th></tr></thead>
  <tbody>
    <tr><td>run : ParM α → State → Schedule → Option (α × State)</td><td>semantics, with interleaving</td></tr>
    <tr><td>runSeq : ParM α → State → α × State</td><td>canonical left-to-right run</td></tr>
    <tr><td>accesses : ParM α → State → Footprint</td><td>the dynamic footprint</td></tr>
    <tr><td>compile : ParM α → (Unit → α)</td><td>real Lean, with Task</td></tr>
    <tr><td>render : ParM α → State → List String</td><td>a printable tree</td></tr>
  </tbody>
</table>
```

A function-valued program admits only `run`. An inductive one admits a footprint fold, which is what
the independence hypothesis is stated against.

# `accesses` walks the tree by simulating it

```html
<div class="dgm col tight">
  <div class="nd mono blue">do let x ← read 5
   write 7 (x+1)</div>
  <table class="dgmt">
    <thead><tr><th>step</th><th>node</th><th>logged</th><th>state</th></tr></thead>
    <tbody>
      <tr><td>1</td><td>.read 5 k</td><td>read&nbsp;&nbsp;5</td><td>σ</td></tr>
      <tr><td>2</td><td>k (int 3) = .write 7 (int 4) k'</td><td>write 7</td><td>σ[7 := 4]</td></tr>
      <tr><td>3</td><td>k' () = .pure ()</td><td>—</td><td>σ[7 := 4]</td></tr>
    </tbody>
  </table>
  <div class="nd key">reads <code>{5}</code> &nbsp; writes <code>{7}</code></div>
</div>
```

A continuation is a function, so reaching the next node requires applying it to a value. Hence
`accesses` takes a `State` and threads writes through it.

# The proof of `wellFormed_canonical` has four parts

```html
<div class="dgm col tight">
  <div class="nd wide">1 &nbsp; LOCALITY<em>states agreeing outside F, program avoiding F ⟹ same result and same footprint</em></div>
  <div class="arr">▼</div>
  <div class="nd wide">2 &nbsp; JOIN-POINT DICHOTOMY<em>at every point of a run of <code>par p q k</code>: inside the node, past the join, or crashed to <code>wrong</code></em></div>
  <div class="arr">▼</div>
  <div class="nd bad wide">3 &nbsp; SINGLE-STEP INVARIANT<em>a step preserves the <code>runSeq</code> value and admits no location outside the original footprint. Both halves are proved together: the hard case consumes its own conclusion one level down.</em></div>
  <div class="arr">▼</div>
  <div class="nd wide">4 &nbsp; CHAINING<em><code>WellFormed</code> survives each step, so part 3 reapplies along the whole <code>Reaches</code> chain</em></div>
</div>
```

:::class "cite"
`Theory/WellFormedCanonical.lean` — Brookes' lemma rebuilt from a step relation, with no trace model
:::

# The hypothesis is about solo runs; the conclusion is not

:::class "steps"
* `accesses p σ` describes `p` running *alone*
* `ParSeqEq` quantifies over *interleaved* executions
* a footprint depends on values read, which inside `p ∥ q` may come from `q`
:::

:::class "gbox" "thm"
*Invariant.* At every point of the interleaved run, the heap restricted to `p`'s footprint agrees
with `p`'s solo run.
:::

When `q` steps it writes only inside `q`'s footprint, which `Indep` makes disjoint from `p`'s reads,
so `p`'s view is unchanged. `step_combined` establishes one step; `WellFormed_preserved` licenses the
next.

# Races map to an absorbing `wrong`, so grain is irrelevant

```html
<div class="dgm col tight">
  <div class="nd blue wide">racy programs step to <code>wrong</code>, which is terminal</div>
  <div class="arr">▼</div>
  <div class="nd good wide">for race-free programs, every choice of atomic grain agrees</div>
  <div class="arr">▼</div>
  <div class="nd key wide">the hypothesis <i>excludes</i> racy programs rather than assuming their behaviour</div>
</div>
```

:::class "cite"
*Reynolds*, _Toward a Grainless Semantics for Shared-Variable Concurrency_, *FSTTCS 2004*
:::

# Related work

```html
<table class="dgmt">
  <thead><tr><th>Work</th><th>Contributes</th><th>Restriction</th></tr></thead>
  <tbody>
    <tr><td>Brookes, CONCUR'04</td><td>the decomposition lemma, in a trace model</td><td>stops at race-freedom and soundness</td></tr>
    <tr><td>Vafeiadis, MFPS'11</td><td>soundness in Coq, operational, no traces</td><td>safety-by-fuel; no equivalence corollary</td></tr>
    <tr><td>Apt &amp; Olderog</td><td>cleanest statement of disjoint parallelism</td><td>textbook, pre-separation-logic, unmechanized</td></tr>
    <tr><td>DPJ, OOPSLA'09</td><td>region effects; non-interference ⟹ determinism</td><td>on paper, for a Java-like calculus</td></tr>
    <tr><td>PolCert, TASE'24</td><td>Bernstein mechanized in Coq, as a validator</td><td>affine loop nests only</td></tr>
    <tr><td>Blom et al., STTT'21</td><td>sequential correctness ⟹ parallel correctness</td><td>VerCors/Viper, not a proof assistant</td></tr>
  </tbody>
</table>
```

:::class "gap"
*paralever* — the equivalence corollary, generic over the program, mechanized in Lean 4
:::

# Three alternatives to disjointness

```html
<table class="dgmt">
  <thead><tr><th>Route</th><th>Criterion</th><th>Status here</th></tr></thead>
  <tbody>
    <tr><td>movers / reduction</td><td>commutativity: <code>R*·A·L*</code> is atomic</td><td>more general, harder soundness — fallback</td></tr>
    <tr><td>confluence (LVars)</td><td>inflationary writes, threshold reads</td><td>most Mathlib-friendly — fallback</td></tr>
    <tr><td>pure algebra</td><td>chunked reduce = fold iff associative</td><td>cannot express mutable shared state</td></tr>
  </tbody>
</table>
```

:::class "cite"
*Lipton*, 1975 · *Kuper & Newton*, LVars, 2013 · third homomorphism theorem / *SyDPaCC*
:::

# Choosing a route to discharge `WellFormed`

```html
<div class="dgm col tight">
  <div class="dgm tight">
    <div class="nd good">PURE — values only<em>values cannot alias</em>
      <div class="arr">▼</div>
      <code>parMap</code> &nbsp;<span class="vd ok">no proof</span>
    </div>
    <div class="nd blue">TOUCHES THE HEAP<em>footprint must be bounded</em></div>
  </div>
  <div class="arr">▼</div>
  <div class="fan">
    <div class="nd">nobody writes<div class="arr">▼</div><code>indep_of_no_writes</code><em>Bernstein vacuous</em></div>
    <div class="nd"><code>Out[i] = f(In[i])</code><div class="arr">▼</div><code>mapArray_par_seq_eq</code><em>1 line</em></div>
    <div class="nd"><code>Out[p] = Σ …</code><div class="arr">▼</div><code>reduceArray_par_seq_eq</code><em>3 arithmetic facts</em></div>
    <div class="nd">opaque body<div class="arr">▼</div><code>opaqueOp</code><em>declare R/W, derive footprint</em></div>
    <div class="nd">straight-line imperative<div class="arr">▼</div><code>Block</code> IR<em>footprint computed, <code>decide</code></em></div>
    <div class="nd">otherwise<div class="arr">▼</div><code>parAll_…_of_indexed_rw</code><em>supply Pr / Pw</em></div>
  </div>
</div>
```

# Pure functions carry no footprint

```lean -stretch
open Paralever.Pragma.ParMap in
theorem pure_is_free {α β : Type} (f : List α → β) (chunks : List (List α)) (σ : State) :
    parMap f chunks ∥≡ seqMap f chunks from σ :=
  parMap_par_seq_eq f chunks σ
```

:::class "steps"
* no hypothesis on `f`, on the chunking, or on `σ`
* every branch is a `.pure`, so `accesses = ⟨[], []⟩`
* `Disjoint [] _` discharges all three Bernstein conditions
:::

# Elementwise maps need two facts

`Out[i] := f (In[i])`, with `In` at `[0,n)` and `Out` at `[n,2n)`:

```lean -stretch
theorem doubling_works (n : Nat) (σ : State) (dbl : Val → Val) :
    mapArrayPar Array[0, n] Array[n, n] dbl
      ∥≡ mapArraySeq Array[0, n] Array[n, n] dbl from σ :=
  mapArray_par_seq_eq Array[0, n] Array[n, n] dbl rfl (Or.inl (by show 0 + n ≤ n; omega)) σ
```

Equal lengths, and non-overlapping regions by `omega`. Holds for every `n` and every `dbl`.

# Reductions: a pure accumulator bounds the write set to one cell

```html
<div class="dgm col tight">
  <div class="nd mono blue">dotBody (n p k : Nat) (acc : Int) : ParM Int
                        ↑ a pure Int, not a heap cell</div>
  <div class="dgm tight">
    <div class="nd bad"><code>A</code>, <code>B</code> — in the heap<em>enter the footprint</em></div>
    <div class="nd good"><code>acc</code> — pure value<em>invisible to <code>accesses</code></em></div>
  </div>
  <div class="arr">▼</div>
  <div class="nd key wide">the inner loop contributes reads only, so one reduction writes a single location</div>
</div>
```

Five hypotheses: well-formedness (`trivial`), reads-within (`grind`), no-writes (`rfl`), `dst`
injective (`omega`), `dst` outside the read region (`omega`). MatMul: 207 → 107 lines.

:::class "cite"
*Blom, Darabi, Huisman, Safari*, _Correct Program Parallelisations_, *STTT 23(5) 2021*
:::

# Opaque bodies: declare the footprint, derive it

```lean -stretch
theorem agents_independent (R₁ W₁ R₂ W₂ : List Loc)
    (bodyA bodyB : List Val → List Val) (σ : State)
    (hww : Disjoint W₁ W₂) (hwr : Disjoint W₁ R₂) (hrw : Disjoint W₂ R₁) :
    ParM.parPair (opaqueOp R₁ W₁ bodyA) (opaqueOp R₂ W₂ bodyB)
      ∥≡ ParM.seqPair (opaqueOp R₁ W₁ bodyA) (opaqueOp R₂ W₂ bodyB) from σ :=
  opaqueOp_par_seq_eq R₁ W₁ R₂ W₂ bodyA bodyB σ hww hwr hrw
```

`bodyA` and `bodyB` are universally quantified. `opaqueOp_accesses` proves reads `= R` and
writes `⊆ W`, so no annotation is trusted.

```html
<table class="dgmt">
  <thead><tr><th>Tier</th><th>Mechanism</th><th>Assumed</th></tr></thead>
  <tbody>
    <tr><td>0</td><td><code>Indep</code> as a hypothesis</td><td>nothing — a conditional</td></tr>
    <tr><td>1</td><td><code>opaqueOp R W f</code></td><td>nothing — footprint proved</td></tr>
    <tr><td>2</td><td><code>axiom</code> on the footprint</td><td>the annotation (DPJ's model)</td></tr>
  </tbody>
</table>
```

# A straight-line IR makes footprints computable

:::class "gbox" "defbox"
```
inductive AExp  | lit | reg | add | sub | mul    -- pure arithmetic, no memory operand
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

`AExp` has no memory operand, so every heap value passes through an explicit `load`, and
`footprintOf` is a fold over the instruction list. Registers never enter a footprint — the split
LLVM's `mem2reg` produces.

:::class "cite"
*Li, Liang, Feng*, *TASE 2024* — Bernstein against an IR, generic over the instruction language
:::

# Two processes over disjoint regions

`procP` over `a = [0,4)` and `b = [4,8)`; `procQ` over `c = [8,12)` and `d = [12,16)`. Each reads
back a cell it wrote, so neither is a reorderable map.

:::class "gbox"
```
def procP : Block :=
  [ .load  0 (a.loc 0),                    -- r0 := a[0]
    .load  1 (a.loc 1),                    -- r1 := a[1]
    .store   (b.loc 0) (R 0 + R 1),        -- b[0] := r0 + r1
    .load  2 (b.loc 0),                    -- r2 := b[0]
    .store   (a.loc 2) (2 * R 2),          -- a[2] := 2 * r2
    .store   (b.loc 3) (R 0 - R 1) ]       -- b[3] := r0 - r1
```
:::

```html
<div class="dgm tight">
  <div class="nd mono">footprintOf procP = ⟨[0,1,4], [4,2,7]⟩<em>by rfl</em></div>
  <div class="nd mono">indepB … = true<em>by rfl</em></div>
  <div class="nd good mono">block_par_seq_eq_of_indepB … (by decide)<em>the whole proof</em></div>
</div>
```

# `render` prints the tree the same way `accesses` reads it

```html
<div class="dgm col tight">
  <div class="nd plain"><code>par ⟨</code></div>
  <div class="dgm tight top">
    <div class="nd mono blue">read  [0] → Val.int 10
read  [1] → Val.int 3
write [4] ← Val.int 13
read  [4] → Val.int 13
write [2] ← Val.int 26
write [7] ← Val.int 7
pure<em>left ∥ · procP</em></div>
    <div class="nd mono blue">read  [9] → Val.int 2
write [14] ← Val.int 7
read  [14] → Val.int 7
read  [8] → Val.int 7
write [11] ← Val.int 0
write [12] ← Val.int 0
pure<em>right ∥ · procQ</em></div>
  </div>
  <div class="nd plain"><code>⟩</code></div>
</div>
```

`write [4] ← 13` is `a[0]+a[1]`; `read [4]` reads it back; `write [2] ← 26` is `2*b[0]`. `ParM` has
function continuations and so no `Repr` — the printer walks the tree against a state.

# The `ParM` program computes the pure specification

```lean -stretch
example {α : Type} (locs : Nat → List Loc) (f : List Val → α → α)
    (σ : State) (m : Nat) (init : α) :
    (runSeq (reduceFold (readsCombine locs f) m 0 init) σ).1
      = foldPure σ locs f m 0 init :=
  reduceFold_eq_foldPure locs f σ m 0 init
```

The user supplies `f` (what to combine) and `locs` (where to read). `readsCombine` builds the `ParM`
program; this equation certifies the translation.

# Rejected cases: the hypothesis is load-bearing

```html
<div class="dgm col tight">
  <div class="nd mono blue">let x := a[i];  x += 1;  let y := a[i+1];  a[i+2] := x + y</div>
  <div class="arr">▼</div>
  <div class="nd">reads <code>{i, i+1}</code> &nbsp; writes <code>{i+2}</code><em><code>x += 1</code> is register traffic and produces no node</em></div>
  <div class="arr">▼</div>
  <div class="nd bad wide">iteration <code>i</code> writes <code>a[i+2]</code>; iterations <code>i+1</code> and <code>i+2</code> read it<em>loop-carried dependence, distances 1 and 2</em></div>
  <table class="dgmt">
    <tbody>
      <tr><td>indepB (body 0) (body 1) = false</td><td>distance 1</td><td><span class="vd no">REJECTED</span></td></tr>
      <tr><td>indepB (body 0) (body 2) = false</td><td>distance 2</td><td><span class="vd no">REJECTED</span></td></tr>
      <tr><td>indepB (body 0) (body 3) = true</td><td>distance 3</td><td><span class="vd ok">OK</span></td></tr>
    </tbody>
  </table>
  <div class="nd key">the dependence has finite reach, so the loop parallelises at stride 3</div>
</div>
```

Each row is checked by `rfl`. `DoubleInto`'s `incFromPrev` (`A[i] := A[i-1] + 1`) fails the same way.

# Line counts

```html
<table class="dgmt">
  <thead><tr><th>Example</th><th>Before</th><th>After</th><th>Removed</th></tr></thead>
  <tbody>
    <tr><td>DoubleInto — elementwise</td><td>74</td><td><span class="win">43</span></td><td>3 lemmas and the assembly</td></tr>
    <tr><td>MatMul — shared reads</td><td>207</td><td><span class="win">107</span></td><td>two fuel inductions, 65 lines</td></tr>
    <tr><td>TwoProcesses — imperative</td><td>187</td><td><span class="win">129</span></td><td>19-line footprint chain → <code>decide</code></td></tr>
    <tr><td>SumArray, Sort, MergeSort</td><td>—</td><td><span class="win">−37</span></td><td>duplicated local lemmas</td></tr>
  </tbody>
</table>
```

Every rewritten example builds with zero `sorry`. The rendered `TwoProcesses` trees are
byte-identical before and after.

# Limits

:::class "steps"
* data-dependent footprints — `A[B[i]]` has no static read set
* `Block` is straight-line; branches need `footprintOf` to union both arms
* tree reduction over one `Σ` needs associativity of the operator
* `ParM` is inductive, so non-terminating programs are unrepresentable
:::

```html
<div class="dgm col tight">
  <div class="nd bad key wide">Lean has no heap</div>
  <div class="nd wide"><code>Array.set</code> is functional and returns a new array<em>so a pure Lean function has no aliasing and no memory traffic to extract; the heap is our construction</em></div>
  <div class="arr lbl2">▼<small>translating from Lean's own Expr/LCNF would need</small></div>
  <div class="dgm tight">
    <div class="nd">a layout choice<em>human</em></div>
    <div class="nd bad">a data-refinement proof<em>the array tracks the heap region across every get/set</em></div>
  </div>
</div>
```

:::class "cite"
*Lammich*, _Refinement of Parallel Algorithms down to LLVM_, *ITP 2022* — that descent requires
pointer-inequality tracking inside a refinement calculus
:::

# Next

:::class "steps"
* LLVM differential comparison against its own dependence analysis
* `Logic/` — a DCSL-lite logic for data-dependent footprints
* `#parallelize` elaborator over affine subscripts, reporting dependence distances
:::

# Summary

```html
<div class="dgm col tight">
  <div class="nd wide">O'Hearn CONCUR'04<em>disjoint concurrency rule — premises mention one thread each</em></div>
  <div class="arr">▼</div>
  <div class="nd wide">Brookes CONCUR'04 §5–7<em>a parallel trace factors into solo traces</em></div>
  <div class="arr">▼</div>
  <div class="nd blue wide"><code>wellFormed_canonical</code><em>mechanized as uniqueness of the outcome</em></div>
  <div class="arr">▼</div>
  <div class="nd key wide"><code>par_seq_eq</code><em><code>WellFormed</code> ⟹ parallel and sequential agree, every schedule</em></div>
  <div class="dgm tight">
    <div class="nd">Bernstein, not <code>∗</code><em>shared reads admitted</em></div>
    <div class="nd">free monad, not <code>Task</code><em><code>par</code> is our constructor</em></div>
    <div class="nd">races ↦ <code>wrong</code><em>grain-independent</em></div>
  </div>
</div>
```

# Thank you

:::class "finale"
paralever
:::

:::class "links"
[github.com/AnirudhG07/paralever](https://github.com/AnirudhG07/paralever)
:::
