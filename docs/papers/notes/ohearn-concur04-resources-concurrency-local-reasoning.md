# Resources, Concurrency and Local Reasoning
Peter W. O'Hearn (Queen Mary, University of London) · CONCUR 2004 (LNCS 3170, pp49–76); **the PDF supplied is the journal version**, *Theoretical Computer Science* 375(1-3), pp271–307, May 2007 · `ohearn-concur04-resources-concurrency-local-reasoning.pdf`

> Header note: the first line of the PDF reads "Published in Theoretical Computer Science 375(1-3), pp271-307, May 2007." A footnote on p.1 says "A preliminary version of this paper appeared in the Proceedings of the 15th International Conference on Concurrency Theory (CONCUR'04), P. Gardner and N. Yoshida editors, LNCS 3170, pp49–76." Section numbers below are the **journal version's**; the CONCUR'04 version is shorter and numbered differently.

## One-line thesis
Separation logic's separating conjunction, inserted into Hoare's TTPP / Owicki–Gries proof rules for conditional critical regions, yields a modular proof system in which each process reasons only about the state it owns, and in which ownership of heap cells can *transfer* dynamically between processes and resources.

## The setting

**Language** (§4). A while-language with a heap, restricted for presentation to programs of the shape

```text
init;
resource r1(variable list), ..., rm(variable list)
C1 ‖ · · · ‖ Cn
```

i.e. a single resource declaration, possibly prefixed by assignments, and a single top-level parallel composition. O'Hearn explicitly says nesting is possible but omitted: "It is possible to consider nested resource declarations and parallel compositions, but the basic case will allow us to describe variable side conditions briefly in an old-fashioned, wordy, style" (§4).

Sequential processes:

```text
C ::= x := E | x := [E] | [E] := F | x := cons(E1,...,En) | dispose(E)
    | skip | C; C | if B then C else C | while B do C
    | with r when B do C endwith
```

**Memory model** (Appendix). A state is a pair (s,h), stack `S = Variables ⇀fin Ints` and heap `H = Nats ⇀fin Ints`, both finite partial functions. `h#h'` means disjoint domains; `h ∗ h'` is union of disjoint heaps.

**Concurrency / atomic grain.** Interleaving, not true concurrency: "we stress, though, that it does not indicate a commitment to true concurrency. Indeed, Brookes's formulation uses an interleaving model where 'same time' means one after the other without intervening synchronization operations" (§2.4). The grain of basic commands is deliberately left unspecified: "In the language and proof system of this paper we say nothing about the granularity of basic commands such as `x := y + x` ... and we regard them as not part of any exclusion group" (§13). Raciness is therefore **relative to the chosen mutual exclusion groups** (§13).

**Judgment form.** A Hoare triple `{P} C {Q}`, partial correctness. §12 opens: "The first, and most obvious, limitation of this work is our focus on partial correctness specifications, so our results pertain to safety but not liveness." The contextual assignment of resource invariants is left implicit in this paper; O'Hearn notes Brookes uses sequents `Γ ⊢ {P}C{Q}` with Γ mapping resource names to invariants (§5).

**Termination.** No termination restriction; `while B do C` is in the grammar and the buffer example is `while true do ... ‖ while true do ...` with postcondition `{false}` (§7.1).

## Main results, stated

This paper proves no theorem of its own — it is explicitly a fluency paper. §1: "This paper is very much about fluency with the logic – how to reason with it – rather than its metatheory." The metatheory is delegated to Brookes's companion paper [12].

The one result quoted (§11):

```text
Theorem (Brookes): the proof rules are sound if all resource invariants are precise
predicates.
```

and the informal statement of what soundness buys (§2.4):

```text
if {P}C{Q} can be proven then any execution of C starting from a state satisfying P
will not result in a race condition or an attempt to access a dangling pointer.
```

### The full rule set (verbatim)

**Disjoint concurrency** (§3) — the warm-up rule, no resources:

```text
       {P}C{Q}   {P'}C'{Q'}
    ─────────────────────────────
    {P ∗ P'} C ‖ C' {Q ∗ Q'}

where C does not modify any variables free in P', C', Q', and conversely.
```

For contrast, O'Hearn gives the original TTPP rule it replaces (§3):

```text
       {P}C{Q}   {P'}C'{Q'}
    ─────────────────────────────
    {P ∧ P'} C ‖ C' {Q ∧ Q'}

where C does not modify any variables free in P', C', Q', and conversely.
```

**Resource declaration** (§5):

```text
  {P}init{RI_r1 ∗ · · · ∗ RI_rm ∗ P'}        {P'} C1 ‖ · · · ‖ Cn {Q}
 ───────────────────────────────────────────────────────────────────────
   {P}
   init;
   resource r1(variable list), ..., rm(variable list)
   C1 ‖ · · · ‖ Cn
   {RI_r1 ∗ · · · ∗ RI_rm ∗ Q}
```

Side condition on invariants (§5): "any command `x := · · ·` changing a variable `x` which is free in `RI_ri` must occur within a critical region for `ri`." O'Hearn notes this is weaker than Owicki–Gries's (each free variable of `RI_ri` must *belong* to `ri`) and credits the weakening to Brookes. Plus: "for soundness, we require that each resource invariant is 'precise'."

**Parallel composition** (§5), N-ary:

```text
      {P1} C1 {Q1}  · · ·  {Pn} Cn {Qn}
 ──────────────────────────────────────────────────
  {P1 ∗ · · · ∗ Pn} C1 ‖ · · · ‖ Cn {Q1 ∗ · · · ∗ Qn}

where
  • no variable free in Pi or Qi is changed in Cj when j ≠ i.
```

**Critical region (CCR)** (§5):

```text
    {(P ∗ RI_r) ∧ B} C {Q ∗ RI_r}         No other process modifies
 ────────────────────────────────────      variables free in P or Q
  {P} with r when B do C endwith {Q}
```

O'Hearn glosses the side condition: "An occurrence of a `with` command will be in one of these processes `Ci`, and the condition means that there are no assignment commands `x := –` in process `Cj` for `i ≠ j`, whenever `x` is free in `P` or `Q`."

**Auxiliary variable elimination** (§5):

```text
Suppose that X is an auxiliary variable set for program prog' and that prog is obtained
from prog' by removing all commands x := · · · to variables x ∈ X. Suppose further that
no variable in X appears freely in assertions P and Q. Then

     {P}prog'{Q}
    ─────────────
     {P}prog{Q}
```

where (§5) "A set X of variables is auxiliary in a program if every occurrence of a variable x ∈ X in the program is in a command `y := · · ·` whose target y is in X."

**Frame rule** (Appendix — "Typically, the effects of these 'small' axioms can be extended using the frame rule"):

```text
      {P} C {Q}          C doesn't change
   ───────────────────    variables free in R
    {P ∗ R} C {Q ∗ R}
```

**Small axioms** (Appendix; x, m, n distinct variables):

```text
{E ↦ –} [E] := F {E ↦ F}
{E ↦ –} dispose(E) {emp}
{x = m ∧ emp} x := cons(E1,...,Ek) {x ↦ E1[m/x],...,Ek[m/x]}
{x = m ∧ emp} x := E {x = (E[m/x]) ∧ emp}
{x = m ∧ E ↦ n} x := [E] {x = n ∧ E[m/x] ↦ n}
```

**Assertion semantics** (Appendix):

```text
s,h ⊨ B        iff  [[B]]s = true
s,h ⊨ E ↦ F    iff  {[[E]]s} = dom(h) and h([[E]]s) = [[F]]s
s,h ⊨ P ⇒ Q    iff  if s,h ⊨ P then s,h ⊨ Q
s,h ⊨ ∀x.P     iff  ∀v ∈ Ints. [s | x ↦ v], h ⊨ P
s,h ⊨ emp      iff  h = [ ] is the empty heap
s,h ⊨ P ∗ Q    iff  ∃h0,h1. h0#h1, h0 ∗ h1 = h, s,h0 ⊨ P and s,h1 ⊨ Q
```

**Precision** (§11): "an assertion `P` is precise if for all states `(s,h)` there is at most one subheap `h' ⊑ h` where `s,h' ⊨ P`."

### Worked example 1: the pointer-transferring buffer (§7.1) — full derivation

Declarations and operations (§4, §7.1):

```text
full := false;
resource buf(c, full);

put(x) ≜ with buf when ¬full do  c := x; full := true   endwith
get(y) ≜ with buf when full  do  y := c; full := false  endwith
```

Program (§7.1):

```text
x := cons(a,b);   ‖   get(y);
put(x);               use(y);
                      dispose(y);
```

Resource invariant (§7.1):

```text
RI_buf :  (full ∧ c ↦ –,–) ∨ (¬full ∧ emp)
```

Step 1 — derive `{x ↦ –,–} put(x) {emp}`. Proof of the region *body*, then one application of the **critical-region rule**:

```text
{(RI_buf ∗ x ↦ –,–) ∧ ¬full}
{(¬full ∧ emp) ∗ x ↦ –,–}        -- unfold RI_buf, kill the left disjunct using ¬full
{x ↦ –,–}                        -- (¬full ∧ emp) ∗ R  ⇒  R   [consequence]
 c := x; full := true            -- assignment axioms
{full ∧ c ↦ –,–}
{RI_buf}                         -- the crucial implication: full ∧ c ↦ –,– ⇒ RI_buf
{RI_buf ∗ emp}                   -- consequence
```

Matching the region rule's premise `{(P ∗ RI_r) ∧ B} C {Q ∗ RI_r}` with `P = x ↦ –,–`, `B = ¬full`, `Q = emp`, the conclusion is `{x ↦ –,–} put(x) {emp}`.

O'Hearn stresses why the postcondition cannot be `x ↦ –,–` (§7.1): "having `x ↦ –,–` as the postcondition would be tantamount to asserting `(x ↦ –,–) ∗ (c ↦ –,–)` at the end of the body of the `with` command, and this assertion is necessarily false when `c` and `x` are equal, as they are at that point."

Step 2 — derive `{emp} get(y) {y ↦ –,–}`, same rule, mirrored:

```text
{(RI_buf ∗ emp) ∧ full}
{full ∧ c ↦ –,–}
 y := c; full := false
{y ↦ –,– ∧ ¬full}
{(¬full ∧ emp) ∗ y ↦ –,–}
{RI_buf ∗ y ↦ –,–}
```

giving `{emp} get(y) {y ↦ –,–}`.

Step 3 — apply the **parallel composition rule** (n = 2), with the sequential rules and `{y ↦ –,–} dispose(y) {emp}` (small axiom, doubled for the binary cell):

```text
         {emp ∗ emp}
{emp}                        {emp}
x := cons(a,b);     ‖        get(y);
{x ↦ –,–}                    {y ↦ –,–}
put(x);                      use(y);
{emp}                        {y ↦ –,–}
                             dispose(y)
                             {emp}
         {emp ∗ emp}
         {emp}
```

Step 4 — apply the **resource declaration rule**, whose left premise is discharged by:

```text
{emp}
full := false
{¬full ∧ emp}
{RI_buf}
{RI_buf ∗ emp ∗ emp}
```

Conclusion for the whole program `prog` (§7.1): `{emp} prog {RI_buf}`.

O'Hearn labels what this is: "we have proven a 'structural integrity' property of the code, which implies that there is no race condition, but we have not shown real correctness" (§7.1). The assertions use `–,–` and so "do not track the flow of the values a and b from the left to the right process."

**Variant proving ownership need not move** (§7.2). Same program text, different invariant `RI : (full ∧ emp) ∨ (¬full ∧ emp)` gives `{x ↦ –,–} put(x) {x ↦ –,–}` and `{emp} get(x) {emp}` — so the sender can keep the cell and `dispose(x)` itself. "We have seen that memory ownership can either transfer with a pointer's value, or stay located in the sending process, depending on what we want to prove." But it cannot go both ways: the program that disposes in both processes "cannot be verified (except with `false` as the precondition)" since "Brookes has shown that any program that gets past our proof rules is race-free, and since this program has a race, it cannot be verified."

### Worked example 2: the toy memory manager (§8)

```text
resource mm(f).
RI_mm : list f

list x ⟺ (x = nil ∧ emp) ∨ (∃y. x ↦ –, y ∗ list y)

alloc(x,a,b) ≜ with mm when true do
                  if f = nil then x := cons(a,b)
                  else x := f; f := x.2; x.1 := a; x.2 := b
dealloc(y)   ≜ with mm when true do
                  y.2 := f;
                  f := y;
```

Interface specs obtained by the region rule: `{emp} alloc(x,a,b) {x ↦ a,b}` and `{y ↦ –,–} dealloc(y) {emp}`. Body proofs (Table 5):

```text
Proof Establishing {emp}alloc(x,a,b){x ↦ a,b}:
  {emp ∗ list f}
  {list f}
   if f = nil then
      {list f ∧ f = nil}
      {f = nil ∧ emp}
      x := cons(a,b)
      {(x ↦ a,b) ∗ (f = nil ∧ emp)}
      {(x ↦ a,b) ∗ list f}
   else
      {list f ∧ f ≠ nil}
      {∃y. f ↦ –,y ∗ list y}
      x := f; f := x.2; x.1 := a; x.2 := b
      {(x ↦ a,b) ∗ list f}
  {(x ↦ a,b) ∗ list f}

Proof Establishing {y ↦ –,–}dealloc(y){emp}:
  {(y ↦ –,–) ∗ list f}
  y.2 := f;
  f := y;
  {list f}
  {emp ∗ list f}
```

Client proof by the parallel rule (§8) — the "daring but safe" program:

```text
            {emp ∗ emp}
{emp}                        {emp}
alloc(x,a,b);                alloc(y,a',b');
{x ↦ a,b}                    {y ↦ a',b'}
x.1 := 4;         ‖          y.1 := 7;
{x ↦ 4,b}                    {y ↦ 7,b'}
dealloc(x);                  dealloc(y);
{emp}                        {emp}
            {emp ∗ emp}
            {emp}
```

Note on why this is interesting (§8): "consider an execution where the left process goes first, right up to completion, before the right one begins. Then the statements mutating `x.1` and `y.1` will in fact alter the same cell, and these statements are not within critical regions. However, although there is potential aliasing between x and y, the program proof tells us that there is no possibility of racing in any execution."

### The Reynolds counterexample (§11)

With `resource r()`, `RI_r = true`, and `one ≜ 10 ↦ –`, two derivations from the same triple:

```text
            {true}skip{true}
   {(emp ∨ one) ∗ true}skip{emp ∗ true}
{emp ∨ one} with r when true do skip endwith {emp}
```

then

```text
{emp ∨ one} with r when true do skip endwith {emp}
   {emp} with r when true do skip endwith {emp}
{emp ∗ one} with r when true do skip endwith {emp ∗ one}
   {one} with r when true do skip endwith {one}
```

and

```text
{emp ∨ one} with r when true do skip endwith {emp}
  {one} with r when true do skip endwith {emp}
```

Conjoining with the (otherwise desirable) Hoare conjunction rule:

```text
{one ∧ one} with r when true do skip endwith {emp ∧ one}
    {one} with r when true do skip endwith {false}
```

"The last triple would indicate that the program diverges, where it clearly does not." Fix: require precise resource invariants. A weaker fix is explicitly refuted (§11, "False Conjecture": restricting only the region rule's *precondition* to be precise is not enough — a second two-route derivation is given).

## Proof technique
None in this paper. §1: "We refer the reader to the companion paper by Stephen Brookes for a thorough theoretical analysis [12]. Brookes gives a denotational model of the programming language with respect to which he proves soundness of the proof rules." O'Hearn describes the shape of Brookes's argument in §2.4 and §5 but does not carry it out: "The most remarkable part of Brookes's analysis is an interplay between an interleaving semantics based on traces of actions and a 'local enabling' relation that 'executes' a trace in a portion of state owned by a process. The enabling relation skips over intermediate states and works by presuming that there is no 'interference from the outside'."

He also notes the Separation Property is a **meta-property**, never an assertion in the logic (§2.4): "we will never write a formula that describes it. Rather, the proof rules are organized in a way that guarantees the property in an implicit way."

## Side condition on parallel composition

Verbatim (§5):

```text
      {P1} C1 {Q1}  · · ·  {Pn} Cn {Qn}
 ──────────────────────────────────────────────────
  {P1 ∗ · · · ∗ Pn} C1 ‖ · · · ‖ Cn {Q1 ∗ · · · ∗ Qn}

where
  • no variable free in Pi or Qi is changed in Cj when j ≠ i.
```

So: (i) a **semantic** condition on the heap, carried by `∗` in the conclusion — the preconditions must be satisfiable on *disjoint* subheaps; and (ii) a **syntactic** condition on stack variables.

**Read/read sharing: NOT allowed on the heap.** `∗` demands "strict disjointness of heap cells" (§2.4). §12 states this as a limitation: "A second limitation is that we have not allowed shared read access to heap cells. An interesting approach to this issue of passivity has recently been put forward in Boyland's work on fractional permissions [7]. Permissions have been adapted to separation logic in [5], extending the work here and leading to proofs of some concurrent programs such as readers-and-writers that are beyond the current paper."

And §2.4: "In the definitions of racy programs and the Separation Property we have not distinguished read from write access; the informal definitions could be weakened to allow two processes to read the same portion of state at the same time. In one part of Brookes's analysis (the 'global' semantics) he allows for sharing of heap cells, while in another part (the 'local' semantics) he does not."

**Fractional permissions: not used in this paper**, only cited as future/adjacent work ([7] Boyland, [5] Bornat–Calcagno–O'Hearn–Parkinson).

**Ownership transfer: yes, and it is the headline feature.** But it happens at the *critical-region* rule, not at the parallel rule. Transfer is logical, not operational (§2.3): "there is nothing operational which says that 'ownership moves'; the semaphore operations themselves do not mention 10 at all. This is the sense in which ownership is a conceptual add-on, which we put on top of the runtime model for the purposes of understanding."

For stack variables the rule is pure syntactic non-interference — and O'Hearn calls this "a continuing source of embarrassment" (§12).

## Shared state / resources

Yes. The mechanism is **resource invariants attached to named resources**, accessed through conditional critical regions, which form mutual exclusion groups (§2.2, §4). The rule:

```text
    {(P ∗ RI_r) ∧ B} C {Q ∗ RI_r}         No other process modifies
 ────────────────────────────────────      variables free in P or Q
  {P} with r when B do C endwith {Q}
```

"The idea of this rule is that when inside a critical region the code gets to see the state associated with the resource as well as that local to the process it is part of, while when outside a region command reasoning proceeds without knowledge of the resource's state" (§5).

Semaphores are encoded as CCRs (§4):

```text
P(s) = with s when s > 0 do s := s − 1 endwith
V(s) = with s when true  do s := s + 1 endwith
```

and "super-semaphores" add auxiliary assignments inside the region, later erased by the auxiliary-variable rule. **No CAS**, no ghost state in the Iris sense; auxiliary variables are the only ghost mechanism (§4, §5, §7.3). No locks beyond CCRs/semaphores.

## What it does NOT claim

- **It proves no equality or equivalence between a parallel program and a sequential one.** Nothing in the paper relates two different programs. Every judgment is a unary Hoare triple about one program. The closest the paper comes is a remark that sequential equivalences *fail* under concurrency (§2.1): "sequentially equivalent programs that can be distinguished by concurrency are `x := x + 1; x := x + 1` and `x := x + 2`. But the only way we can see their inequivalence is through interference from another process, that is, by racing." That is an observation about when sequential reasoning is *safe*, not a theorem relating `C1 ‖ C2` to `C1; C2`.
- What it proves instead (via Brookes): partial-correctness triples, plus the meta-consequence that a provable program is race-free and does not dereference dangling pointers (§2.4).
- **No metatheory of its own.** §1: "This paper is very much about fluency with the logic ... rather than its metatheory."
- **No liveness, no termination** (§12, first paragraph).
- **No shared read access to the heap** (§12, second paragraph).
- **No refinement** (§12): "it would be desirable to be able to transit between levels of abstraction ... This would mean being able to do refinement proofs that start from an abstract program and specification, rather operating exclusively on the level of the final programs. We decided to present our ideas on a particular level for the very simple reason that the right way to incorporate refinement into our logic is not clear."
- **Full functional correctness is not shown for the buffer** — only "structural integrity" (§7.1).
- The soundness result is **conditional on precision** of resource invariants (§11), and the parallel-mergesort predicates `array` and `sorted` are explicitly *not* precise (§11 Remark 3) — allowed only because mergesort uses no CCRs.
- **Not mechanized** — see below.

## Mechanized?
**No.** `NOT FOUND IN PDF` — there is no mention of any proof assistant, mechanization, or tool anywhere in the paper. All proofs are hand-written proof outlines in the paper's own notation, and the soundness theorem is attributed to Brookes's companion paper (also on paper).

## Quotable lines

- "A program is racy if two concurrent processes attempt to access the same portion of state at the same time. Otherwise the program is race-free." — §2.1
- "if {P}C{Q} can be proven then any execution of C starting from a state satisfying P will not result in a race condition or an attempt to access a dangling pointer." — §2.4 (O'Hearn summarizing Brookes)
- "Brookes's formulation uses an interleaving model where 'same time' means one after the other without intervening synchronization operations." — §2.4
- "A second limitation is that we have not allowed shared read access to heap cells." — §12
- "This paper is very much about fluency with the logic – how to reason with it – rather than its metatheory." — §1
- "In the language and proof system of this paper we say nothing about the granularity of basic commands such as x := y + x ... we regard them as not part of any exclusion group." — §13
- "we have proven a 'structural integrity' property of the code, which implies that there is no race condition, but we have not shown real correctness." — §7.1

## Relevance to a parallel-equals-sequential equivalence theorem

- CSL's parallel rule is **unary and compositional, not relational**: from `{Pi}Ci{Qi}` it concludes `{P1 ∗ ⋯ ∗ Pn} C1 ‖ ⋯ ‖ Cn {Q1 ∗ ⋯ ∗ Qn}`. It never mentions `C1; C2`. A par≡seq outcome-set equality is a judgment of different arity and cannot be read off this rule; conversely, this rule gives a *spec* for the parallel program without ever producing a sequential counterpart.
- The side condition is `∗`, i.e. **strict heap disjointness**, and §12 names shared read access as an open limitation of the paper. A Bernstein condition (`w₁∩w₂ = w₁∩r₂ = w₂∩r₁ = ∅`, reads may overlap) is strictly weaker than `∗` on the heap and is exactly what §2.4 says the informal definitions "could be weakened to" but the formalism does not do. This is the sharpest point of difference.
- O'Hearn's §2.4 observation — that `x := x+1; x := x+1` and `x := x+2` are sequentially equal but concurrently distinguishable, "and the only way we can see their inequivalence is through interference from another process, that is, by racing" — is the informal content a par≡seq theorem makes formal, and it is stated as intuition here, not proved.
- Granularity: §13 makes raciness relative to the choice of mutual exclusion groups, so CSL does *not* make the atomic grain irrelevant by itself; Reynolds's grainless semantics is cited (footnote 1, §2.1) as the route to that. A theorem whose races go to an absorbing `wrong` inherits that route rather than this one.
