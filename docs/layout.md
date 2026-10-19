# `Layout` — declare buffers, not addresses

Code: `Paralever/Lang/Layout.lean`. Used by `Examples/NeuralNet.lean` (the net's memory) and
`Examples/RaceReport.lean` §9 (named diagnostics).

## The problem

Before this, every example assigned base addresses by hand. `Examples/NeuralNet.lean` looked like
this:

```lean
abbrev X  : Nat := 0     -- input        [0, 8)
abbrev CW : Nat := 8     -- conv weights [8, 11)
abbrev C  : Nat := 20    -- conv output  [20, 26)
abbrev W2 : Nat := 40    -- dense weights 2x6, [40, 52)
```

and its initial heap like this:

```lean
def σ0 : State
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => .int 1     -- x  = all ones
  | 8 | 9 | 10                    => .int 1     -- conv weights = [1,1,1]
  | 62 => .int 30 | 63 => .int (-18)            -- targets
  | _ => .int 0
```

Three faults, and the file documents the third as having actually happened (§5):

1. The ranges in the comments are maintained by hand and can go stale.
2. The gaps (`11` to `20`, `26` to `30`) are slack left in case a shape was miscounted.
3. The heap repeats the addresses, so there are two places to keep in step — and one of them put
   the output region on top of the weight region. `wfB` caught it, but nothing had prevented it.

No numerical-computing interface works that way. You declare a buffer with a *shape* and an
initializer, the allocator places it, and you index by subscript.

## The shape of it

```text
   declarations                allocation                   uses
  ┌──────────────┐          ┌──────────────┐        ┌─────────────────────┐
  │ buf "x"  [8] │          │ x  @0  (8)   │  ───►  │ mem.at "w2" [1, 3]  │  address
  │ buf "cw" [3] │  alloc   │ cw @8  (3)   │        │ mem.state           │  heap
  │ buf "w2"[2,6]│  ─────►  │ w2 @11 (12)  │        │ mem.ref "w2"        │  ArrRef
  │      …       │          │      …       │        │ mem.show 14         │  "w2[0, 3]"
  └──────────────┘          └──────────────┘        │ mem.render σ        │  printing
    shapes, no                consecutive,          └─────────────────────┘
    addresses                 no overlap
```

`alloc` places each buffer where the previous one ended, so the layout above is 43 cells with no
gaps where the hand-written one was 72 with four.

## A shape is enough

A declaration needs nothing but a name and a shape. `init` defaults to empty and a missing cell
reads `0`, so

```lean
buf "c" [6]        -- six zero cells
buf "m" [2, 4]     -- a 2×4 of zeros
```

Four of `NeuralNet`'s nine buffers are declared that way. For the cases where zeros are not what you
want, an `Init` is a function *of the shape*, which is why `ones` needs no size:

| | |
|---|---|
| `buf "c" [6]` | zeros — the default |
| `buf "o" [2, 3] ones` | all one |
| `buf "f" [4] (full 7)` | all `7` |
| `buf "a" [6] arange` | `0, 1, 2, …` row-major |
| `buf "i" [3, 3] eye` | `1` on the diagonal |
| `buf "cw" [3] [1, 0, -1]` | explicit, row-major (a bare list coerces to `data`) |
| `buf "w" [2, 6] (rows [[1, 0, -1], [0, 1, 0]])` | explicit, by rows |

`rows` pads or truncates **each row to the shape's last dimension**, so the ragged literal above
gives two 6-wide rows rather than a flat list that shifts every row after the first:

```text
W [2, 6] @42  [1, 0, -1, 0, 0, 0]
              [0, 1, 0, 0, 0, 0]
```

Taking the shape is what makes that possible; an `Init` that only saw a length could not know where
the rows break.

## The API

| | |
|---|---|
| `buf "w2" [2, 6]` | a declaration: name, shape, and an optional initializer (see above) |
| `Layout.of bufs` | allocate, in declaration order |
| `L.at "w2" [i, j]` | the cell's address — row-major, instead of `W2 + i*6 + j` |
| `L.ref "w2"` | the buffer as an `ArrRef`, for `Theory/Intervals.lean` |
| `L.state` | the initial heap, from the declarations |
| `L.inRange "w2" idx` | whether the subscript names a cell |
| `L.nameOf l` / `L.show l` | the **reverse** map: `14 ↦ "w2[0, 3]"` |
| `L.render σ` | the heap as the buffers you declared, matrices shaped |
| `L.covers f` / `L.strayLocs f` | whether a computed footprint stays inside the declarations |
| `L.wfB` | names distinct, no buffer over-initialized |

`cells`, `strides` and `offsetOf` are written as recursions rather than folds because every lemma
below inducts on them.

## Two facts a proof wants

Naming an address is only worth it if the name carries a proof. These are the two that let a layout
feed the machinery array examples currently re-derive by hand:

```lean
theorem Layout.at_inRange (L : Layout) (h : L.inRange name idx = true) :
    (L.ref name).InRange (L.at name idx)

theorem Layout.disjoint (L : Layout) (m n : String) (h : L.disjointB m n = true) :
    ∀ l, (L.ref m).InRange l → (L.ref n).InRange l → False
```

The first is `FootprintWithin`'s hypothesis: a kernel indexing `W[i, j]` in range provably touches
only `W`'s range. It rests on `offsetOf_lt`, one induction over the shape. The second is exactly
`ArrRef.disjoint_of_range`'s hypothesis, so the last step of an array example's independence proof
becomes `by decide` on the layout:

```lean
example : ∀ l, (mem.ref "X").InRange l → (mem.ref "Y").InRange l → False :=
  mem.disjoint "X" "Y" (by decide)
```

`disjointB` is a check rather than a derivation because `Layout` is an ordinary structure — a layout
can also be written out by hand with explicit bases. For an *allocated* layout it is true by
construction, which is `alloc_pairwise`:

```lean
theorem alloc_pairwise (bs : List Buf) (start : Loc) :
    (alloc start bs).Pairwise
      (fun p q => p.base + p.toBuf.size ≤ q.base ∨ q.base + q.toBuf.size ≤ p.base)
```

one induction, with `alloc_ge` ("nothing is placed below `start`") as the cons step.

## Out-of-range subscripts are still total

`L.at "W" [2, 0]` on a `[2, 6]` buffer is an address like any other — no clamping, no error. This is
the same choice as `ArrRef.loc` and for the same reason: `State = Loc → Val` is total, so an index
out of range is an out-of-bounds *intention*, not an access (`docs/semantics.md`,
`Examples/Pointers.lean`). What the layout adds is that you can now *see* where it went:

```lean
#eval mem.show (mem.at "W" [2, 0])     -- "Y[0]"
```

which is the aliasing diagnosis from `Examples/Pointers.lean` reported directly. `inRange` and
`covers` are how you say you meant otherwise, and `covers` catches a stray pointer with **no second
thread needed** — unlike the race check, which only fires when the stray address collides.

## Why the heap is an `Array`

`Layout.state` flattens the declared contents into an `Array Val` and reads through it:

```lean
def Layout.state (L : Layout) : State :=
  let a := L.data
  fun l => a.getD l (.int 0)
```

`Examples/NeuralNet.lean` records a 40× slowdown from a heap whose reads walked a structure per
access (50 training epochs went from over 110 s to 2.7 s once reads were `O(1)`). The `let` binds
the array outside the closure, so it is built once per call to `Layout.state` — **bind it to a
`def`**; inlining `L.state` into a loop rebuilds it every iteration, which is the same mistake.

## Named diagnostics

`Search/Explain.lean` takes a `LocName := Loc → String` rather than a `Layout`, so `Search/` never
learns that layouts exist and the dependency does not invert. `rawName` is `toString`; passing
`mem.show` gives

```text
     ┌ one side   reads {}  writes {Y[0]}
     ├ the rest   reads {}  writes {Y[0]}
     └ conflict at {Y[0]}
```

where it used to say `{37}`.

## A note on the `mem` keyword

`Lang/Notation.lean` used to spell memory `mem l`, which reserved `mem` as a **global** token: while
it did, no declaration anywhere in the project could be named `mem` — including the obvious name for
a layout. Memory is now written `[l]`, which reserves nothing (`[` and `]` are tokens already) and
drops the parentheses arithmetic addresses needed:

```lean
-- before                          -- after
%0 := mem (ij.1 * n + k)           %0 := [ij.1 * n + k]
mem 2 := R 0 + R 1                 [2] := R 0 + R 1
```

This is the second time a `syntax` keyword has collided with an ordinary identifier (the first was
`r`, which broke `Test/NArySpike.lean`). Prefer tokens that already exist.
