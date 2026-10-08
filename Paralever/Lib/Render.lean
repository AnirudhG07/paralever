import Paralever.Core.Access

/-! # `render` — print a `ParM` tree

`ParM`'s effect nodes carry *function* continuations, so there is no `Repr (ParM α)`: you cannot
print a function. But you can print the tree the same way `accesses` reads it — walk it against a
state, applying each continuation to the value that step would actually produce.

So `render` is simply one more interpreter over the same term, alongside `run`, `runSeq`, `accesses`
and `work`/`time`. Its recursion is `accesses`'s, with strings accumulated instead of locations.

ref: `docs/program-model.md` — the "one program, many meanings" interpreter table. -/

namespace Paralever

/-- Two spaces per level of nesting. -/
private def indent (d : Nat) : String := String.ofList (List.replicate (2 * d) ' ')

mutual

/-- The lines of `p`'s tree as seen from `σ`, one per effect node, indented by depth `d`. Reads and
writes show the values the canonical (`runSeq`) execution produces — a continuation is a function, so
there is no way to print past a `read` without a state to supply its result. A `par` prints its
children as a numbered list, each from the heap the one before it leaves, exactly as `accesses`
measures them. -/
def render {τ : Type} : ParM τ → State → Nat → List String
  | .pure _,      _, d => [indent d ++ "pure"]
  | .read l k,    σ, d =>
      (indent d ++ "read  [" ++ toString l ++ "] → " ++ toString (repr (σ l)))
        :: render (k (σ l)) σ d
  | .write l v k, σ, d =>
      (indent d ++ "write [" ++ toString l ++ "] ← " ++ toString (repr v))
        :: render (k ()) (σ.update l v) d
  | .par cs k,    σ, d =>
      let r := runChilds cs σ
      ((indent d ++ "par ⟨") :: renderChilds cs σ (d + 1) 0) ++
      ((indent d ++ "⟩") :: render (k r.1) r.2 d)

/-- The children, one labelled block each. -/
def renderChilds {αs : List Type} : Childs ParM αs → State → Nat → Nat → List String
  | .nil,       _, _, _ => []
  | .cons p ps, σ, d, i =>
      ((indent d ++ "[" ++ toString i ++ "] ∥") :: render p σ (d + 1))
        ++ renderChilds ps (runSeq p σ).2 d (i + 1)

end

/-- `render` from depth `0`, joined with newlines — the `#eval`-friendly form. -/
def renderStr {τ : Type} (p : ParM τ) (σ : State) : String :=
  "\n".intercalate (render p σ 0)

/-- `p`'s footprint from `σ` as one line of text, for printing beside a rendered tree. -/
def footprintStr {τ : Type} (p : ParM τ) (σ : State) : String :=
  let f := accesses p σ
  "reads " ++ toString f.reads ++ "   writes " ++ toString f.writes

/-
# Examples
-/

def prog₁ : ParM Unit :=
  ParM.read 0 (fun a =>
    ParM.write 1 (a + 1) (fun _ =>
      ParM.read 2 (fun b =>
        ParM.write 3 (b + 1) (fun _ =>
          ParM.pure ()))))

#eval IO.println (renderStr prog₁ (fun l => if l = 0 then 10 else 0))

end Paralever
