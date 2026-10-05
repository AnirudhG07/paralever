import Paralever.Core.Access

/-! # `render` — print a `ParM` tree

`ParM`'s effect nodes carry *function* continuations, so there is no `Repr (ParM α)`: you cannot
print a function. But you can print the tree the same way `accesses` reads it — walk it against a
state, applying each continuation to the value that step would actually produce.

So `render` is simply one more interpreter over the same term, alongside `run`, `runSeq`, `accesses`
and `compile`. Its recursion is `accesses`'s, with strings accumulated instead of locations.

ref: `docs/program-model.md` — the "one program, many meanings" interpreter table. -/

namespace Paralever

/-- Two spaces per level of nesting. -/
private def indent (d : Nat) : String := String.ofList (List.replicate (2 * d) ' ')

/-- The lines of `p`'s tree as seen from `σ`, one per effect node, indented by depth `d`. Reads and
writes show the values the canonical (`runSeq`) execution produces — a continuation is a function, so
there is no way to print past a `read` without a state to supply its result. Inside a `par`, the right
branch is rendered from the heap the left branch leaves, exactly as `accesses` measures it. -/
def render {τ : Type} : ParM τ → State → Nat → List String
  | .pure _,      _, d => [indent d ++ "pure"]
  | .read l k,    σ, d =>
      (indent d ++ "read  [" ++ toString l ++ "] → " ++ toString (repr (σ l)))
        :: render (k (σ l)) σ d
  | .write l v k, σ, d =>
      (indent d ++ "write [" ++ toString l ++ "] ← " ++ toString (repr v))
        :: render (k ()) (σ.update l v) d
  | .par p q k,   σ, d =>
      let (a, σ₁) := runSeq p σ
      let (b, σ₂) := runSeq q σ₁
      ((indent d ++ "par ⟨") :: (indent (d + 1) ++ "left ∥") :: render p σ (d + 2)) ++
      ((indent (d + 1) ++ "right ∥") :: render q σ₁ (d + 2)) ++
      ((indent d ++ "⟩") :: render (k (a, b)) σ₂ d)

/-- `render` from depth `0`, joined with newlines — the `#eval`-friendly form. -/
def renderStr {τ : Type} (p : ParM τ) (σ : State) : String :=
  "\n".intercalate (render p σ 0)

/-- `p`'s footprint from `σ` as one line of text, for printing beside a rendered tree. -/
def footprintStr {τ : Type} (p : ParM τ) (σ : State) : String :=
  let f := accesses p σ
  "reads " ++ toString f.reads ++ "   writes " ++ toString f.writes

end Paralever
