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

/-! ## A readable rendering

The same tree as imperative code: reads bind a temporary, writes are assignments, a fork is a
`parallel` block with one labelled thread per child. Rendered *against a state*, because a
continuation is a function and there is no seeing past a `read` without supplying its value — so
each read's observed value appears as a trailing comment and the rendering doubles as a trace. -/

/-- Values without the constructor noise: `10`, `true`, `()`. -/
def showVal : Val → String
  | .int k  => toString k
  | .bool b => toString b
  | .unit   => "()"

private def pad (s : String) (w : Nat) : String :=
  if s.length ≥ w then s else s ++ String.ofList (List.replicate (w - s.length) ' ')

mutual

/-- The program as imperative code. `d` is the indentation depth and `c` the next temporary's
number; both are threaded through so that names do not restart inside a thread. -/
def code {τ : Type} : ParM τ → State → Nat → Nat → List String × Nat
  | .pure _,      _, _, c => ([], c)   -- a finished branch adds no line; the block shows the end
  | .read l k,    σ, d, c =>
      let v := σ l
      let line := indent d ++ pad ("%" ++ toString c ++ " := M[" ++ toString l ++ "]") 28
                    ++ "// reads " ++ showVal v
      let r := code (k v) σ d (c + 1)
      (line :: r.1, r.2)
  | .write l v k, σ, d, c =>
      let line := indent d ++ "M[" ++ toString l ++ "] := " ++ showVal v
      let r := code (k ()) (σ.update l v) d c
      (line :: r.1, r.2)
  | .par cs k,    σ, d, c =>
      let rc := runChilds cs σ
      let b := codeChilds cs σ (d + 1) c 0
      let r := code (k rc.1) rc.2 d b.2
      ((indent d ++ "parallel {") :: b.1 ++ (indent d ++ "}") :: r.1, r.2)

/-- One labelled block per child, each rendered from the heap the previous child left — the same
convention `accesses` and `runChilds` use. -/
def codeChilds {αs : List Type} :
    Childs ParM αs → State → Nat → Nat → Nat → List String × Nat
  | .nil,       _, _, c, _ => ([], c)
  | .cons p ps, σ, d, c, i =>
      let b := code p σ (d + 1) c
      let rest := codeChilds ps (runSeq p σ).2 d b.2 (i + 1)
      ((indent d ++ "thread " ++ toString i ++ " {") :: b.1 ++ [indent d ++ "}"] ++ rest.1, rest.2)

end

/-- `code` from depth `0`, joined with newlines — the `#eval`-friendly form. -/
def codeStr {τ : Type} (p : ParM τ) (σ : State) : String :=
  match (code p σ 0 0).1 with
  | []    => "skip"
  | lines => "\n".intercalate lines

/-- A rendering with the footprint and the two cost measures beneath it: everything one needs to see
why a fork was accepted and what it bought, in one block of text. -/
def reportStr {τ : Type} (p : ParM τ) (σ : State) : String :=
  let f := accesses p σ
  codeStr p σ ++ "\n-- reads  " ++ toString f.reads
              ++ "\n-- writes " ++ toString f.writes

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
