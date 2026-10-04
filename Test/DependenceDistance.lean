import Paralever.Core.Access

/-! Sanity: the worked translation of an imperative loop body, and the dependence it exposes.

Source (array `a` based at 0, loop variable `i`):

    let x := a[i]
    x += 1
    let y := a[i+1]
    a[i+2] := x + y

Translation: each array access becomes a node; `x += 1` becomes **no node at all** — it is ordinary
Lean computation inside the continuation. Footprint: reads `{i, i+1}`, writes `{i+2}`. -/

namespace Paralever.Test.DependenceDistance

/-- The loop body above, mechanically translated. -/
def body (i : Loc) : ParM Unit :=
  .read i (fun vx =>
    .read (i + 1) (fun vy =>
      match vx, vy with
      | .int x, .int y => .write (i + 2) (.int ((x + 1) + y)) .pure
      | _, _           => .pure ()))

def σ0 : State := fun _ => .int 0

/-- The footprint is exactly what the source reads and writes. -/
example : accesses (body 0) σ0 = ⟨[0, 1], [2]⟩ := rfl
example : accesses (body 5) σ0 = ⟨[5, 6], [7]⟩ := rfl

/-! ### The trap: this loop is **not** parallelizable in `i`

Iteration `i` writes `a[i+2]`, which iterations `i+1` and `i+2` *read*. Those are loop-carried
dependences of distance 2 and 1. The analysis finds them. -/

/-- Distance 2: iteration 0 writes `a[2]`; iteration 2 reads `a[2]`. -/
example : indepB (accesses (body 0) σ0) (accesses (body 2) σ0) = false := rfl

/-- Distance 1: iteration 0 writes `a[2]`; iteration 1 reads `a[2]`. -/
example : indepB (accesses (body 0) σ0) (accesses (body 1) σ0) = false := rfl

/-- Distance 3 and beyond is fine — the dependence has finite reach. -/
example : indepB (accesses (body 0) σ0) (accesses (body 3) σ0) = true := rfl

/-- So the *same* loop body parallelizes if iterations are strided by 3. -/
example : indepB (accesses (body 0) σ0) (accesses (body 6) σ0) = true := rfl

end Paralever.Test.DependenceDistance
