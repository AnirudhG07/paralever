/-! # Scalars: `Int` for the integer types, `Rat` for the floating-point ones

MLIR's element types have to land somewhere. Integer types land in `Int`, which is exact. Floating
point lands in `Rat`, and that is not a compromise: a finite IEEE value *is* `m · 2ᵉ`, so every
`f32` and `f64` literal is a rational exactly. What `Rat` does not model is IEEE *rounding*, so the
divergence from a C run is the rounding error and nothing else.

Not `Real`: it is noncomputable, so a `Real`-valued interpreter could state a corpus gate but never
run one, and running them against the original program is the point of `MLIR/Eval.lean`.

This type is the *frontend's* value algebra, used by the reference interpreter. The lowered
`ParProg` stays over `Int`, because `footprintOf` and `indepB` never inspect a `Val` — a race
verdict is value-blind, so it is the same for a float kernel as for its integer twin.
-- ref: `docs/mlir.md` § Values -/

namespace Paralever.MLIR

/-- A value the reference interpreter computes with. `int` and `rat` are kept apart rather than
collapsed into `Rat` so that `arith.divsi` can truncate and `arith.divf` need not. -/
inductive Scalar where
  | int : Int → Scalar
  | rat : Rat → Scalar
  deriving Repr, DecidableEq, Inhabited

namespace Scalar

/-- Zero of the integers — the default for an unwritten cell, matching `State`'s `.int 0`. -/
def zero : Scalar := .int 0

/-- Every scalar as a rational: the common type a mixed operation promotes to. -/
def toRat : Scalar → Rat
  | .int n => (n : Rat)
  | .rat q => q

/-- Whether this value came from a floating-point type. -/
def isRat : Scalar → Bool
  | .int _ => false
  | .rat _ => true

/-- A rational truncated toward zero. `Int./` truncates, so this is `Int`'s own rounding applied
to `num/den`. -/
def truncQ (q : Rat) : Int := q.num / q.den

/-- The integer a scalar denotes, truncating a rational toward zero — what `arith.fptosi` does. -/
def toInt : Scalar → Int
  | .int n => n
  | .rat q => truncQ q

/-- **A rational as a `Float`, for printing and for benchmarking.** Only at the edges: comparing
against a C program's output, never inside a verdict. -/
def toFloat (s : Scalar) : Float :=
  let q := s.toRat
  q.num.toFloat / q.den.toFloat

/-- A binary operation given on both carriers. Two integers stay integral; anything else promotes,
which is C's usual-arithmetic-conversions rule restricted to the two types we have. -/
def lift2 (fi : Int → Int → Int) (fq : Rat → Rat → Rat) : Scalar → Scalar → Scalar
  | .int a, .int b => .int (fi a b)
  | a,      b      => .rat (fq a.toRat b.toRat)

def add : Scalar → Scalar → Scalar := lift2 (· + ·) (· + ·)
def sub : Scalar → Scalar → Scalar := lift2 (· - ·) (· - ·)
def mul : Scalar → Scalar → Scalar := lift2 (· * ·) (· * ·)

/-- `arith.divsi` — signed integer division, truncating, and `0` on a zero divisor. Total, the same
choice `AExp.div` makes. -/
def divInt : Scalar → Scalar → Scalar := lift2 (· / ·) (· / ·)

/-- `arith.divf` — exact division, so it promotes even when both operands are integers. Division by
zero is `0`, as `Rat`'s own division is. -/
def divRat (a b : Scalar) : Scalar := .rat (a.toRat / b.toRat)

/-- `arith.remsi` / `arith.remf` — the remainder left by truncating division, so `rem` and
`divInt` agree: `a = b * (a / b) + rem a b`. -/
def rem : Scalar → Scalar → Scalar :=
  lift2 (· % ·) (fun a b => a - b * (truncQ (a / b) : Rat))

def lt (a b : Scalar) : Bool :=
  match a, b with
  | .int x, .int y => x < y
  | _,      _      => a.toRat < b.toRat

def min (a b : Scalar) : Scalar := if lt a b then a else b
def max (a b : Scalar) : Scalar := if lt a b then b else a

/-- Printed as an integer when it is one, and as `num/den` otherwise, so a corpus report shows
exactly which cells left the integers. -/
def repr : Scalar → String
  | .int n => toString n
  | .rat q => if q.den == 1 then toString q.num else toString q.num ++ "/" ++ toString q.den

/-- Whether two scalars agree to within `tol`, for comparing a rational result against a `Float`
one a C program printed. Exact equality is the right test only when neither side rounded. -/
def closeTo (a b : Scalar) (tol : Rat) : Bool :=
  let d := a.toRat - b.toRat
  (if d < 0 then -d else d) ≤ tol

end Scalar

end Paralever.MLIR
