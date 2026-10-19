import MLIR.Ast

/-! # Evaluating affine maps

An `affine.load` carries a map and a list of index operands; the map applied to those indices is the
subscript. Because `MLIR/Lower.lean` unrolls every loop, the indices are *constants* at lowering
time, so this evaluation turns a map into a literal subscript — which is what keeps
`ParProg.footprintExact` true and makes the footprint proportional to the accesses rather than to
the array. -- ref: `docs/mlir.md` § An affine map is a footprint function

Division is MLIR's, not Lean's: `floordiv` rounds down and `mod` is non-negative, whereas `Int./`
truncates toward zero and `Int.%` follows it. The two disagree on negative operands, which is
exactly where an unchecked `/` would put an access in the wrong cell. -/

namespace Paralever.MLIR

/-- The value of an affine expression. Out-of-range dimensions and symbols read as `0`, and
division by zero is `0`, so this is total — a malformed map gives a wrong address rather than an
exception, and `Lower` is what rejects it. -/
def AffExp.eval (dims syms : List Int) : AffExp → Int
  | .dim n      => dims.getD n 0
  | .sym n      => syms.getD n 0
  | .const k    => k
  | .add a b    => a.eval dims syms + b.eval dims syms
  | .sub a b    => a.eval dims syms - b.eval dims syms
  | .mul a b    => a.eval dims syms * b.eval dims syms
  | .floorDiv a b =>
      let d := b.eval dims syms
      if d == 0 then 0 else Int.fdiv (a.eval dims syms) d
  | .ceilDiv a b =>
      let d := b.eval dims syms
      if d == 0 then 0 else -(Int.fdiv (-(a.eval dims syms)) d)
  | .mod a b =>
      let d := b.eval dims syms
      if d == 0 then 0 else Int.emod (a.eval dims syms) d

/-- Whether an expression mentions a dimension or symbol out of the declared range — the one way a
map can be malformed that `eval`'s totality would otherwise hide. -/
def AffExp.wellScoped (nd ns : Nat) : AffExp → Bool
  | .dim n        => n < nd
  | .sym n        => n < ns
  | .const _      => true
  | .add a b      => a.wellScoped nd ns && b.wellScoped nd ns
  | .sub a b      => a.wellScoped nd ns && b.wellScoped nd ns
  | .mul a b      => a.wellScoped nd ns && b.wellScoped nd ns
  | .floorDiv a b => a.wellScoped nd ns && b.wellScoped nd ns
  | .ceilDiv a b  => a.wellScoped nd ns && b.wellScoped nd ns
  | .mod a b      => a.wellScoped nd ns && b.wellScoped nd ns

/-- Every result of the map at the given dimensions and symbols. -/
def AffMap.eval (m : AffMap) (dims syms : List Int) : List Int :=
  m.results.map (AffExp.eval dims syms)

/-- Whether every result is in scope for the map's own arity. -/
def AffMap.wellScoped (m : AffMap) : Bool :=
  m.results.all (AffExp.wellScoped m.dims m.syms)

/-- **The map applied to a flat operand list.** MLIR passes an affine op's dimension operands first
and its symbol operands after, so splitting at `m.dims` is the calling convention, not a guess.
`none` when the operand count does not match the map's arity. -/
def AffMap.apply (m : AffMap) (args : List Int) : Option (List Int) :=
  if args.length == m.dims + m.syms then
    some (m.eval (args.take m.dims) (args.drop m.dims))
  else
    none

/-- A map with no dimensions and no symbols denotes a tuple of constants — the form `affine.for`
writes its bounds in (`affine_map<() -> (0)>`). -/
def AffMap.constResults? (m : AffMap) : Option (List Int) :=
  if m.dims == 0 && m.syms == 0 then some (m.eval [] []) else none

/-- A bound given as a single constant, which is what a loop with static bounds has. -/
def AffMap.constBound? (m : AffMap) : Option Int :=
  match m.constResults? with
  | some [k] => some k
  | _        => none

/-- The identity map on `n` dimensions — what `affine.load %A[%i]` means when it carries no map. -/
def AffMap.identity (n : Nat) : AffMap :=
  ⟨(List.range n).map (fun i => "d" ++ toString i), [], (List.range n).map AffExp.dim⟩

end Paralever.MLIR
