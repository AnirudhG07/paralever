import Lang.Core.Loop

/-! # Rolling a nest: the linear algebra both front ends share

A front end that keeps a loop *rolled* must read the subscripts symbolically: `A[i*n + j]` has to
become coefficients over the loop coordinates rather than an address per iteration. The two front
ends disagree about what a subscript looks like — `.prl` writes an `Exp`, MLIR an `AffExp` under an
`AffMap` — but they agree about everything after that, and this is that part.

The pipeline is one shape in both:

```text
subscript, per axis ──► Lin (over Int) ──► rowMajor against the shape ──► affAccess? ──► AffAccess
```

`Lin` is over `Int` because a subtraction is linear while `AffAccess`'s coefficients are `Nat`:
`A[n-1-i]` is a perfectly good affine subscript that this representation cannot hold, so it is
*refused* at the last step rather than silently wrapped. -- ref: `docs/loops.md` § Rolling

Rationale: `docs/loops.md`. -/

namespace Paralever.Lang.Roll
open Paralever Paralever.Nest

/-- A linear form over a nest's coordinates: `off + Σ coeffs[k] · cₖ`, one coefficient per level,
outermost first. Every form in one nest is built at that nest's depth, so the list lengths agree
and `zipWith` loses nothing. -/
structure Lin where
  coeffs : List Int
  off    : Int
  deriving Repr, DecidableEq, Inhabited

namespace Lin

/-- The constant `k`, at depth `d`. -/
def const (d : Nat) (k : Int) : Lin := ⟨List.replicate d 0, k⟩

/-- Coordinate `k` of `d`. Out of range is the constant `0`, so every use is total. -/
def coord (d k : Nat) : Lin := ⟨(List.range d).map (fun j => if j == k then 1 else 0), 0⟩

def add (a b : Lin) : Lin := ⟨List.zipWith (· + ·) a.coeffs b.coeffs, a.off + b.off⟩
def sub (a b : Lin) : Lin := ⟨List.zipWith (· - ·) a.coeffs b.coeffs, a.off - b.off⟩
def scale (s : Int) (a : Lin) : Lin := ⟨a.coeffs.map (s * ·), s * a.off⟩

/-- The constant this form is, when it mentions no coordinate. -/
def const? (a : Lin) : Option Int := if a.coeffs.all (· == 0) then some a.off else none

/-- A product, when one side is constant. `i * j` is not linear and has no form here. -/
def mul (a b : Lin) : Option Lin :=
  match a.const?, b.const? with
  | some k, _      => some (scale k b)
  | none,   some k => some (scale k a)
  | none,   none   => none

end Lin

/-- **The subscript, collapsed.** One `Lin` per axis against the buffer's row-major strides — the
same collapse `Layout.offsetOf` performs on a constant subscript, so a rolled access addresses the
cell the unrolled one would. -/
def rowMajor (d : Nat) (shape : List Nat) (idx : List Lin) : Lin :=
  (List.zipWith (fun s l => Lin.scale (Int.ofNat s) l) (strides shape) idx).foldl
    Lin.add (Lin.const d 0)

/-- The declared access, when every coefficient and the constant term are non-negative. A backwards
subscript is refused here, which is the one place `Lin`'s `Int` and `AffAccess`'s `Nat` meet. -/
def affAccess? (base : Loc) (size : Nat) (l : Lin) : Option AffAccess :=
  if l.off < 0 || l.coeffs.any (fun c => c < 0) then none
  else some ⟨base, size, l.coeffs.map Int.toNat, l.off.toNat⟩

/-- **Points above which a front end rolls.** Below it the unrolled path is unchanged, which is what
keeps every pinned term in `Examples/` and `Test/` the shape it already has: a rolled nest is a new
route, never a replacement. -- ref: `docs/loops.md` § Rolled is additive -/
def maxUnroll : Nat := 128

/-- One level of a perfect nest, as a front end reads it off its own syntax. -/
structure Level where
  /-- The register the level's induction variable lives in. -/
  iv   : Reg
  /-- Trip count. -/
  size : Nat
  /-- First value, and the stride between values — `0` and `1` when normalized. -/
  lo   : Int := 0
  step : Int := 1
  /-- Whether this level forks. -/
  par  : Bool
  deriving Repr, DecidableEq, Inhabited

/-- **The forked prefix**, when the levels have one: `parDepth` is a *prefix* of the nest, so a
`parfor` under a sequential `for` is not a nest this representation can hold. `none` refuses it
rather than silently sequentializing the fork. -/
def parPrefix? (ls : List Level) : Option Nat :=
  let d := (ls.takeWhile (·.par)).length
  if (ls.drop d).any (·.par) then none else some d

/-- The nest those levels and that body describe. -/
def nestOf (ls : List Level) (d : Nat) (body : List NestStmt) : LoopNest :=
  { ivs := ls.map (·.iv), sizes := ls.map (·.size), lo := ls.map (·.lo), step := ls.map (·.step)
    parDepth := d, body := body }

end Paralever.Lang.Roll
