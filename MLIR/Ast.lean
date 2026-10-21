/-! # MLIR generic form, as Lean data

The interface between Paralever and every language that has an MLIR front end. `Op` is the
*generic* textual form (`--mlir-print-op-generic`), which is uniform across dialects, so one reader
covers `affine`, `memref`, `arith` and `func` rather than one reader per dialect's custom assembly.

Nothing here is Paralever-specific: this is MLIR's own structure, to the depth the lowering reads
it. What the lowering does with it is `MLIR/Lower.lean`; why MLIR rather than LLVM IR is
`docs/mlir.md`. -- ref: `docs/mlir.md` § The interface -/

namespace Paralever.MLIR

/-! ## Affine maps

`affine_map<(d0, d1)[s0] -> (d0 * 32 + d1)>`. The load-bearing piece: an affine map applied to a
loop index *is* the footprint function the kernel lemmas ask for.
-- ref: `docs/mlir.md` § An affine map is a footprint function -/

/-- An affine expression over dimensions and symbols. `sub` is not one of MLIR's own constructors —
MLIR writes `d0 - 1` as `d0 + (-1)` internally — but the textual form admits `-`, so the reader
needs somewhere to put it. -/
inductive AffExp where
  | dim      : Nat → AffExp
  | sym      : Nat → AffExp
  | const    : Int → AffExp
  | add      : AffExp → AffExp → AffExp
  | sub      : AffExp → AffExp → AffExp
  | mul      : AffExp → AffExp → AffExp
  | floorDiv : AffExp → AffExp → AffExp
  | ceilDiv  : AffExp → AffExp → AffExp
  | mod      : AffExp → AffExp → AffExp
  deriving Repr, DecidableEq, Inhabited

/-- A map from `dimNames.length` dimensions and `symNames.length` symbols to `results.length`
results. The names are kept rather than counted so an expression resolves by name, not by the
convention that they are called `d0, d1, …`. -/
structure AffMap where
  dimNames : List String
  symNames : List String
  results  : List AffExp
  deriving Repr, DecidableEq, Inhabited

/-- Dimensions in the map. -/
def AffMap.dims (m : AffMap) : Nat := m.dimNames.length

/-- Symbols in the map. -/
def AffMap.syms (m : AffMap) : Nat := m.symNames.length

/-! ## Types

Read only as deep as the lowering needs: a `memref`'s shape becomes a `Buf`'s shape, and everything
else is carried through so the generic form can be printed back. -/

/-- An MLIR type. `float` is parsed and then treated as `Int`, which is a scope limit, not an
approximation of arithmetic — see `docs/mlir.md` § Values. -/
inductive MTy where
  | index  : MTy
  /-- `i1`, `i32`, `i64`. -/
  | int    : Nat → MTy
  /-- `f16`, `f32`, `f64`. -/
  | float  : Nat → MTy
  /-- `memref<10x20xi32>`: a static shape and an element type. A dynamic dimension (`?`) has no
  `Nat` to put in the shape, so the reader rejects it rather than guessing. -/
  | memref : List Nat → MTy → MTy
  /-- `tensor<6xi64>` — a static-shaped tensor. Read only because a `memref.global`'s
  `initial_value` carries its elements as one: `dense<[1, 2]> : tensor<2xi64>`. -/
  | tensor : List Nat → MTy → MTy
  /-- `(i32, index)` — a parenthesised type list. -/
  | tuple  : List MTy → MTy
  /-- `(memref<8xi32>, index) -> i32` — a function type, which is what a `func.func` carries in its
  `function_type` attribute as well as what every op's trailer is. -/
  | fn     : List MTy → List MTy → MTy
  /-- Anything the reader carried through verbatim. -/
  | other  : String → MTy
  deriving Repr, Inhabited

/-! ## Attributes -/

/-- An attribute value. -/
inductive MAttr where
  | int    : Int → MAttr
  /-- A floating-point literal, read at its written decimal value and therefore *exactly*: `4.2`
  is `21/5`. The nearest `f64` to `4.2` is a different rational, so this already differs from what
  a C program holds, by one rounding. -- ref: `docs/mlir.md` § Values -/
  | flt    : Rat → MAttr
  | str    : String → MAttr
  /-- `@A` — a symbol reference, how `memref.get_global` names its global. -/
  | sym    : String → MAttr
  | ty     : MTy → MAttr
  | affine : AffMap → MAttr
  /-- `dense<0>` (splat) or `dense<[1, 2, 3]>` (elements, row-major). -/
  | dense  : List Int → Bool → MAttr
  | arr    : List MAttr → MAttr
  | dict   : List (String × MAttr) → MAttr
  | unit   : MAttr
  /-- `array<i32: 0, 0, 0>` — a dense array attribute. Current MLIR prints `operandSegmentSizes`
  this way, so an op with variadic operand groups cannot be read without it. The element type is
  kept as written, because printing it back is what the round trip compares. -/
  | darr   : String → List Int → MAttr
  /-- `3 : index`, `dense<0> : tensor<8xi32>` — a value with its type annotation. MLIR *requires*
  the annotation on `arith.constant`, so dropping it would print files MLIR cannot read back.
  `Op.attr?` strips it, so no rule has to look through it. -/
  | ann    : MAttr → MTy → MAttr
  deriving Repr, Inhabited

/-! ## Operations

A region is single-block here. Multi-block regions exist in MLIR and carry unstructured control
flow, which `ParM` cannot represent at all (`CLAUDE.md` fact 4), so the reader rejects them at the
door instead of the lowering failing later. -/

mutual

/-- One operation in generic form:
`%0, %1 = "dialect.op"(%a, %b) ({region}) {attr = …} : (ty, ty) -> (ty, ty)`.
SSA names are stored without their `%`. -/
structure Op where
  name      : String
  results   : List String
  operands  : List String
  attrs     : List (String × MAttr)
  regions   : List Region
  operandTys : List MTy
  resultTys  : List MTy
  deriving Inhabited, Repr

/-- A single-block region: the entry block's arguments, then its operations. An `affine.for`'s
induction variable is its region's one argument. -/
structure Region where
  args : List (String × MTy)
  ops  : List Op
  deriving Inhabited, Repr

end

/-- An attribute with its type annotation removed: what a rule reads. -/
def MAttr.bare : MAttr → MAttr
  | .ann a _ => MAttr.bare a
  | a        => a

namespace Op

/-- The attribute under this key, with any type annotation stripped. -/
def attr? (o : Op) (k : String) : Option MAttr :=
  ((o.attrs.find? (fun p => p.1 == k)).map Prod.snd).map MAttr.bare

def intAttr? (o : Op) (k : String) : Option Int :=
  match o.attr? k with
  | some (.int n) => some n
  | _             => none

def strAttr? (o : Op) (k : String) : Option String :=
  match o.attr? k with
  | some (.str s) => some s
  | _             => none

def symAttr? (o : Op) (k : String) : Option String :=
  match o.attr? k with
  | some (.sym s) => some s
  | some (.str s) => some s
  | _             => none

def affineAttr? (o : Op) (k : String) : Option AffMap :=
  match o.attr? k with
  | some (.affine m) => some m
  | _                => none

def tyAttr? (o : Op) (k : String) : Option MTy :=
  match o.attr? k with
  | some (.ty t) => some t
  | _            => none

/-- An integer-array attribute, as `steps = [1, 1]` is. A bare integer reads as a one-element
array, which is how MLIR prints a single-element `steps`. -/
def intsAttr? (o : Op) (k : String) : Option (List Int) :=
  match o.attr? k with
  | some (.arr xs)   => xs.mapM fun a => match a.bare with | .int n => some n | _ => none
  | some (.darr _ es) => some es
  | some (.int n)    => some [n]
  | _                => none

/-- The op's single region, when it has exactly one. -/
def body? (o : Op) : Option Region :=
  match o.regions with
  | [r] => some r
  | _   => none

end Op

/-! ### Walking the tree

`opNames` is what a corpus report's expressiveness taxonomy is built from: the ops a benchmark
contains, so the ones no rule handles can be counted rather than discovered one at a time. -/

mutual

/-- Every op name in the tree, outermost first, with duplicates. -/
def opNames : Op → List String
  | ⟨nm, _, _, _, rs, _, _⟩ => nm :: opNamesRegions rs

def opNamesRegions : List Region → List String
  | []                => []
  | ⟨_, ops⟩ :: rs    => opNamesOps ops ++ opNamesRegions rs

def opNamesOps : List Op → List String
  | []      => []
  | o :: os => opNames o ++ opNamesOps os

end

/-- Every op name in a whole file, deduplicated. -/
def opNamesOf (ops : List Op) : List String := (opNamesOps ops).eraseDups

/-- How many operations the tree holds. -/
def opCount (ops : List Op) : Nat := (opNamesOps ops).length

end Paralever.MLIR
