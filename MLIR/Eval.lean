import MLIR.Lower

/-! # The reference interpreter, over ℚ

`MLIR/Lower.lean` produces a `ParProg`, which computes in `Int`. That is exactly right for the
verdict and wrong for the values of a floating-point kernel. This file is the other half: the MLIR
program evaluated directly, with `f32` and `f64` cells holding rationals, so a translation can be
checked against the program it came from rather than trusted.

Three things make it the right shape for that job.

* **Addresses come from `MLIR/Lower.lean`.** `subscript`, `addrOf` and the `Layout` are shared, so
  when the two runs disagree about a cell they disagree about a *value*; the addresses cannot drift
  apart.
* **ℚ is exact.** `arith.divf` divides rather than truncating, and a decimal literal is read at its
  written value. So on an integer program the two runs must agree cell for cell, and that agreement
  is a real test of the lowering. Where they disagree on a float program, the difference is the
  `Int` truncation `Lowered.notes` already named.
* **A `par` is evaluated in one canonical order**, and what licenses that is `par_seq_eq` itself:
  once the verdict says race-free, every schedule gives the same heap, so the reference run may
  take the sequential one. -- ref: `docs/mlir.md` § Differential execution -/

namespace Paralever.MLIR
open Paralever Paralever.Lang Paralever.Lang.ParProg

/-- A value at run time: every SSA name holds a number or a buffer. -/
inductive EVal where
  | buf : String → EVal
  | num : Scalar → EVal
  deriving Repr, Inhabited

/-- The heap as `Loc → Scalar`, plus the bindings in scope. -/
structure EState where
  heap : Loc → Scalar
  env  : List (String × EVal)

def EState.find? (s : EState) (v : String) : Option EVal :=
  (s.env.find? (fun p => p.1 == v)).map Prod.snd

def EState.bind (s : EState) (v : String) (x : EVal) : EState :=
  { s with env := (v, x) :: s.env }

def EState.get (s : EState) (v : String) : Except String EVal :=
  match s.find? v with
  | some x => .ok x
  | none   => .error s!"unbound SSA name '%{v}'"

def EState.num (s : EState) (v : String) : Except String Scalar := do
  match ← s.get v with
  | .num x  => .ok x
  | .buf nm => .error s!"'%{nm}' is a memref where a value was expected"

def EState.buf (s : EState) (v : String) : Except String String := do
  match ← s.get v with
  | .buf nm => .ok nm
  | .num _  => .error s!"'%{v}' is a value where a memref was expected"

def EState.store (s : EState) (l : Loc) (x : Scalar) : EState :=
  { s with heap := fun k => if k == l then x else s.heap k }

/-- The declared initial contents, as scalars. A cell of a floating-point buffer starts as a
rational even when its value is integral, so a report can see which cells left the integers. -/
def initialHeap (r : Lowered) : Loc → Scalar :=
  let σ := r.layout.state
  let franges := r.floatBufs.map r.layout.ref
  fun l =>
    let n : Int := match σ l with | .int k => k | _ => 0
    if franges.any (fun a => a.base ≤ l && l < a.base + a.len) then .rat (n : Rat) else .int n

/-- A constant index, for addressing. -/
def EState.constIdx (s : EState) (v : String) : Except String Int := do
  match ← s.get v with
  | .num x  => .ok x.toInt
  | .buf nm => .error s!"'%{nm}' is a memref where an index was expected"

/-- An affine access's subscript, by the same route `MLIR/Lower.lean` takes. -/
def eSubscript (s : EState) (o : Op) (m : AffMap) (idxOps : List String) :
    Except String (List Nat) := do
  let args ← idxOps.mapM s.constIdx
  match m.apply args with
  | none    => .error s!"{o.name}: index operands do not match the map's arity"
  | some rs => rs.mapM fun k =>
      if k < 0 then .error s!"{o.name}: subscript {k} is negative" else .ok k.toNat

mutual

/-- Evaluate a list of operations in order. -/
partial def evalOps (C : LCtx) : List Op → EState → Except String EState
  | [],      s => .ok s
  | o :: os, s => do evalOps C os (← evalOp C o s)

/-- A region, with its entry arguments bound. Bindings made inside do not escape. -/
partial def evalRegion (C : LCtx) (r : Region) (binds : List EVal) (s : EState) :
    Except String EState := do
  if r.args.length != binds.length then
    .error s!"region expects {r.args.length} arguments, given {binds.length}"
  let s0 := ((r.args.map Prod.fst).zip binds).foldl (fun a (v, b) => a.bind v b) s
  let s' ← evalOps C r.ops s0
  .ok { s' with env := s.env }

/-- Each point of an index box in turn. For a `par` this is the canonical schedule, which
`par_seq_eq` makes the only one worth running. -/
partial def evalPoints (C : LCtx) (r : Region) : List (List Int) → EState → Except String EState
  | [],      s => .ok s
  | p :: ps, s => do evalPoints C r ps (← evalRegion C r (p.map (fun k => EVal.num (.int k))) s)

partial def evalOp (C : LCtx) (o : Op) (s : EState) : Except String EState := do
  match o.name with
  | "builtin.module" =>
      match o.body? with
      | some r => evalOps C r.ops s
      | none   => .error "builtin.module without a single region"
  | "func.func" =>
      match o.body? with
      | some r => evalRegion C r (r.args.map (fun (nm, _) => EVal.buf nm)) s
      | none   => .error "func.func without a single region"
  | "func.return" | "affine.yield" | "memref.dealloc" | "memref.global" => .ok s
  | "memref.alloc" | "memref.alloca" =>
      match o.results with
      | [r] => .ok (s.bind r (.buf r))
      | _   => .error s!"{o.name} must have exactly one result"
  | "memref.get_global" =>
      match o.symAttr? "name", o.results with
      | some nm, [r] => .ok (s.bind r (.buf nm))
      | _, _         => .error "memref.get_global needs a 'name' attribute and one result"
  | "arith.constant" =>
      match o.attr? "value", o.results with
      | some (.int n), [r] => .ok (s.bind r (.num (.int n)))
      | some (.flt q), [r] => .ok (s.bind r (.num (.rat q)))
      | _, _               => .error "arith.constant needs a scalar 'value' and one result"
  | "affine.load" =>
      match o.operands, o.results with
      | mr :: idxOps, [res] => do
          let nm ← s.buf mr
          let idx ← eSubscript s o (accessMap o idxOps.length) idxOps
          let l ← addrOf C o nm idx
          .ok (s.bind res (.num (s.heap l)))
      | _, _ => .error "affine.load needs a memref operand and one result"
  | "affine.store" =>
      match o.operands with
      | v :: mr :: idxOps => do
          let nm ← s.buf mr
          let idx ← eSubscript s o (accessMap o idxOps.length) idxOps
          let l ← addrOf C o nm idx
          .ok (s.store l (← s.num v))
      | _ => .error "affine.store needs a value, a memref and its indices"
  | "memref.load" =>
      match o.operands, o.results with
      | mr :: idxOps, [res] => do
          let nm ← s.buf mr
          let l ← eAddr C s o nm idxOps
          .ok (s.bind res (.num (s.heap l)))
      | _, _ => .error "memref.load needs a memref operand and one result"
  | "memref.store" =>
      match o.operands with
      | v :: mr :: idxOps => do
          let nm ← s.buf mr
          let l ← eAddr C s o nm idxOps
          .ok (s.store l (← s.num v))
      | _ => .error "memref.store needs a value, a memref and its indices"
  | "affine.for" =>
      match o.body?, boundsOf o ["lowerBound", "lowerBoundMap"],
            boundsOf o ["upperBound", "upperBoundMap"] with
      | some r, some [lo], some [hi] => do
          let is ← rangeStep lo hi ((o.intAttr? "step").getD 1)
          evalPoints C r (is.map (fun i => [i])) s
      | some _, _, _ => .error "affine.for needs constant lowerBound and upperBound maps"
      | none, _, _   => .error "affine.for without a single region"
  | "affine.parallel" =>
      match o.body?, boundsOf o ["lowerBoundsMap"], boundsOf o ["upperBoundsMap"] with
      | some r, some los, some his => do
          let steps := (o.intsAttr? "steps").getD (los.map (fun _ => 1))
          let ranges ← (los.zip his).zipIdx.mapM fun ((lo, hi), k) =>
            rangeStep lo hi (steps.getD k 1)
          evalPoints C r (boxPoints ranges) s
      | some _, _, _ => .error "affine.parallel needs constant bound maps"
      | none, _, _   => .error "affine.parallel without a single region"
  | nm => evalArith nm o s

/-- The address of a possibly computed subscript. A computed index goes through `ArrRef.addr`, the
same wrapping `ParProg.loadAt` uses, so the two runs address the same cell. -/
partial def eAddr (C : LCtx) (s : EState) (o : Op) (nm : String) (idxOps : List String) :
    Except String Loc := do
  match idxOps with
  | [v] => do
      match ← s.get v with
      | .num x  => .ok ((C.L.ref nm).addr x.toInt)
      | .buf _  => .error s!"{o.name}: a memref used as an index"
  | _ => do
      let idx ← eSubscript s o (AffMap.identity idxOps.length) idxOps
      addrOf C o nm idx

/-- Pure arithmetic and the casts. `divf` is exact here, which is the whole reason this interpreter
exists. -/
partial def evalArith (nm : String) (o : Op) (s : EState) : Except String EState := do
  let res ← match o.results with
    | [r] => .ok r
    | _   => .error s!"unsupported op '{nm}'"
  let bin (f : Scalar → Scalar → Scalar) : Except String EState := do
    match o.operands with
    | [a, b] => .ok (s.bind res (.num (f (← s.num a) (← s.num b))))
    | _      => .error s!"{nm} expects two operands"
  let un (f : Scalar → Scalar) : Except String EState := do
    match o.operands with
    | [a] => .ok (s.bind res (.num (f (← s.num a))))
    | _   => .error s!"{nm} expects one operand"
  match nm with
  | "arith.addi" | "arith.addf" => bin Scalar.add
  | "arith.subi" | "arith.subf" => bin Scalar.sub
  | "arith.muli" | "arith.mulf" => bin Scalar.mul
  | "arith.divsi" | "arith.divui" => bin Scalar.divInt
  | "arith.divf"                  => bin Scalar.divRat
  | "arith.remsi" | "arith.remf"  => bin Scalar.rem
  | "arith.maxsi" | "arith.maxnumf" => bin Scalar.max
  | "arith.minsi" | "arith.minnumf" => bin Scalar.min
  | "arith.index_cast" | "arith.index_castui" | "arith.extsi" | "arith.extui" | "arith.trunci" =>
      un (fun x => .int x.toInt)
  | "arith.sitofp" | "arith.uitofp" | "arith.extf" | "arith.truncf" => un (fun x => .rat x.toRat)
  | "arith.fptosi" | "arith.fptoui" => un (fun x => .int x.toInt)
  | "affine.apply" => do
      let idx ← eSubscript s o (accessMap o o.operands.length) o.operands
      match idx with
      | [k] => .ok (s.bind res (.num (.int (k : Int))))
      | _   => .error "affine.apply must produce exactly one result"
  | _ => .error s!"unsupported op '{nm}'"

end

/-! ## Running one benchmark both ways -/

/-- **The reference run**: the MLIR program evaluated over ℚ, from the declared initial heap. -/
def Lowered.evalRef (r : Lowered) (ops : List Op) : Except String (Loc → Scalar) := do
  let f ← entryOf ops
  let s ← evalOp ⟨r.layout, r.decls⟩ f ⟨initialHeap r, []⟩
  .ok s.heap

/-- A named buffer's cells after the reference run. -/
def Lowered.refCells (r : Lowered) (ops : List Op) (name : String) :
    Except String (List Scalar) := do
  let σ ← r.evalRef ops
  let a := r.layout.ref name
  .ok ((List.range a.len).map (fun i => σ (a.base + i)))

/-- A named buffer's cells after the `ParProg` run, as scalars, so the two are comparable. -/
def Lowered.progCells (r : Lowered) (name : String) : List Scalar :=
  (r.cells name).map (fun v => match v with | .int n => .int n | _ => .int 0)

/-- **Differential execution.** `some true` when the two runs agree on this buffer; `some false`
when they disagree, which on an integer program is a lowering bug. `none` when the reference run
could not be made at all. -/
def Lowered.agreesOn (r : Lowered) (ops : List Op) (name : String) : Option Bool :=
  match r.refCells ops name with
  | .error _ => none
  | .ok cs   => some (cs == r.progCells name)

/-- Agreement on every declared buffer. -/
def Lowered.agrees (r : Lowered) (ops : List Op) : Option Bool :=
  (r.layout.bufs.map (fun p => p.name)).foldl
    (fun acc nm => match acc, r.agreesOn ops nm with
                   | some a, some b => some (a && b)
                   | _, _           => none)
    (some true)

/-- The reference run's cells, printed by buffer — what a corpus report shows beside the C
program's own output. -/
def Lowered.refReport (r : Lowered) (ops : List Op) : String :=
  match r.evalRef ops with
  | .error e => "reference run failed: " ++ e
  | .ok σ    =>
      "\n".intercalate (r.layout.bufs.map fun p =>
        p.name ++ " = [" ++ ", ".intercalate
          ((List.range p.toBuf.size).map (fun i => (σ (p.base + i)).repr)) ++ "]")

end Paralever.MLIR
