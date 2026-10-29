import MLIR.Affine
import MLIR.Scalar
import MLIR.Pretty
import Lang.Core.Exec
import Lang.Core.Layout
import Paralever.Search.RaceSearch
import Lang.Core.Roll

/-! # `Mlir.Op → Layout × ParProg`

The second stage, and the only one that is ours: `cgeist` lowers C and C++, `flang` lowers Fortran,
and the upstream SCF→Affine pass or a hand-written `.mlir` feeds the same text. So this is one
artifact rather than one front end per language. -- ref: `docs/mlir.md`

Two things make the lowering small. Loops are **unrolled** here, so every index is a literal `Nat`
by the time an address is formed, which keeps `ParProg.footprintExact` true and makes a footprint
proportional to the accesses rather than to the array. And an **affine map applied to those indices
is the subscript**, so `affine.store %v, %A[%i, %j]` with `(i, j) -> i*M + j` needs no analysis at
all — the map *is* the footprint function.

What the lowering is faithful about, and what it is not:

* **The verdict is exact.** `footprintOf` and `indepB` never inspect a `Val`, so a race verdict does
  not depend on any value this file computes. A `memref<8xf64>` occupies the same eight cells as a
  `memref<8xi32>`, and gets the same verdict.
* **Values are exact for the integer types and approximate for the floating-point ones.** `ParProg`
  computes in `Int`, so a rational coefficient `q` multiplying `e` is emitted as `(q.num · e)/q.den`
  — right magnitude, truncated. `Lowered.exactValues` records when that happened, and
  `MLIR/Eval.lean` is the exact `Rat`-valued reference.
* Values cannot change the verdict even where they are approximate, because a value reaches an
  address only through `loadAt`/`storeAt`, whose footprint is the whole array whatever the index is.

`Lower` is a Lean function rather than a script precisely so that these can become theorems: the
target is footprint preservation — every access the MLIR program performs lies inside the bound the
produced `ParProg` reports. -- ref: `docs/mlir.md` § Why in Lean -/

namespace Paralever.MLIR
open Paralever Paralever.Lang Paralever.Lang.ParProg

/-! ## Buffers

Every `memref` the program names becomes a `Buf`, and `Layout.of` places them in consecutive,
provably non-overlapping ranges (`alloc_pairwise`) — so array disjointness is discharged once by the
allocator rather than once per pair. -/

/-- A memref's shape and element type. -/
def memrefOf? : MTy → Option (List Nat × MTy)
  | .memref ds e => some (ds, e)
  | _            => none

/-- A cell of `State` holds one scalar, so a memref of vectors or of an opaque type has no shape to
place: the refusal is here rather than in the reader, which keeps such a type verbatim so the file
still parses. -- ref: `docs/mlir-pretty.md` -/
def scalarElt (what : String) : MTy → Except String MTy
  | .index   => .ok .index
  | .int w   => .ok (.int w)
  | .float w => .ok (.float w)
  | t        => .error s!"{what}: element type {renderTy t} is not a scalar, so one cell cannot \
                          hold one element"

/-- Whether an element type is floating point, which is what makes a buffer's values rational. -/
def isFloatTy : MTy → Bool
  | .float _ => true
  | _        => false

/-- A declared buffer, with the element type kept so a report can say which cells are rational. -/
structure BufDecl where
  arr : Buf
  elt : MTy

/-- Initial contents from a `memref.global`'s `initial_value`. A splat fills the buffer; an explicit
`dense<[…]>` is already row-major, which is the order `Buf.init` wants. -/
def initOf (shape : List Nat) : Option MAttr → List Int
  | some (.dense [k] true) => List.replicate (cells shape) k
  | some (.dense es false) => es
  | _                      => []

/-- The buffer an op declares, if it declares one. -/
def declOf (o : Op) : Except String (Option BufDecl) :=
  match o.name with
  | "memref.global" =>
      match o.symAttr? "sym_name", o.tyAttr? "type" with
      | some nm, some t =>
          match memrefOf? t with
          | some (ds, e) => do
              let e ← scalarElt s!"memref.global '{nm}'" e
              .ok (some ⟨⟨nm, ds, initOf ds (o.attr? "initial_value")⟩, e⟩)
          | none         => .error s!"memref.global '{nm}' has a non-memref type"
      | _, _ => .error "memref.global without sym_name and type"
  | "memref.alloc" | "memref.alloca" =>
      match o.results, o.resultTys with
      | [r], [t] =>
          match memrefOf? t with
          | some (ds, e) => do
              let e ← scalarElt s!"{o.name} '%{r}'" e
              -- `%0` is a legal SSA name and not a legal buffer name, and `to-prl` has to print
              -- something a reader takes back. -- ref: docs/mlir-pretty.md
              let nm := if (r.toList.head?).any (fun c => c.isAlpha || c == '_') then r else "v" ++ r
              .ok (some ⟨⟨nm, ds, []⟩, e⟩)
          | none         => .error s!"{o.name} result is not a memref"
      | _, _ => .error s!"{o.name} must have exactly one result and one result type"
  | _ => .ok none

mutual

/-- Buffers declared anywhere in the tree, in declaration order. A `func.func`'s memref-typed block
arguments are declarations too: they are the arrays the benchmark was handed. -/
partial def collectOp (o : Op) : Except String (List BufDecl) := do
  let here ← declOf o
  let args ←
    if o.name == "func.func" then
      match o.body? with
      | some r =>
          r.args.mapM fun (nm, t) =>
            match memrefOf? t with
            | some (ds, e) => .ok (⟨⟨nm, ds, []⟩, e⟩ : BufDecl)
            | none => .error s!"function parameter '%{nm}' has type {renderTy t}; a parameter has \
                               to be a memref with a static shape, since it is the buffer the \
                               caller handed over and it has to be placed"
      | none => .error "func.func without a single region"
    else .ok []
  let inner ← collectRegions o.regions
  .ok (here.toList ++ args ++ inner)

partial def collectRegions : List Region → Except String (List BufDecl)
  | []             => .ok []
  | ⟨_, ops⟩ :: rs => do .ok ((← collectOps ops) ++ (← collectRegions rs))

partial def collectOps : List Op → Except String (List BufDecl)
  | []      => .ok []
  | o :: os => do .ok ((← collectOp o) ++ (← collectOps os))

end

/-! ## Values at lowering time -/

/-- What an SSA name denotes while lowering. Because loops are unrolled, an index is a `num`, so an
affine map evaluates to a literal address. -/
inductive SVal where
  /-- A buffer, by its name in the `Layout`. -/
  | buf : String → SVal
  /-- A compile-time constant: a loop index, or an `arith.constant`. -/
  | num : Scalar → SVal
  /-- A run-time value, as an expression over thread-private registers. -/
  | exp : AExp → SVal
  deriving Repr, Inhabited

/-- A rational coefficient applied to an integer expression: `(q.num · e) / q.den`. Right
magnitude, truncated by `AExp.div` — the one place `ParProg` is not faithful to a float program's
values, and `Lowered.exactValues` records it. -/
def ratScale (q : Rat) (e : AExp) : AExp := .div (.mul (.lit q.num) e) (.lit q.den)

/-- A value as an `Int`-valued expression. -/
def SVal.toAExp : SVal → Except String AExp
  | .buf nm => .error s!"'%{nm}' is a memref where a value was expected"
  | .num s  => .ok (.lit s.toInt)
  | .exp e  => .ok e

/-- The constant a value denotes, when it is one — what an index operand has to be. -/
def SVal.toConst : SVal → Except String Int
  | .num s  => .ok s.toInt
  | .exp _  => .error "an index is not a compile-time constant; the loop was not unrolled"
  | .buf nm => .error s!"'%{nm}' is a memref where an index was expected"

/-! ## The lowering state -/

/-- The placed buffers, fixed before any body is lowered: addresses are absolute, so the layout
cannot be discovered as we go. -/
structure LCtx where
  L     : Layout
  decls : List BufDecl

/-- Bindings, the next free register, and what was given up along the way. -/
structure LSt where
  env     : List (String × SVal)
  nextReg : Reg
  /-- Reversed while building. -/
  notes   : List String
  /-- Whether the emitted `ParProg` reproduces the MLIR program's values. -/
  exact   : Bool
  deriving Inhabited

def LSt.find? (st : LSt) (v : String) : Option SVal := (st.env.find? (fun p => p.1 == v)).map Prod.snd
def LSt.bind (st : LSt) (v : String) (s : SVal) : LSt := { st with env := (v, s) :: st.env }
def LSt.note (st : LSt) (m : String) : LSt :=
  if st.notes.contains m then st else { st with notes := m :: st.notes }
def LSt.inexact (st : LSt) (m : String) : LSt := { st.note m with exact := false }

def LSt.get (st : LSt) (v : String) : Except String SVal :=
  match st.find? v with
  | some s => .ok s
  | none   => .error s!"unbound SSA name '%{v}'"

/-- The buffer an SSA name is bound to. -/
def LSt.buf (st : LSt) (v : String) : Except String String := do
  match ← st.get v with
  | .buf nm => .ok nm
  | _       => .error s!"'%{v}' is not a memref"

/-! ## Arithmetic

Two constants fold; anything else becomes an `AExp`. The float cases are where `Int` stops being
faithful, and each marks the result. -/

/-- A binary `arith` op. `fq` is the exact rational meaning, used when both operands are constants;
`mk` is the `AExp` to emit otherwise. -/
def binOp (st : LSt) (nm : String) (a b : SVal)
    (fi : Int → Int → Int) (fq : Rat → Rat → Rat) (mk : AExp → AExp → AExp)
    (isFloat : Bool) : Except String (SVal × LSt) :=
  match a, b with
  | .num x, .num y =>
      let v := Scalar.lift2 fi fq x y
      .ok (.num v, if v.isRat then st.note s!"{nm}: folded over ℚ" else st)
  | _, _ => do
      -- a rational coefficient is kept as a scale rather than truncated to a literal
      match nm, a, b with
      | "arith.mulf", .num (.rat q), e
      | "arith.mulf", e, .num (.rat q) => do
          let x ← e.toAExp
          .ok (.exp (ratScale q x),
               st.inexact s!"arith.mulf: rational coefficient {q.num}/{q.den} emitted as \
                             (num·e)/den, which truncates")
      | _, _, _ => do
          let x ← a.toAExp
          let y ← b.toAExp
          .ok (.exp (mk x y),
               if isFloat then
                 st.inexact s!"{nm}: floating-point arithmetic evaluated in Int"
               else st)

/-- Two operands, resolved. -/
def two (st : LSt) (o : Op) : Except String (SVal × SVal) :=
  match o.operands with
  | [a, b] => do .ok ((← st.get a), (← st.get b))
  | _      => .error s!"{o.name} expects two operands"

/-- One operand, resolved. -/
def one (st : LSt) (o : Op) : Except String SVal :=
  match o.operands with
  | [a] => st.get a
  | _   => .error s!"{o.name} expects one operand"

/-- Bind the op's single result. -/
def bindResult (o : Op) (st : LSt) (s : SVal) : Except String LSt :=
  match o.results with
  | [r] => .ok (st.bind r s)
  -- an operation whose result nobody names still happens: a load with no reader is a read, and its
  -- footprint is what the verdict is about. -- ref: `docs/mlir-pretty.md`
  | []  => .ok st
  | _   => .error s!"{o.name} must have exactly one result"

/-! ## Addresses

The subscript of an affine access is its map applied to its index operands, and the index operands
are constants because the loops are gone. -/

/-- A map's results at constant index operands, as a subscript. -/
def subscript (st : LSt) (o : Op) (m : AffMap) (idxOps : List String) :
    Except String (List Nat) := do
  if !m.wellScoped then .error s!"{o.name}: affine map mentions a dimension or symbol out of range"
  let args ← idxOps.mapM fun v => do (← st.get v).toConst
  match m.apply args with
  | none     => .error s!"{o.name}: {args.length} index operands for a map of arity \
                          {m.dims}+{m.syms}"
  | some rs  =>
      rs.mapM fun k =>
        if k < 0 then .error s!"{o.name}: subscript {k} is negative"
        else .ok k.toNat

/-- The map an affine access carries, defaulting to the identity when it carries none. -/
def accessMap (o : Op) (n : Nat) : AffMap := (o.affineAttr? "map").getD (AffMap.identity n)

/-- The address of a subscript, with the in-range check that makes it meaningful. `Layout.at` is
total, so an out-of-range subscript would otherwise silently name a cell of the next buffer. -/
def addrOf (C : LCtx) (o : Op) (nm : String) (idx : List Nat) : Except String Loc :=
  if C.L.inRange nm idx then .ok (C.L.at nm idx)
  else .error s!"{o.name}: subscript {idx} is outside buffer '{nm}'"

/-! ## Loop ranges -/

/-- `[lo, hi)` by `step`, as the indices a loop is unrolled over. -/
def rangeStep (lo hi step : Int) : Except String (List Int) :=
  if step ≤ 0 then .error s!"loop step {step} is not positive"
  else
    let n := if hi ≤ lo then 0 else ((hi - lo + step - 1) / step).toNat
    .ok ((List.range n).map (fun k => lo + step * Int.ofNat k))

/-- Every point of a rectangular index box, in row-major order — one thread per point. -/
def boxPoints : List (List Int) → List (List Int)
  | []      => [[]]
  | r :: rs => r.flatMap (fun x => (boxPoints rs).map (fun p => x :: p))

/-- A loop's constant bounds, accepting either spelling MLIR uses. -/
def boundsOf (o : Op) (keys : List String) : Option (List Int) :=
  keys.foldl (fun acc k => acc.orElse (fun _ => (o.affineAttr? k).bind AffMap.constResults?)) none

/-- Whether every index operand is a compile-time constant. `none` means the subscript is computed,
which is the `loadAt`/`storeAt` case. -/
def allConst (st : LSt) : List String → Except String (Option (List Int))
  | []      => .ok (some [])
  | v :: vs => do
      match ← st.get v with
      | .num x => do
          match ← allConst st vs with
          | some ks => .ok (some (x.toInt :: ks))
          | none    => .ok none
      | _      => .ok none

/-- The index expression of a computed subscript. One dimension only: a multi-dimensional computed
subscript would need `i·stride + j` as an `AExp`, and `ArrRef.addr` takes a single index. -/
def nonAffineIndex (o : Op) (nm : String) (idxOps : List String) (st : LSt) :
    Except String AExp := do
  match idxOps with
  | [v] => (← st.get v).toAExp
  | _   => .error s!"{o.name} on '{nm}': a computed subscript is supported for \
                     one-dimensional memrefs only"

/-! ## Rolling an affine nest

`subscript` above turns a map into a *literal* because the unrolled route hands it constant
indices. A rolled nest hands it the loop coordinates instead, so the same map has to be read
symbolically — this is that reading, and `Lang/Core/Roll.lean` is the algebra it lands in.
-- ref: `docs/loops.md` § Rolling -/

/-- An affine expression as a linear form over the nest's coordinates, given a form per dimension
and per symbol. `floordiv`, `ceildiv`, `mod` and a product of two coordinates are not linear and
have none; each is a refusal, and the unrolled route still reads the op. -/
def linearOf (dims syms : List Roll.Lin) (d : Nat) : AffExp → Option Roll.Lin
  | .dim n   => dims[n]?
  | .sym n   => syms[n]?
  | .const k => some (Roll.Lin.const d k)
  | .add a b => do pure (Roll.Lin.add (← linearOf dims syms d a) (← linearOf dims syms d b))
  | .sub a b => do pure (Roll.Lin.sub (← linearOf dims syms d a) (← linearOf dims syms d b))
  | .mul a b => do Roll.Lin.mul (← linearOf dims syms d a) (← linearOf dims syms d b)
  | _        => none

/-- A loop's trip count, from constant bounds. `LoopNest.sizes` is `List Nat`, so a rolled nest
removes the *cost* of a large trip count and not the need for it to be a literal — the
non-constant-bound refusal stands either way. -- ref: `docs/loops.md` -/
private def tripCount (lo hi step : Int) : Option Nat :=
  if step ≤ 0 || hi ≤ lo then none else some ((hi - lo + step - 1) / step).toNat

/-- Ops that carry no statement and end a region. -/
private def stripYield (ops : List Op) : List Op :=
  ops.filter (fun o => o.name != "affine.yield" && o.name != "func.return")

/-- **The perfect nest a loop op opens**: one level per `affine.for`, one per induced dimension of
an `affine.parallel`, the SSA name of each level's induction variable, and the innermost body. -/
private partial def peelAffine (base : Reg) (k : Nat) (ops : List Op) :
    Option (List Roll.Level × List (String × Nat) × List Op) :=
  match stripYield ops with
  | [o] =>
      if o.name == "affine.for" then
        match o.body?, boundsOf o ["lowerBound", "lowerBoundMap"],
              boundsOf o ["upperBound", "upperBoundMap"] with
        | some r, some [lo], some [hi] => do
            let n ← tripCount lo hi ((o.intAttr? "step").getD 1)
            match r.args with
            | [(v, _)] => do
                let (ls, ivs, b) ← peelAffine base (k + 1) r.ops
                some (⟨base + k, n, lo, (o.intAttr? "step").getD 1, false⟩ :: ls,
                      (v, k) :: ivs, b)
            | _ => none
        | _, _, _ => none
      else if o.name == "affine.parallel" then
        match o.body?, boundsOf o ["lowerBoundsMap", "lowerBoundsGroups"],
              boundsOf o ["upperBoundsMap"] with
        | some r, some los, some his => do
            guard (los.length == his.length && r.args.length == los.length)
            let steps := (o.intsAttr? "steps").getD (los.map (fun _ => 1))
            let here ← (List.range los.length).mapM fun j => do
              let sp := steps.getD j 1
              let n ← tripCount (los.getD j 0) (his.getD j 0) sp
              some (⟨base + k + j, n, los.getD j 0, sp, true⟩ : Roll.Level)
            let names := (r.args.map Prod.fst).zipIdx.map (fun (v, j) => (v, k + j))
            let (ls, ivs, b) ← peelAffine base (k + los.length) r.ops
            some (here ++ ls, names ++ ivs, b)
        | _, _, _ => none
      else some ([], [], [o])
  | bs => some ([], [], bs)

/-- **The access an affine subscript names**, as a rolled nest declares it: the map read
symbolically over the loop coordinates, then collapsed row-major against the memref's shape. An
index operand that is neither a loop coordinate nor a constant has no form, which is the
heap-dependent subscript `wfB` refuses in any case. -/
private def affAccessOf (C : LCtx) (ivs : List (String × Nat)) (d : Nat) (st : LSt)
    (o : Op) (nm : String) (idxOps : List String) : Option Nest.AffAccess := do
  let m := accessMap o idxOps.length
  guard m.wellScoped
  guard (idxOps.length == m.dims + m.syms)
  let args ← idxOps.mapM fun v =>
    match ivs.lookup v with
    | some k => some (Roll.Lin.coord d k)
    | none   =>
        match st.find? v with
        | some (.num (.int x)) => some (Roll.Lin.const d x)
        | _                    => none
  let ls ← m.results.mapM (linearOf (args.take m.dims) (args.drop m.dims) d)
  let p ← C.L.find? nm
  guard (ls.length == p.toBuf.shape.length)
  Roll.affAccess? p.base p.toBuf.size (Roll.rowMajor d p.toBuf.shape ls)

/-! ## The pass -/

mutual

/-- Lower a list of operations in order. A run of `async.execute` ops is read as one unit, because
a fork is a group of ops rather than a single one. -/
partial def lowerOps (C : LCtx) : List Op → LSt → Except String (List ParProg × LSt)
  | [],      st => .ok ([], st)
  | o :: os, st =>
      if o.name == "async.execute" then
        lowerFork C (o :: os.takeWhile (fun q => q.name == "async.execute"))
          (os.dropWhile (fun q => q.name == "async.execute")) st
      else do
        let (p, st') ← lowerOp C o st
        let (ps, st'') ← lowerOps C os st'
        .ok (p ++ ps, st'')

/-- A maximal run of `async.execute` ops and the `async.await_all` that joins them: one `par` node.

The await must come immediately after the run and name exactly those tokens. A token awaited later
joins later than `par` does, so the shape is *required* rather than assumed — the alternative is a
`ParProg` whose threads rejoin earlier than the MLIR program's, which is a different program.
-- ref: `docs/mlir.md` § A fork is a group of ops -/
partial def lowerFork (C : LCtx) (group : List Op) (after : List Op) (st : LSt) :
    Except String (List ParProg × LSt) := do
  let toks := group.flatMap (fun g => g.results)
  if toks.length != group.length then
    .error "async.execute must have exactly one result, its token"
  if group.any (fun g => !g.operands.isEmpty) then
    .error "async.execute with operands (a dependency token or a captured value) is not supported: \
            a thread's inputs are the heap and the registers it forked with"
  let regions ← group.mapM fun g =>
    match g.body? with
    | some r => if r.args.isEmpty then .ok r
                else .error "async.execute region takes no arguments"
    | none   => .error "async.execute without a single region"
  match after with
  | []      => .error "async.execute with no async.await_all to join it"
  | j :: tl =>
      if j.name != "async.await_all" && j.name != "async.await" then
        .error s!"async.execute joined by '{j.name}': the fork must be closed by the \
                  async.await_all that immediately follows it"
      else if j.operands.length != toks.length || !toks.all (fun t => j.operands.contains t) then
        .error "async.await_all awaits other tokens than the async.execute ops before it"
      else do
        let (bs, st') ← lowerForkBodies C regions st
        let node := ParProg.par bs
        let p := match j.strAttr? "paralever.label" with
                 | some nm => ParProg.label nm node
                 | none    => node
        let (ps, st'') ← lowerOps C tl st'
        .ok (p :: ps, st'')

/-- The bodies of a fork, each on its own: an `async.execute` region takes no arguments, so the
threads differ by what they contain rather than by an index. -/
partial def lowerForkBodies (C : LCtx) : List Region → LSt →
    Except String (List ParProg × LSt)
  | [],      st => .ok ([], st)
  | r :: rs, st => do
      let (b, st') ← lowerThread C r [] st
      let (bs, st'') ← lowerForkBodies C rs st'
      .ok (b :: bs, st'')

/-- The ops of a region, with its entry-block arguments bound to `binds`. Bindings made inside do
not escape: the region's scope ends with it. -/
partial def lowerRegion (C : LCtx) (r : Region) (binds : List SVal) (st : LSt) :
    Except String (ParProg × LSt) := do
  if r.args.length != binds.length then
    .error s!"region expects {r.args.length} arguments, given {binds.length}"
  let inner := (r.args.map Prod.fst).zip binds
  let st0 := inner.foldl (fun s (v, b) => s.bind v b) st
  let (ps, st') ← lowerOps C r.ops st0
  .ok (block ps, { st' with env := st.env })

/-- One thread of a `par`: lowered on its own, because registers are thread-private and a thread's
bindings are invisible outside it. Only the notes and the exactness flag come back. -/
partial def lowerThread (C : LCtx) (r : Region) (binds : List SVal) (st : LSt) :
    Except String (ParProg × LSt) := do
  let (p, st') ← lowerRegion C r binds st
  .ok (p, { st with notes := st'.notes, exact := st.exact && st'.exact })

partial def lowerThreads (C : LCtx) (r : Region) : List (List Int) → LSt →
    Except String (List ParProg × LSt)
  | [],      st => .ok ([], st)
  | p :: ps, st => do
      let (b, st') ← lowerThread C r (p.map (fun k => SVal.num (.int k))) st
      let (bs, st'') ← lowerThreads C r ps st'
      .ok (b :: bs, st'')

/-- Unrolled iterations of a sequential loop, in order. -/
partial def lowerIters (C : LCtx) (r : Region) : List Int → LSt →
    Except String (List ParProg × LSt)
  | [],      st => .ok ([], st)
  | i :: is, st => do
      let (b, st') ← lowerRegion C r [.num (.int i)] st
      let (bs, st'') ← lowerIters C r is st'
      .ok (b :: bs, st'')

/-- **The innermost body as nest statements.** `affine.load` and `affine.store` become the nest's
accesses; every other op must be pure arithmetic, which the ordinary lowering already turns into an
`SVal` and no statement — so `arith.mulf`, the casts and `arith.constant` are reused rather than
re-read. Anything that emits a statement is a fallback. -/
partial def nestBody (C : LCtx) (ivs : List (String × Nat)) (d : Nat) :
    List Op → LSt → Option (List NestStmt × LSt)
  | [],      st => some ([], st)
  | o :: os, st =>
      if o.name == "affine.load" then
        match o.operands with
        | mr :: idxOps => do
            let nm ← (st.buf mr).toOption
            let a ← affAccessOf C ivs d st o nm idxOps
            let r := st.nextReg
            let st' ← (bindResult o { st with nextReg := r + 1 } (.exp (.reg r))).toOption
            let (ss, st'') ← nestBody C ivs d os st'
            some (.rd r a :: ss, st'')
        | [] => none
      else if o.name == "affine.store" then
        match o.operands with
        | v :: mr :: idxOps => do
            let nm ← (st.buf mr).toOption
            let a ← affAccessOf C ivs d st o nm idxOps
            let e ← ((← (st.get v).toOption).toAExp).toOption
            let (ss, st') ← nestBody C ivs d os st
            some (.wr a e :: ss, st')
        | _ => none
      else do
        let (ps, st') ← (lowerOp C o st).toOption
        guard ps.isEmpty
        nestBody C ivs d os st'

/-- **An affine nest, rolled.** `none` falls back to unrolling, which is what every nest below
`Roll.maxUnroll` points takes in any case. The induction registers are allocated first so a load
inside the body cannot collide with one. -/
partial def rollAffine (C : LCtx) (o : Op) (st : LSt) : Option (ParProg × LSt) := do
  let (levels, ivs, body) ← peelAffine st.nextReg 0 [o]
  guard (Roll.maxUnroll < Paralever.Box.prodN (levels.map (fun l => l.size)))
  let dp ← Roll.parPrefix? levels
  let st1 := ivs.foldl (fun s (v, k) => s.bind v (.exp (.reg (st.nextReg + k))))
    { st with nextReg := st.nextReg + levels.length }
  let (bs, st2) ← nestBody C ivs levels.length (stripYield body) st1
  some (.loop (Roll.nestOf levels dp bs), { st2 with env := st.env })

/-- One operation. Statements it contributes, and the state after it. -/
partial def lowerOp (C : LCtx) (o : Op) (st : LSt) : Except String (List ParProg × LSt) := do
  match o.name with
  -- structure
  | "builtin.module" =>
      match o.body? with
      | some r => lowerOps C r.ops st
      | none   => .error "builtin.module without a single region"
  | "func.func" =>
      match o.body? with
      | some r =>
          let binds := r.args.map (fun (nm, _) => SVal.buf nm)
          let inner := (r.args.map Prod.fst).zip binds
          let st0 := inner.foldl (fun s (v, b) => s.bind v b) st
          let (ps, st') ← lowerOps C r.ops st0
          .ok (ps, { st' with env := st.env })
      | none => .error "func.func without a single region"
  | "func.return" | "affine.yield" | "async.yield" | "memref.dealloc" | "memref.global" =>
      .ok ([], st)
  | "async.execute" =>
      .error "async.execute outside a block of operations: a fork is read as a group, so the \
              ops it is grouped with have to be its siblings"
  | "async.await" | "async.await_all" =>
      .error "async.await_all with no async.execute before it: the tokens it awaits were not \
              forked here"
  -- buffers
  | "memref.alloc" | "memref.alloca" =>
      match o.results with
      | [r] =>
          let nm := if (r.toList.head?).any (fun c => c.isAlpha || c == '_') then r else "v" ++ r
          .ok ([], st.bind r (.buf nm))
      | _   => .error s!"{o.name} must have exactly one result"
  | "memref.get_global" =>
      match o.symAttr? "name" with
      | some nm => do .ok ([], ← bindResult o st (.buf nm))
      | none    => .error "memref.get_global without a 'name' attribute"
  -- constants
  | "arith.constant" =>
      match o.attr? "value" with
      | some (.int n) => do .ok ([], ← bindResult o st (.num (.int n)))
      | some (.flt q) => do
          let st' ← bindResult o st (.num (.rat q))
          .ok ([], st'.note s!"arith.constant {q.num}/{q.den}: a float literal, read exactly as ℚ")
      | some a        => .error s!"arith.constant with a non-scalar value {renderAttr a}"
      | none          => .error "arith.constant without a 'value' attribute"
  -- arithmetic
  | "arith.addi" => do let (a, b) ← two st o
                       let (v, st') ← binOp st o.name a b (· + ·) (· + ·) .add false
                       .ok ([], ← bindResult o st' v)
  | "arith.subi" => do let (a, b) ← two st o
                       let (v, st') ← binOp st o.name a b (· - ·) (· - ·) .sub false
                       .ok ([], ← bindResult o st' v)
  | "arith.muli" => do let (a, b) ← two st o
                       let (v, st') ← binOp st o.name a b (· * ·) (· * ·) .mul false
                       .ok ([], ← bindResult o st' v)
  | "arith.divsi" | "arith.divui" => do
      let (a, b) ← two st o
      let (v, st') ← binOp st o.name a b (· / ·) (· / ·) .div false
      .ok ([], ← bindResult o st' v)
  | "arith.maxsi" => do let (a, b) ← two st o
                        let (v, st') ← binOp st o.name a b max max .max false
                        .ok ([], ← bindResult o st' v)
  | "arith.minsi" => do let (a, b) ← two st o
                        let (v, st') ← binOp st o.name a b min min .min false
                        .ok ([], ← bindResult o st' v)
  -- comparison: MLIR's predicate numbering, signed only. The result is `i1` and a cell holds an
  -- integer, so the `arith.extui` that follows is read as the identity cast it is.
  | "arith.cmpi" => do
      let (a, b) ← two st o
      let bi : (Int → Int → Bool) → Int → Int → Int := fun f x y => if f x y then 1 else 0
      let bq : (Rat → Rat → Bool) → Rat → Rat → Rat := fun f x y => if f x y then 1 else 0
      let (fi, fq, mk) ←
        match o.intAttr? "predicate" with
        | some 0 => .ok (bi (· == ·), bq (· == ·), (AExp.eq · ·))
        | some 1 => .ok (bi (· != ·), bq (· != ·), (AExp.ne · ·))
        | some 2 => .ok (bi (· < ·),  bq (· < ·),  (AExp.lt · ·))
        | some 3 => .ok (bi (· ≤ ·),  bq (· ≤ ·),  (AExp.le · ·))
        | some 4 => .ok (bi (· > ·),  bq (· > ·),  (AExp.gt · ·))
        | some 5 => .ok (bi (· ≥ ·),  bq (· ≥ ·),  (AExp.ge · ·))
        | some p => .error (s!"arith.cmpi: predicate {p} is unsigned, and a Paralever cell holds " ++
                            "a signed integer — only predicates 0 to 5 are read")
        | none   => .error "arith.cmpi without a 'predicate' attribute"
      let (v, st') ← binOp st o.name a b fi fq mk false
      .ok ([], ← bindResult o st' v)
  | "arith.addf" => do let (a, b) ← two st o
                       let (v, st') ← binOp st o.name a b (· + ·) (· + ·) .add true
                       .ok ([], ← bindResult o st' v)
  | "arith.subf" => do let (a, b) ← two st o
                       let (v, st') ← binOp st o.name a b (· - ·) (· - ·) .sub true
                       .ok ([], ← bindResult o st' v)
  | "arith.mulf" => do let (a, b) ← two st o
                       let (v, st') ← binOp st o.name a b (· * ·) (· * ·) .mul true
                       .ok ([], ← bindResult o st' v)
  | "arith.divf" => do let (a, b) ← two st o
                       let (v, st') ← binOp st o.name a b (· / ·) (· / ·) .div true
                       .ok ([], ← bindResult o st' v)
  | "arith.maxnumf" => do let (a, b) ← two st o
                          let (v, st') ← binOp st o.name a b max max .max true
                          .ok ([], ← bindResult o st' v)
  | "arith.minnumf" => do let (a, b) ← two st o
                          let (v, st') ← binOp st o.name a b min min .min true
                          .ok ([], ← bindResult o st' v)
  -- casts: the value is unchanged, because the only widths Paralever has are unbounded
  | "arith.index_cast" | "arith.index_castui" | "arith.extsi" | "arith.extui" | "arith.trunci"
  | "arith.sitofp" | "arith.uitofp" | "arith.extf" | "arith.truncf" => do
      .ok ([], ← bindResult o st (← one st o))
  | "arith.fptosi" | "arith.fptoui" => do
      match ← one st o with
      | .num s => do .ok ([], ← bindResult o st (.num (.int s.toInt)))
      | v      => do .ok ([], ← bindResult o st v)
  | "affine.apply" => do
      let m := accessMap o o.operands.length
      let idx ← subscript st o m o.operands
      match idx with
      | [k] => do .ok ([], ← bindResult o st (.num (.int k)))
      | _   => .error "affine.apply must produce exactly one result"
  -- memory, affine: the address is a literal
  | "affine.load" =>
      match o.operands with
      | mr :: idxOps => do
          let nm ← st.buf mr
          let idx ← subscript st o (accessMap o idxOps.length) idxOps
          let l ← addrOf C o nm idx
          let r := st.nextReg
          let st' ← bindResult o { st with nextReg := r + 1 } (.exp (.reg r))
          .ok ([.load r l], st')
      | [] => .error "affine.load without a memref operand"
  | "affine.store" =>
      match o.operands with
      | v :: mr :: idxOps => do
          let nm ← st.buf mr
          let idx ← subscript st o (accessMap o idxOps.length) idxOps
          let l ← addrOf C o nm idx
          let e ← (← st.get v).toAExp
          .ok ([.store l e], st)
      | _ => .error "affine.store needs a value, a memref and its indices"
  -- memory, non-affine: the address is computed, so the footprint is the whole array
  | "memref.load" =>
      match o.operands with
      | mr :: idxOps => do
          let nm ← st.buf mr
          match ← allConst st idxOps with
          | some _ => do
              let idx ← subscript st o (AffMap.identity idxOps.length) idxOps
              let l ← addrOf C o nm idx
              let r := st.nextReg
              let st' ← bindResult o { st with nextReg := r + 1 } (.exp (.reg r))
              .ok ([.load r l], st')
          | none => do
              let e ← nonAffineIndex o nm idxOps st
              let r := st.nextReg
              let st' ← bindResult o
                { st with nextReg := r + 1 } (.exp (.reg r))
              .ok ([.loadAt r (C.L.ref nm) e],
                   st'.note s!"memref.load on '{nm}': computed subscript, so the footprint is all \
                               of '{nm}'")
      | [] => .error "memref.load without a memref operand"
  | "memref.store" =>
      match o.operands with
      | v :: mr :: idxOps => do
          let nm ← st.buf mr
          let e ← (← st.get v).toAExp
          match ← allConst st idxOps with
          | some _ => do
              let idx ← subscript st o (AffMap.identity idxOps.length) idxOps
              let l ← addrOf C o nm idx
              .ok ([.store l e], st)
          | none => do
              let ix ← nonAffineIndex o nm idxOps st
              .ok ([.storeAt (C.L.ref nm) ix e],
                   st.note s!"memref.store on '{nm}': computed subscript, so the footprint is all \
                              of '{nm}'")
      | _ => .error "memref.store needs a value, a memref and its indices"
  -- loops
  | "affine.for" =>
      match rollAffine C o st with
      | some (p, st') => .ok ([p], st')
      | none =>
      match o.body?, boundsOf o ["lowerBound", "lowerBoundMap"],
            boundsOf o ["upperBound", "upperBoundMap"] with
      | some r, some [lo], some [hi] => do
          let step := (o.intAttr? "step").getD 1
          let is ← rangeStep lo hi step
          let (bs, st') ← lowerIters C r is st
          .ok ([block bs], st')
      | some _, _, _ => .error "affine.for needs constant lowerBound and upperBound maps"
      | none, _, _   => .error "affine.for without a single region"
  | "affine.parallel" =>
      match rollAffine C o st with
      | some (p, st') => .ok ([p], st')
      | none =>
      match o.body?, boundsOf o ["lowerBoundsMap", "lowerBoundsGroups"],
            boundsOf o ["upperBoundsMap"] with
      | some r, some los, some his => do
          if los.length != his.length then
            .error "affine.parallel: lower and upper bound maps have different arities"
          let steps := (o.intsAttr? "steps").getD (los.map (fun _ => 1))
          let ranges ← (los.zip his).zipIdx.mapM fun ((lo, hi), k) =>
            rangeStep lo hi (steps.getD k 1)
          let pts := boxPoints ranges
          let (bs, st') ← lowerThreads C r pts st
          .ok ([.par bs], st')
      | some _, _, _ => .error "affine.parallel needs constant lowerBoundsMap and upperBoundsMap"
      | none, _, _   => .error "affine.parallel without a single region"
  | nm => .error s!"unsupported op '{nm}'"

end

/-! ## The result -/

/-- A lowered benchmark: where its arrays are, what the program is, and what was given up. -/
structure Lowered where
  layout : Layout
  prog   : ParProg
  /-- Whether the `ParProg` reproduces the MLIR program's values. False as soon as floating-point
  arithmetic was evaluated in `Int`; the verdict is unaffected either way. -/
  exactValues : Bool
  /-- Every approximation made, in the order made. -/
  notes  : List String
  /-- Element types, so a report can say which buffers are rational. -/
  decls  : List BufDecl

/-- Buffers declared outside any function: the module's globals. Collected separately from the
entry function's own declarations, so that the nineteen functions a real file holds besides the one
being lowered do not place nineteen buffers. -- ref: `docs/mlir-pretty.md` § One function out of
twenty -/
partial def globalsOf : List Op → List Op
  | []      => []
  | o :: os =>
      let here :=
        if o.name == "memref.global" then [o]
        else if o.name == "builtin.module" then
          match o.regions with
          | [⟨_, inner⟩] => globalsOf inner
          | _            => []
        else []
      here ++ globalsOf os

/-- The one function to lower: the one named, the only one there is, or the one called `main`.
Refusing to guess among several is deliberate — `func.call` is not supported, so concatenating
functions would run code the program never runs. -/
def entryOf (entry : Option String) (ops : List Op) : Except String Op :=
  let fs := funcsOf ops
  let names := fs.map (fun f => (f.symAttr? "sym_name").getD "?")
  match entry with
  | some nm =>
      match fs.find? (fun f => f.symAttr? "sym_name" == some nm) with
      | some f => .ok f
      | none   => .error (s!"no function called '{nm}' in this module: "
                          ++ ", ".intercalate names)
  | none =>
      match fs with
      | [f] => .ok f
      | []  => .error "no func.func in the module"
      | _   =>
          match fs.find? (fun f => f.symAttr? "sym_name" == some "main") with
          | some f => .ok f
          | none   =>
              .error ("several functions and none called 'main', so name one with --func: "
                      ++ ", ".intercalate names)

/-- **Lower a parsed file**, taking the function named when there is more than one. The buffers are
collected first, because addresses are absolute and the layout therefore cannot be discovered while
lowering. -/
def lowerAt (entry : Option String) (ops : List Op) : Except String Lowered := do
  let f ← entryOf entry ops
  let decls ← do
    let globals ← collectOps (globalsOf ops)
    let own ← collectOp f
    .ok (globals ++ own)
  let L := Layout.of (decls.map BufDecl.arr)
  if !L.wfB then
    let names := ", ".intercalate (decls.map (fun d => d.arr.name))
    .error ("layout is ill-formed (duplicate buffer names, or more initial data than cells): "
            ++ names)
  let (ps, st) ← lowerOp ⟨L, decls⟩ f ⟨[], 0, [], true⟩
  .ok ⟨L, block ps, st.exact, st.notes.reverse, decls⟩

/-- The whole module, when it holds one function. -/
def lower (ops : List Op) : Except String Lowered := lowerAt none ops

/-- Parse — in either form, generic or custom — and lower. Naming a function in a custom-form file
reads *that function* and not the rest, which is what makes a real test file usable: the nineteen
functions beside it may hold a reduction or an op outside the vocabulary.
-- ref: `docs/mlir-pretty.md` § One function out of twenty -/
def lowerTextAt (entry : Option String) (src : String) : Except String Lowered := do
  match entry with
  | some nm =>
      if looksGeneric src then lowerAt entry (← parseAny src)
      else
        match (Pretty.parseFunctions src).find? (fun p => p.1 == nm) with
        | some (_, r) => lowerAt entry (← r)
        | none        =>
            let names := (Pretty.parseFunctions src).map Prod.fst
            .error (s!"no function called '{nm}' in this module: " ++ ", ".intercalate names)
  | none => lowerAt none (← parseAny src)

def lowerText (src : String) : Except String Lowered := lowerTextAt none src

/-! ## Verdicts

Two of them, and the difference is the price of a syntactic check. `verdict` is `wfB`: every heap,
read off the syntax, and what `par_seq_eq` takes. `verdictExact` is `wellFormedB`: this heap,
footprints measured along the canonical run, and complete for the obligation
(`raceSites_nil_iff`). A program `verdict` rejects and `verdictExact` accepts is the precision gap,
which is what a computed subscript costs. -/

namespace Lowered

/-- The initial heap: the declared contents at the allocated addresses. -/
def state (r : Lowered) : State := r.layout.state

/-- `wfB`: pairwise independence at every `par` node, for every heap. -/
def verdict (r : Lowered) : Bool := wfB r.prog

/-- `wellFormedB`: the same obligation at this heap, with exact footprints. -/
def verdictExact (r : Lowered) : Bool := wellFormedB (execPar r.prog (fun _ => 0)) r.state

/-- Whether the footprint `verdict` used is exact rather than a bound. -/
def footprintIsExact (r : Lowered) : Bool := footprintExact r.prog

/-- The `par` nodes that fail Bernstein, with the cells they collide on. -/
def sites (r : Lowered) : List RaceSite := raceSites (execPar r.prog (fun _ => 0)) r.state

/-- The heap after a threaded run. Sound to look at only when `verdict` holds — that is exactly
`runTask_eq`. -/
def run (r : Lowered) : State := (runTask r.prog (fun _ => 0) r.state).2

/-- A named buffer's cells after the run. -/
def cells (r : Lowered) (name : String) : List Val :=
  let a := r.layout.ref name
  let σ := r.run
  (List.range a.len).map (fun i => σ (a.base + i))

/-- Buffers whose element type is floating point. -/
def floatBufs (r : Lowered) : List String :=
  (r.decls.filter (fun d => isFloatTy d.elt)).map (fun d => d.arr.name)

/-- **The whole story about one benchmark**, in the order a corpus table wants it. -/
def report (r : Lowered) : String :=
  let f := ParProg.footprintOf r.prog
  "layout      " ++ ", ".intercalate (r.layout.bufs.map (fun p =>
      p.name ++ toString p.shape ++ "@" ++ toString p.base))
    ++ "\nfloat bufs  " ++ (if r.floatBufs.isEmpty then "(none)"
                            else ", ".intercalate r.floatBufs)
    ++ "\nreads       " ++ toString f.reads.length ++ " cells"
    ++ "\nwrites      " ++ toString f.writes.length ++ " cells"
    ++ "\nfootprint   " ++ (if r.footprintIsExact then "exact" else "over-approximated")
    ++ "\nverdict     wfB " ++ toString r.verdict
                          ++ ", wellFormedB " ++ toString r.verdictExact
    ++ "\nsites       " ++ toString r.sites.length
    ++ "\nvalues      " ++ (if r.exactValues then "exact in Int"
                            else "approximated in Int; MLIR/Eval.lean is the ℚ reference")
    ++ (if r.notes.isEmpty then ""
        else "\nnotes\n" ++ "\n".intercalate (r.notes.map (fun n => "  - " ++ n)))

end Lowered

/-! ## Expressiveness

The op names no rule handles. This list *is* the taxonomy a corpus report needs: what is missing is
counted rather than discovered one benchmark at a time. -/

/-- Every op the lowering has a rule for. -/
def handledOps : List String :=
  [ "builtin.module", "func.func", "func.return",
    "affine.yield", "affine.for", "affine.parallel", "affine.load", "affine.store", "affine.apply",
    "memref.load", "memref.store", "memref.alloc", "memref.alloca", "memref.dealloc",
    "memref.global", "memref.get_global",
    "arith.constant", "arith.addi", "arith.subi", "arith.muli", "arith.divsi", "arith.divui",
    "arith.maxsi", "arith.minsi",
    "arith.addf", "arith.subf", "arith.mulf", "arith.divf", "arith.maxnumf", "arith.minnumf",
    "arith.index_cast", "arith.index_castui", "arith.extsi", "arith.extui", "arith.trunci",
    "arith.sitofp", "arith.uitofp", "arith.extf", "arith.truncf", "arith.fptosi", "arith.fptoui",
    "async.execute", "async.await", "async.await_all", "async.yield" ]

/-- Op names in the file that no rule handles. -/
def unsupportedOps (ops : List Op) : List String :=
  (opNamesOf ops).filter (fun nm => !handledOps.contains nm)

end Paralever.MLIR
