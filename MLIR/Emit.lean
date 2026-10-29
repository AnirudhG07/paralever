import MLIR.Lower
import Lang.Core.Analysis

/-! # Generic form out: a compiled program as MLIR

The other direction of `MLIR/Lower.lean`. A `Compiled` holds a `Layout` and an unrolled `ParProg`,
and both have generic-form spellings: a buffer is a `memref.global`, a thread is an
`async.execute`, and a fork's join is the `async.await_all` that closes it.

What is **not** expressible is rejected rather than approximated, as the reader rejects: `ifElse`
(the supported op set has no conditional), a computed subscript into a multi-dimensional buffer
(`ArrRef.addr` takes one index), and an address in no buffer (MLIR has no memory outside a memref).

Two things change on the way out, both recorded in the emitted file's header. Registers are
assignable and SSA values are not, so `set` nodes disappear into the expressions that use them;
and a `.prl` computed subscript wraps on the buffer's length (`ArrRef.addr_mem_cells`) where
MLIR's does not, so the two agree on indices in range. `roundTrips` is the gate: what comes back
has the same memory, the same footprint, the same verdict and leaves the same heap.
-- ref: `docs/mlir.md` § Generic form out -/

namespace Paralever.MLIR
open Paralever Paralever.Lang

/-- The element type every cell is emitted at. `Val` is an `Int`, so one width serves. -/
def cellTy : MTy := .int 64

/-- `!async.token` — what an `async.execute` yields and an `async.await_all` consumes. -/
def tokenTy : MTy := .other "!async.token"

/-- What the emitter carries: the next SSA number, the value holding each register, and the
approximations made. -/
structure ESt where
  next  : Nat := 0
  env   : List (Reg × String) := []
  notes : List String := []

/-- The emitter: generic-form operations, or a named refusal. -/
abbrev E (α : Type) := StateT ESt (Except String) α

namespace E

/-- A fresh SSA name. Numeric, so it can never collide with a buffer's name, and allocated in
textual order, which is the order MLIR requires unnamed values to be defined in. -/
def fresh : E String := do
  let st ← get
  set { st with next := st.next + 1 }
  pure (toString st.next)

/-- The SSA value a register currently holds. -/
def reg? (r : Reg) : E (Option String) := do
  pure (((← get).env.find? (fun p => p.1 == r)).map Prod.snd)

def bindReg (r : Reg) (v : String) : E Unit :=
  modify fun st => { st with env := (r, v) :: st.env }

def note (m : String) : E Unit :=
  modify fun st => { st with notes := if st.notes.contains m then st.notes else st.notes ++ [m] }

/-- Run `p` with the registers it is forked with, and drop what it binds: a thread's registers are
private, which is how `lowerThread` reads one back. -/
def thread (p : E α) : E α := do
  let before := (← get).env
  let a ← p
  modify fun st => { st with env := before }
  pure a

end E

open E

/-- One operation. -/
def mk (nm : String) (res ops : List String) (attrs : List (String × MAttr))
    (rgs : List Region) (ins outs : List MTy) : Op := ⟨nm, res, ops, attrs, rgs, ins, outs⟩

/-- `%r = "arith.constant"() {value = v : t} : () -> t`. The annotation is not decoration: MLIR
reads `arith.constant` only with its value typed. -/
def constOp (r : String) (v : Int) (t : MTy) : Op :=
  mk "arith.constant" [r] [] [("value", .ann (.int v) t)] [] [] [t]

/-- The memref type of a declared buffer. A shapeless buffer is one cell. -/
def memTy (p : Placed) : MTy :=
  .memref (if p.shape.isEmpty then [p.toBuf.size] else p.shape) cellTy

/-- The buffer an address falls in, with the subscript it names there. -/
def place (L : Layout) (l : Loc) : E (Placed × List Nat) := do
  match L.bufs.find? (fun p => p.base ≤ l && l < p.base + p.toBuf.size) with
  | some p => pure (p, if p.shape.isEmpty then [l - p.base] else unoffset p.shape (l - p.base))
  | none   => throw s!"address {l} is in no buffer, and MLIR has no memory outside a memref"

/-- The buffer a computed access ranges over, which `ArrRef` names by its base. -/
def ranged (L : Layout) (a : ArrRef) : E Placed := do
  match L.bufs.find? (fun p => p.base == a.base && p.toBuf.size == a.len) with
  | some p =>
      if p.shape.length ≤ 1 then pure p
      else throw s!"computed subscript into '{p.name}', which has {p.shape.length} dimensions: \
                    one index is all ArrRef.addr takes"
  | none   => throw s!"the range [{a.base}, {a.base + a.len}) is no declared buffer"

/-- Index constants for a subscript. -/
def idxOps (idx : List Nat) : E (List Op × List String) := do
  let ns ← idx.mapM fun (k : Nat) => do
    let n ← fresh
    pure (n, constOp n (Int.ofNat k) .index)
  pure (ns.map Prod.snd, ns.map Prod.fst)

/-- An arithmetic expression, as the operations that compute it and the name of its value. A
register read before it is written emits the `0` every run starts from. -/
partial def expOps : AExp → E (List Op × String)
  | .lit n   => do let r ← fresh; pure ([constOp r n cellTy], r)
  | .reg k   => do
      match ← reg? k with
      | some v => pure ([], v)
      | none   => do
          note s!"%{k} is read before it is written, so it emits the 0 a run starts from"
          let r ← fresh
          pure ([constOp r 0 cellTy], r)
  | .add a b => bin "arith.addi" a b
  | .sub a b => bin "arith.subi" a b
  | .mul a b => bin "arith.muli" a b
  | .div a b => bin "arith.divsi" a b
  | .min a b => bin "arith.minsi" a b
  | .max a b => bin "arith.maxsi" a b
  | .lt a b  => cmp 2 a b          -- `slt`
  | .eq a b  => cmp 0 a b          -- `eq`
  -- `not a` is `a == 0`, which is one op fewer than negating a comparison and reads back as the
  -- same `AExp` the emitter was given.
  | .not a   => cmp 0 a (.lit 0)
where
  bin (nm : String) (a b : AExp) : E (List Op × String) := do
    let (oa, na) ← expOps a
    let (ob, nb) ← expOps b
    let r ← fresh
    pure (oa ++ ob ++ [mk nm [r] [na, nb] [] [] [cellTy, cellTy] [cellTy]], r)
  -- `arith.cmpi` answers in `i1`, and a cell holds `cellTy`, so the comparison is widened. The
  -- predicate is MLIR's own numbering: 0 is `eq`, 2 is `slt`. -- ref: `docs/mlir.md` § Conditions
  cmp (pred : Int) (a b : AExp) : E (List Op × String) := do
    let (oa, na) ← expOps a
    let (ob, nb) ← expOps b
    let c ← fresh
    let r ← fresh
    pure (oa ++ ob ++
      [ mk "arith.cmpi" [c] [na, nb] [("predicate", .ann (.int pred) (.int 64))] []
          [cellTy, cellTy] [.int 1],
        mk "arith.extui" [r] [c] [] [] [.int 1] [cellTy] ], r)

/-- `%i = "arith.index_cast"(%v) : (i64) -> index` — a computed subscript is an index. -/
def toIndex (v : String) : E (List Op × String) := do
  let r ← fresh
  pure ([mk "arith.index_cast" [r] [v] [] [] [cellTy] [.index]], r)

/-! ## A rolled nest, out

A nest is `affine.parallel` over its forked prefix wrapping one `affine.for` per sequential level,
which is the pair of ops `MLIR/Lower.lean` reads back as one.

The subscript maps are reconstructed by dividing the flat coefficients by the memref's row-major
strides, outermost axis first. The division is exact — `Σ strides[j] · axis[j]` is the flat form it
came from — so the reader's own `rowMajor` recovers the access that was declared, which is what
`emitRoundTrips` compares. -- ref: `docs/loops.md` § The nest, out -/

/-- A flat linear form split into one form per memref axis, against the axis strides. -/
def splitAxes : List Nat → List Nat → Nat → List (List Nat × Nat)
  | [],      _,  _   => []
  | s :: ss, cs, off =>
      ((cs.map (fun c => c / s), off / s)) :: splitAxes ss (cs.map (fun c => c % s)) (off % s)

/-- One axis's form as an affine expression over the nest's coordinates. -/
def axisExp (q : List Nat) (c : Nat) : AffExp :=
  q.zipIdx.foldl
    (fun acc (k, j) => if k == 0 then acc else .add acc (.mul (.const (Int.ofNat k)) (.dim j)))
    (.const (Int.ofNat c))

/-- The axes a buffer is emitted with: its shape, or one axis of `size` cells when it is
shapeless — exactly what `memTy` writes, so the reader reads the shape back. -/
def emitAxes (p : Placed) : List Nat :=
  if p.shape.isEmpty then [p.toBuf.size] else p.shape

/-- The map an affine access carries: one result per axis, over the nest's levels. -/
def accessMapOf (depth : Nat) (p : Placed) (a : Nest.AffAccess) : AffMap :=
  ⟨(List.range depth).map (fun i => "d" ++ toString i), [],
   (splitAxes (Nest.strides (emitAxes p)) a.coeffs a.off).map (fun qc => axisExp qc.1 qc.2)⟩

/-- The buffer an access names, found by its base and extent as `ranged` finds a computed one. -/
def accessBuf (L : Layout) (a : Nest.AffAccess) : E Placed := do
  match L.bufs.find? (fun p => p.base == a.base && p.toBuf.size == a.size) with
  | some p => pure p
  | none   => throw s!"a rolled nest accesses [{a.base}, {a.base + a.size}), which is no declared \
                       buffer"

/-- A constant-tuple affine map — the form `affine.for` and `affine.parallel` write bounds in. -/
def constMap (ks : List Int) : MAttr := .affine ⟨[], [], ks.map AffExp.const⟩

/-- `"affine.yield"() : () -> ()` — the terminator every affine region needs. -/
def affineYield : Op := mk "affine.yield" [] [] [] [] [] []

mutual

/-- One statement, as the operations it contributes. -/
partial def stmtOps (L : Layout) : ParProg → E (List Op)
  | .set r e => do
      let (os, v) ← expOps e
      bindReg r v
      pure os
  | .load r l => do
      let (p, idx) ← place L l
      let (cs, ns) ← idxOps idx
      let v ← fresh
      bindReg r v
      pure (cs ++ [mk "memref.load" [v] (p.name :: ns) [] []
                      (memTy p :: ns.map (fun _ => MTy.index)) [cellTy]])
  | .store l e => do
      let (p, idx) ← place L l
      let (os, v) ← expOps e
      let (cs, ns) ← idxOps idx
      pure (os ++ cs ++ [mk "memref.store" [] (v :: p.name :: ns) [] []
                            (cellTy :: memTy p :: ns.map (fun _ => MTy.index)) []])
  | .loadAt r a e => do
      let p ← ranged L a
      let (os, v) ← expOps e
      let (cast, i) ← toIndex v
      let w ← fresh
      bindReg r w
      note s!"%{r} := {p.name}[·] keeps the index MLIR is given; the `.prl` access wraps it on \
              {p.name}'s length, so the two agree on indices in range"
      pure (os ++ cast ++ [mk "memref.load" [w] [p.name, i] [] [] [memTy p, .index] [cellTy]])
  | .storeAt a e v => do
      let p ← ranged L a
      let (ov, nv) ← expOps v
      let (oe, ne) ← expOps e
      let (cast, i) ← toIndex ne
      note s!"{p.name}[·] := … keeps the index MLIR is given; the `.prl` access wraps it on \
              {p.name}'s length, so the two agree on indices in range"
      pure (ov ++ oe ++ cast ++ [mk "memref.store" [] [nv, p.name, i] [] []
                                    [cellTy, memTy p, .index] []])
  | .seq a b => do pure ((← stmtOps L a) ++ (← stmtOps L b))
  | .par ss => forkOps L ss none
  | .label nm s => do
      match s with
      | .par ss => forkOps L ss (some nm)
      | _       => do
          note s!"the region named '{nm}' is emitted without its name: only a fork carries one, \
                  on the async.await_all that closes it"
          stmtOps L s
  | .ifElse _ _ _ =>
      throw "if/else has no spelling in the op set the reader supports, so a file with one \
             cannot be emitted as MLIR"
  | .synchronize => do
      note ("synchronize needs no operation: every fork is already closed by the async.await_all "
            ++ "that joins it, so the phases MLIR sees are the phases the barrier marks")
      pure []
  | .print _ =>
      throw "print has no spelling in the op set the reader supports, so a file with one cannot \
             be emitted as MLIR"
  | .loop n => thread (do
      let depth := n.ivs.length
      -- one block argument per level, in the order the subscript maps index them
      let avs ← (List.range depth).mapM (fun _ => fresh)
      -- a level's induction register holds the loop's *value*, which is its block argument. MLIR
      -- types that `index` and a cell `i64`, so a body that reads an index as a value gets the
      -- cast; one that only subscripts with it gets nothing.
      let used := Paralever.Lang.ParProg.regsOfNest n.body
      let casts ← (n.ivs.zip avs).filterMapM fun (r, v) =>
        if used.contains r then do
          let (os, w) ← toIndex v
          bindReg r w
          pure (some os)
        else pure none
      let body ← n.body.foldlM (fun acc st => do pure (acc ++ (← nestStmtOps L depth avs st))) []
      pure (nestOps n avs (casts.flatten ++ body)))

/-- A fork: one `async.execute` per thread, then the `async.await_all` that joins them. The token
is named before its body is emitted, because that is the order the names are defined in. -/
partial def forkOps (L : Layout) (ss : List ParProg) (nm : Option String) : E (List Op) := do
  let ts ← ss.mapM fun t => do
    let tk ← fresh
    let body ← thread (stmtOps L t)
    pure (tk, mk "async.execute" [tk] [] [("operandSegmentSizes", .darr "i32" [0, 0, 0])]
                  [⟨[], body ++ [mk "async.yield" [] [] [] [] [] []]⟩] [] [tokenTy])
  let toks := ts.map Prod.fst
  let join := mk "async.await_all" [] toks
                (nm.elim [] (fun n => [("paralever.label", MAttr.str n)])) []
                (toks.map (fun _ => tokenTy)) []
  pure (ts.map Prod.snd ++ [join])

/-- One body statement of a nest: an `affine.load`, an `affine.store`, or the arithmetic a `.st`
is. The index operands are every level's block argument, which is what makes the map's dimensions
the nest's coordinates. -/
partial def nestStmtOps (L : Layout) (depth : Nat) (avs : List String) :
    NestStmt → E (List Op)
  | .rd r a => do
      let p ← accessBuf L a
      let v ← fresh
      bindReg r v
      pure [mk "affine.load" [v] (p.name :: avs) [("map", .affine (accessMapOf depth p a))] []
               (memTy p :: avs.map (fun _ => MTy.index)) [cellTy]]
  | .wr a e => do
      let p ← accessBuf L a
      let (os, v) ← expOps e
      pure (os ++ [mk "affine.store" [] (v :: p.name :: avs)
                      [("map", .affine (accessMapOf depth p a))] []
                      (cellTy :: memTy p :: avs.map (fun _ => MTy.index)) []])
  | .st r e => do
      let (os, v) ← expOps e
      bindReg r v
      pure os

/-- The nest's own operations: `affine.parallel` over the forked prefix, then one `affine.for` per
sequential level, innermost last. A nest with no forked level is the `affine.for` chain alone,
which is what `parDepth = 0` means. -/
partial def nestOps (n : LoopNest) (avs : List String) (body : List Op) : List Op :=
  let lv := fun (k : Nat) => (n.lo.getD k 0, n.sizes.getD k 0, n.step.getD k 1)
  let seqs := (List.range (n.ivs.length - n.parDepth)).map (fun j => n.parDepth + j)
  -- innermost first, so each `affine.for` wraps what is already built
  let inner := seqs.reverse.foldl (fun acc k =>
      let (lo, sz, sp) := lv k
      [ mk "affine.for" [] [] [ ("lowerBound", constMap [lo])
                              , ("upperBound", constMap [lo + sp * Int.ofNat sz])
                              , ("step", .int sp) ]
          [⟨[(avs.getD k "0", MTy.index)], acc ++ [affineYield]⟩] [] [] ]) body
  if n.parDepth == 0 then inner
  else
    let ks := List.range n.parDepth
    [ mk "affine.parallel" [] []
        [ ("lowerBoundsMap", constMap (ks.map (fun k => (lv k).1)))
        , ("upperBoundsMap", constMap (ks.map (fun k =>
              let (lo, sz, sp) := lv k; lo + sp * Int.ofNat sz)))
        , ("steps", .arr ((ks.map (fun k => (lv k).2.2)).map MAttr.int)) ]
        [⟨ks.map (fun k => (avs.getD k "0", MTy.index)), inner ++ [affineYield]⟩] [] [] ]

end

/-- A buffer's declaration: `memref.global` with its contents, padded to its cells. -/
def globalOp (p : Placed) : Op :=
  let n := p.toBuf.size
  let es := p.init.take n ++ List.replicate (n - p.init.length) 0
  mk "memref.global" [] []
    [ ("sym_name", .str p.name)
    , ("type", .ty (memTy p))
    , ("initial_value",
        .ann (.dense es false)
          (.tensor (if p.shape.isEmpty then [n] else p.shape) cellTy)) ]
    [] [] []

/-- `%A = "memref.get_global"() {name = @A} : () -> memref<…>`, one per buffer: the names the body
then uses. -/
def getGlobalOp (p : Placed) : Op :=
  mk "memref.get_global" [p.name] [] [("name", .sym p.name)] [] [] [memTy p]

/-- Pairs of buffers that share cells. A `free` that returned space leaves one: the names overlap
by design, and `Layout` is happy with that. -/
def overlapping (L : Layout) : List (String × String) :=
  L.bufs.flatMap fun p => (L.bufs.filter fun q =>
      p.name < q.name
        && !(decide (p.base + p.toBuf.size ≤ q.base) || decide (q.base + q.toBuf.size ≤ p.base))
    ).map (fun q => (p.name, q.name))

/-- **A compiled program as a module**, with whatever was given up on the way. -/
def emitOps (L : Layout) (p : ParProg) (entry : String := "main") :
    Except String (List Op × List String) := do
  match overlapping L with
  | (a, b) :: _ =>
      .error s!"'{a}' and '{b}' share cells, which is what a `free` that returned space leaves \
                behind: two MLIR globals cannot alias, so the file has no generic-form spelling"
  | [] => do
  let (body, st) ← (stmtOps L p).run {}
  let fn := mk "func.func" [] []
    [("function_type", .ty (.fn [] [])), ("sym_name", .str entry)]
    [⟨[], L.bufs.map getGlobalOp ++ body ++ [mk "func.return" [] [] [] [] [] []]⟩] [] []
  let md := mk "builtin.module" [] [] [] [⟨[], L.bufs.map globalOp ++ [fn]⟩] [] []
  .ok ([md], st.notes)

/-- **The file**: a header saying where it came from and what changed, then the module. -/
def emitText (L : Layout) (p : ParProg) (from? : String := "") (entry : String := "main") :
    Except String String := do
  let (ops, notes) ← emitOps L p entry
  let hdr := (if from?.isEmpty then [] else ["// from " ++ from? ++ ", by paralever to-mlir"])
    ++ [ "// registers are not SSA values, so a `%r := e` with no memory in it is emitted into the"
       , "// expressions that read it rather than as an operation of its own." ]
    ++ notes.map (fun n => "// " ++ n)
  .ok ("\n".intercalate hdr ++ "\n" ++ render ops ++ "\n")

/-! ## The gate

Registers are renumbered and pure assignments are inlined on the way out, so the program that comes
back is not the same tree. What is compared instead is everything a theorem about it would use: the
memory, the footprint, the verdict, and the heap a sequential run leaves. -/

private def sameLocs (a b : List Loc) : Bool :=
  a.all (fun l => b.contains l) && b.all (fun l => a.contains l)

private def heapOf (L : Layout) (p : ParProg) : List Val :=
  let σ := (ParProg.runTaskSeq p (fun _ => 0) L.state).2
  (List.range L.top).map σ

/-- **Emit, read back, and compare.** -/
def emitRoundTrips (L : Layout) (p : ParProg) : Bool :=
  match emitText L p with
  | .error _  => false
  | .ok src   =>
      match lowerText src with
      | .error _ => false
      | .ok r    =>
          r.layout.bufs.map (fun q => q.base) == L.bufs.map (fun q => q.base)
            && r.layout.data == L.data
            && sameLocs (ParProg.footprintOf r.prog).reads (ParProg.footprintOf p).reads
            && sameLocs (ParProg.footprintOf r.prog).writes (ParProg.footprintOf p).writes
            && ParProg.wfB r.prog == ParProg.wfB p
            && heapOf r.layout r.prog == heapOf L p

end Paralever.MLIR
