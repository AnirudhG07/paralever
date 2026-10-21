import Prl.Compile.Parse
import Prl.Lang.Core

/-! # From a `.prl` file to `Layout × ParProg`

Names are resolved, compile-time arithmetic is folded, loops are unrolled. The result is the
`ParProg` a `paralever { … }` block elaborates to, so `footprintOf`, `wfB`, `par_seq_eq`, `execTask`
and the autoparallelizer apply unchanged.

`buf` and `free` are **erased**: they place memory and end its lifetime, and neither emits a
`ParProg` node, so no theorem about the program can depend on either. Rejected rather than
approximated: a register in a bare address, a subscript outside its buffer, a live buffer overlapping
another, a use after `free`, `%` in a value expression. -- ref: `docs/prl.md` -/

namespace Paralever.Prl
open Paralever

/-- What names mean, at one point in the file. -/
structure Env where
  /-- `const`s and the enclosing loop variables, innermost first. -/
  consts : List (String × Int) := []
  /-- Assigned by `assignRegs` before compilation, so a register never needs declaring. -/
  regs   : List (String × Reg) := []
  layout : Layout := ⟨[]⟩
  /-- Where the next allocator-placed buffer goes. -/
  next   : Loc := 0
  /-- Buffers whose lifetime has ended. -/
  dead   : List String := []

/-- A compiled file: the declared memory, the program, the register names, and the buffers whose
lifetime ended. `dead` is what `free` leaves behind — it is not part of the program. -/
structure Compiled where
  layout : Layout
  prog   : ParProg
  regs   : List (String × Reg)
  dead   : List String := []
  deriving Repr

/-- The buffer a location belongs to, preferring one that is still live: after a `free` two names
can own a cell, and the live one is what the program calls it. -/
def Compiled.locName (c : Compiled) (l : Loc) : String :=
  let owners := c.layout.bufs.filter (fun p => p.base ≤ l && l < p.base + p.toBuf.size)
  match owners.find? (fun p => !c.dead.contains p.name) with
  | some p => (Layout.nameOf ⟨[p]⟩ l).getD (toString l)
  | none   => c.layout.show l

/-! ## Registers

Every `%name` in the file is collected and given an index before anything is compiled, so a name
needs no declaration and gets the same index wherever it occurs. `reg acc = 3` pins one. -/

def Exp.regTokens : Exp → List String
  | .num _ | .name _ => []
  | .reg r  => [r]
  | .add a b | .sub a b | .mul a b | .div a b | .mod a b | .min a b | .max a b =>
      a.regTokens ++ b.regTokens

def Addr.regTokens : Addr → List String
  | .raw e     => e.regTokens
  | .cell _ es => es.flatMap Exp.regTokens

mutual

def Stmt.regTokens : Stmt → List String
  | .load r a      => r :: a.regTokens
  | .store a e     => a.regTokens ++ e.regTokens
  | .set r e       => r :: e.regTokens
  | .par ts _      => threadTokens ts
  | .forIn _ n b   => n.regTokens ++ stmtTokens b
  | .parfor _ n b _ => n.regTokens ++ stmtTokens b
  | .ifElse c t e  => c.regTokens ++ stmtTokens t ++ stmtTokens e
  | .whileIn c n b => c.regTokens ++ n.regTokens ++ stmtTokens b
  | .decl ds       => ds.filterMap (fun d => match d with | .reg x _ => some x | _ => none)
  | .free _        => []

def stmtTokens : List Stmt → List String
  | []      => []
  | s :: ss => s.regTokens ++ stmtTokens ss

def threadTokens : List (List Stmt) → List String
  | []      => []
  | t :: ts => stmtTokens t ++ threadTokens ts

end

private def isNum (s : String) : Bool := !s.isEmpty && s.all Char.isDigit

/-- The smallest index not in `used`. -/
private def fresh (used : List Nat) : Nat :=
  ((List.range (used.length + 1)).find? (fun k => !used.contains k)).getD 0

private def assign : List String → List Nat → List (String × Reg) → List (String × Reg)
  | [],      _,    acc => acc
  | n :: ns, used, acc => let k := fresh used; assign ns (k :: used) (acc ++ [(n, k)])

/-- Indices for every register name in the file: pinned ones keep theirs, the rest take the lowest
index no numbered register uses. -/
def assignRegs (f : File) : List (String × Reg) :=
  let toks := stmtTokens f.body
  let pins := pinsOf f.body
  let nums := (toks.filter isNum).map (fun t => t.toNat!)
  let names := (toks.filter (fun t => !isNum t)).eraseDups.filter
                 (fun n => !(pins.map (fun p => p.1)).contains n)
  pins ++ assign names (nums ++ pins.map (fun p => p.2)) []
where
  /-- `reg acc = 3`, anywhere in the file. -/
  pinsOf : List Stmt → List (String × Reg)
    | []      => []
    | s :: ss =>
        (match s with
          | .decl ds => ds.filterMap (fun d => match d with | .reg x (some k) => some (x, k) | _ => none)
          | _        => []) ++ pinsOf ss

/-! ## Expressions -/

/-- Whether a register occurs: a compile-time address from a computed one. -/
def Exp.dynamic : Exp → Bool
  | .num _ | .name _ => false
  | .reg _  => true
  | .add a b | .sub a b | .mul a b | .div a b | .mod a b | .min a b | .max a b =>
      a.dynamic || b.dynamic

/-- The register an occurrence names. -/
def Env.reg (E : Env) (r : String) : Except String Reg :=
  if isNum r then .ok r.toNat!
  else match E.regs.lookup r with
    | some i => .ok i
    | none   => .error s!"no register '%{r}'"

/-- The buffer a name denotes, if it is declared and still live. -/
def Env.buf? (E : Env) (nm : String) : Except String Placed :=
  match E.layout.find? nm with
  | none   => .error s!"undeclared buffer '{nm}'"
  | some p => if E.dead.contains nm then .error s!"'{nm}' was freed" else .ok p

private def Env.nameErr (E : Env) (x : String) (role : String) : String :=
  if E.dead.contains x then s!"'{x}' was freed"
  else if (E.layout.find? x).isSome then s!"'{x}' is a buffer — {role}"
  else s!"unknown name '{x}'"

/-- An expression as a compile-time number. -/
def Env.fold (E : Env) : Exp → Except String Int
  | .num n  => .ok n
  | .name x =>
      match E.consts.lookup x with
      | some v => .ok v
      | none   => .error (E.nameErr x s!"subscript it, as {x}[i]")
  | .reg r  =>
      .error s!"'%{r}' is a register, so this address is only known at run time — \
write it as a subscript, A[%{r}], so the access is confined to A"
  | .add a b => do pure ((← E.fold a) + (← E.fold b))
  | .sub a b => do pure ((← E.fold a) - (← E.fold b))
  | .mul a b => do pure ((← E.fold a) * (← E.fold b))
  | .min a b => do let x ← E.fold a; let y ← E.fold b; pure (if x ≤ y then x else y)
  | .max a b => do let x ← E.fold a; let y ← E.fold b; pure (if x ≤ y then y else x)
  | .div a b => do
      let d ← E.fold b
      if d == 0 then .error "division by zero in an address" else pure ((← E.fold a) / d)
  | .mod a b => do
      let d ← E.fold b
      if d == 0 then .error "division by zero in an address" else pure ((← E.fold a) % d)

/-- A compile-time number that must be a size or an address. -/
def Env.foldNat (E : Env) (e : Exp) : Except String Nat := do
  let v ← E.fold e
  if v < 0 then .error s!"expected a non-negative number, got {v}" else pure v.toNat

/-- An expression as an `AExp`: constants fold to literals, registers stay. -/
def Env.aexp (E : Env) : Exp → Except String AExp
  | .num n  => .ok (.lit n)
  | .name x =>
      match E.consts.lookup x with
      | some v => .ok (.lit v)
      | none   => .error (E.nameErr x s!"a value must be loaded first: %r := {x}[i]")
  | .reg r  => do pure (.reg (← E.reg r))
  | .add a b => do pure (.add (← E.aexp a) (← E.aexp b))
  | .sub a b => do pure (.sub (← E.aexp a) (← E.aexp b))
  | .mul a b => do pure (.mul (← E.aexp a) (← E.aexp b))
  | .div a b => do pure (.div (← E.aexp a) (← E.aexp b))
  | .min a b => do pure (.min (← E.aexp a) (← E.aexp b))
  | .max a b => do pure (.max (← E.aexp a) (← E.aexp b))
  | .mod _ _ => .error "'%' is not a value operator: AExp has no modulo (docs/block-ir.md)"

/-! ## Addresses -/

/-- Where a statement touches: a literal location, or a cell of an array chosen at run time. -/
inductive Place where
  | fixed : Loc → Place
  | dyn   : ArrRef → AExp → Place

/-- Resolve an address. A subscript mentioning a register gives the data-dependent form, confined to
its array by `ArrRef.addr_mem_cells`. -/
def Env.place (E : Env) : Addr → Except String Place
  | .raw e => do pure (.fixed (← E.foldNat e))
  | .cell nm idx => do
      let p ← E.buf? nm
      if idx.any Exp.dynamic then
        match idx with
        | [e] => do pure (.dyn p.ref (← E.aexp e))
        | _   => .error s!"a computed subscript must be the only one: {nm}[%r] indexes \
{nm} flat, and wraps on its {p.toBuf.size} cells"
      else do
        let ids ← idx.mapM E.foldNat
        if p.toBuf.inRange ids then pure (.fixed (E.layout.at nm ids))
        else .error s!"{nm}{ids} is outside {nm}, which has shape {p.shape}"

/-! ## Declarations

Positional, because `free` is. With no `at` a buffer goes where the previous one ended (`alloc`'s
placement); with an `at` it is checked against every *live* buffer. `free` ends a lifetime, and
returns the space when the buffer is the most recent one placed. -/

/-- The live buffer this one would overlap. -/
private def clash (E : Env) (p : Placed) : Option String :=
  (E.layout.bufs.find? (fun q =>
      !E.dead.contains q.name &&
      !(decide (q.base + q.toBuf.size ≤ p.base) || decide (p.base + p.toBuf.size ≤ q.base)))).map
    (fun q => s!"'{p.name}' at {p.base}..{p.base + p.toBuf.size} overlaps live '{q.name}' at \
{q.base}..{q.base + q.toBuf.size}")

def Env.addDecl (E : Env) : Decl → Except String Env
  | .const x e => do
      let v ← E.fold e
      pure { E with consts := (x, v) :: E.consts }
  -- `assignRegs` owns register indices, so a `reg` statement adds nothing here
  | .reg _ _ => pure E
  | .buf nm shape init at? => do
      let dims ← shape.mapM E.foldNat
      let vals ← (match init with
        | .data es => do pure (Paralever.data (← es.mapM E.fold))
        | .full e  => do pure (Paralever.full (← E.fold e))
        | .zeros   => pure Paralever.zeros
        | .ones    => pure Paralever.ones
        | .eye     => pure Paralever.eye
        | .arange  => pure Paralever.arange : Except String Init)
      let b := buf nm dims vals
      if (E.layout.find? nm).isSome then .error s!"'{nm}' is declared twice"
      else do
        let base ← match at? with
          | none   => pure E.next
          | some e => E.foldNat e
        let p : Placed := ⟨b, base⟩
        match clash E p with
        | some msg => .error msg
        | none =>
            if b.init.length > b.size then
              .error s!"'{nm}' has {b.size} cells but {b.init.length} initial values"
            else pure { E with
              layout := ⟨E.layout.bufs ++ [p]⟩, next := max E.next (base + b.size) }

/-- End a buffer's lifetime. The space is returned to the allocator when this buffer is the most
recent one placed, which makes `buf`/`free` a stack; freeing out of order ends the name's scope and
leaves the hole. -/
def Env.freeBuf (E : Env) (nm : String) : Except String Env := do
  let p ← E.buf? nm
  pure { E with dead := nm :: E.dead, next := p.release E.next }

/-! ## Statements -/

mutual

/-- One statement, and the environment the next one sees. A `for` splices its unrolled iterations
into the enclosing chain rather than nesting a block in it, so the chain `AutoPar.flatten` sees is
the chain that was written. -/
partial def compileStmt (E : Env) (top : Bool) : Stmt → Except String (List ParProg × Env)
  | .decl ds =>
      if top then do pure ([], ← ds.foldlM Env.addDecl E)
      else .error "a declaration belongs at the top level of the program"
  | .free nm =>
      if top then do pure ([], ← E.freeBuf nm)
      else .error "'free' belongs at the top level of the program"
  | .load r a => do
      let i ← E.reg r
      match ← E.place a with
      | .fixed l   => pure ([.load i l], E)
      | .dyn ar ix => pure ([.loadAt i ar ix], E)
  | .store a e => do
      let v ← E.aexp e
      match ← E.place a with
      | .fixed l   => pure ([.store l v], E)
      | .dyn ar ix => pure ([.storeAt ar ix v], E)
  | .set r e => do pure ([.set (← E.reg r) (← E.aexp e)], E)
  | .par ts nm => do
      let bodies ← ts.mapM (fun t => do pure (ParProg.block (← compileStmts E false t).1))
      pure ([nm.elim id ParProg.label (.par bodies)], E)
  | .forIn i n body => do
      let k ← E.foldNat n
      let parts ← (List.range k).mapM fun j =>
        do pure (← compileStmts { E with consts := (i, Int.ofNat j) :: E.consts } false body).1
      pure (parts.flatten, E)
  | .parfor i n body nm => do
      let k ← E.foldNat n
      let bodies ← (List.range k).mapM fun j => do
        pure (ParProg.block
          (← compileStmts { E with consts := (i, Int.ofNat j) :: E.consts } false body).1)
      pure ([nm.elim id ParProg.label (.par bodies)], E)
  | .ifElse c t e => do
      pure ([.ifElse (← E.aexp c) (ParProg.block (← compileStmts E false t).1)
                                  (ParProg.block (← compileStmts E false e).1)], E)
  | .whileIn c n body => do
      pure ([ParProg.whileAtMost (← E.foldNat n) (← E.aexp c)
              (ParProg.block (← compileStmts E false body).1)], E)

partial def compileStmts (E : Env) (top : Bool) : List Stmt → Except String (List ParProg × Env)
  | []      => .ok ([], E)
  | s :: ss => do
      let (a, E') ← compileStmt E top s
      let (b, E'') ← compileStmts E' top ss
      pure (a ++ b, E'')

end

/-- **Compile a file.** -/
def compile (f : File) : Except String Compiled := do
  let (ss, E) ← compileStmts { regs := assignRegs f } true f.body
  pure ⟨E.layout, ParProg.block ss, E.regs, E.dead⟩

/-- **Read and compile `.prl` text.** -/
def ofString (src : String) : Except String Compiled := do compile (← parse src)

end Paralever.Prl
