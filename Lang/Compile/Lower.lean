import Lang.Compile.Parse
import Lang.Compile.Expand
import Lang.Core.Prog
import Lang.Core.Analysis
import Lang.Core.Roll

/-! # From a `.prl` file to `Layout × ParProg`

Names are resolved, compile-time arithmetic is folded, loops are unrolled. The result is the
`ParProg` a `paralever { … }` block elaborates to, so `footprintOf`, `wfB`, `par_seq_eq`, `execTask`
and the autoparallelizer apply unchanged.

`buf` and `free` are **erased**: they place memory and end its lifetime, and neither emits a
`ParProg` node, so no theorem about the program can depend on either. Rejected rather than
approximated: a register in a bare address, a subscript outside its buffer, a live buffer overlapping
another, a use after `free`, `%` in a value expression. -- ref: `docs/prl.md` -/

namespace Paralever.Lang
open Paralever

/-- A named sub-range of a buffer: the buffer whose cells these are, and the cells. The parent is
kept so that `free`ing a buffer ends the scope of every view of it, and it is always the buffer
itself — slicing a slice inherits the root. -- ref: `docs/prl.md` § Slices -/
structure Slice where
  parent : String
  ref    : ArrRef
  deriving Repr

/-- What names mean, at one point in the file. -/
structure Env where
  /-- `const`s and the enclosing loop variables, innermost first. -/
  consts : List (String × Int) := []
  /-- Assigned by `assignRegs` before compilation, so a register never needs declaring. -/
  regs   : List (String × Reg) := []
  /-- `slice h = A[lo..hi]`, innermost first. Erased: a slice contributes nothing to the layout. -/
  slices : List (String × Slice) := []
  layout : Layout := ⟨[]⟩
  /-- Where the next allocator-placed buffer goes. -/
  next   : Loc := 0
  /-- Buffers whose lifetime has ended. -/
  dead   : List String := []
  /-- Standard input not yet consumed. Empty when the program has no `input` form, and also when it
  has one and nothing was piped in — then the first read fails with "input is exhausted". -/
  inp    : Input := []
  /-- The loop variables of the enclosing *rolled* nests, innermost first. In a value expression
  such a variable is this register; in a subscript it is a coordinate, which is why rolling reads
  subscripts itself instead of going through `Env.place`. -- ref: `docs/loops.md` -/
  ivRegs : List (String × Reg) := []
  /-- One past the highest register index any occurrence in the file uses, so a rolled nest's
  induction registers cannot collide with the program's own. -/
  nextReg : Reg := 0

/-- **What an `assert` compiled to**: the other program, and the cells the two are compared on.
The file's own `prog` is the left side, so everything that reads a `Compiled` reads the left
program unchanged and a claim is extra. -- ref: `docs/equivalence.md` -/
structure Claim where
  /-- The two callees, as a report names them. -/
  left  : String
  right : String
  /-- The right side's program: the same file, with the right call's body written out instead. -/
  other : ParProg
  /-- The buffers compared, in the order the `on` list gave them; every live buffer when it was
  omitted. -/
  bufs  : List String
  /-- Those buffers' cells. -/
  cells : List Loc
  /-- Which keyword stated the claim, and so which relation it is: `AgreeOn` or `AgreeParSeq`. -/
  strength : Strength := .heap
  /-- The registers compared, empty for a `.heap` claim. `claimRegs` derives them. -/
  regs  : List Reg := []
  deriving Repr

/-- A compiled file: the declared memory, the program, the register names, and the buffers whose
lifetime ended. `dead` is what `free` leaves behind — it is not part of the program. -/
structure Compiled where
  layout : Layout
  prog   : ParProg
  regs   : List (String × Reg)
  dead   : List String := []
  /-- The file's `assert`, if it states one. -/
  claim  : Option Claim := none
  deriving Repr

/-- The claim's second program — the file's own when it states no claim, so that every reader is
total and `AgreeOn` on a claimless file is the (non-trivial) reflexive statement. -/
def Compiled.other (c : Compiled) : ParProg := c.claim.elim c.prog (·.other)

/-- The cells a claim compares, empty when the file states none. -/
def Compiled.compared (c : Compiled) : List Loc := c.claim.elim [] (·.cells)

/-- The buffer a location belongs to, preferring one that is still live: after a `free` two names
can own a cell, and the live one is what the program calls it. -/
def Compiled.locName (c : Compiled) (l : Loc) : String :=
  let owners := c.layout.bufs.filter (fun p => p.base ≤ l && l < p.base + p.toBuf.size)
  match owners.find? (fun p => !c.dead.contains p.name) with
  | some p => (Layout.nameOf ⟨[p]⟩ l).getD (toString l)
  | none   => c.layout.show l

/-- What the file calls a register: its `%name` when the file gave it one, and `%index` otherwise —
a register written as a number names its index, so it has no entry in the table.
-- ref: `docs/equivalence.md` § What `assertParSeq` adds -/
def Compiled.regName (c : Compiled) (r : Reg) : String :=
  match c.regs.find? (fun p => p.2 == r) with
  | some (n, _) => "%" ++ n
  | none        => "%" ++ toString r

/-- The registers a claim compares, empty when the file states none or states only a heap claim. -/
def Compiled.comparedRegs (c : Compiled) : List Reg := c.claim.elim [] (·.regs)

/-! ## Registers

Every `%name` in the file is collected and given an index before anything is compiled, so a name
needs no declaration and gets the same index wherever it occurs. `reg acc = 3` pins one. -/

-- `Stmt.regTokens` and the two walkers beside it are in `Lang/Compile/Expand.lean`: hygiene needs
-- the same list, and a call is written out before a register is given an index.

/-- The smallest index not in `used`. -/
private def lowestFree (used : List Nat) : Nat :=
  ((List.range (used.length + 1)).find? (fun k => !used.contains k)).getD 0

private def assign : List String → List Nat → List (String × Reg) → List (String × Reg)
  | [],      _,    acc => acc
  | n :: ns, used, acc => let k := lowestFree used; assign ns (k :: used) (acc ++ [(n, k)])

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

/-- **A register index no occurrence in the file uses.** A rolled nest needs induction registers
that are not in the program's own vocabulary, and `assignRegs` already knows every name; the
numbered occurrences are counted beside them because `%7` needs no declaration. -/
def freshRegBase (f : File) : Reg :=
  let nums := ((stmtTokens f.body).filter isNum).map (fun t => t.toNat!)
  ((assignRegs f).map (fun p => p.2) ++ nums).foldl Nat.max 0 + 1

/-! ## Expressions -/

/-- Whether a register occurs: a compile-time address from a computed one. -/
def Exp.dynamic : Exp → Bool
  | .num _ | .name _ | .len _ | .input => false
  | .reg _  => true
  | .add a b | .sub a b | .mul a b | .div a b | .mod a b | .min a b | .max a b
  | .lt a b | .eq a b => a.dynamic || b.dynamic
  | .not a  => a.dynamic

/-- The register an occurrence names. -/
def Env.reg (E : Env) (r : String) : Except Diag.Diagnostic Reg :=
  if isNum r then .ok r.toNat!
  else match E.regs.lookup r with
    | some i => .ok i
    | none   => .error (diag Diag.p101 s!"no register '%{r}'")

/-- The buffer a name denotes, if it is declared and still live. -/
def Env.buf? (E : Env) (nm : String) : Except Diag.Diagnostic Placed :=
  match E.layout.find? nm with
  | none   => .error (diag Diag.p101 s!"undeclared buffer '{nm}'")
  | some p =>
      if E.dead.contains nm then
        .error (diag Diag.p101 s!"'{nm}' was freed"
          (notes := ["a freed name keeps its address but leaves scope, so a later buffer may \
already own its cells"]))
      else .ok p

private def Env.nameErr (E : Env) (x : String) (role : String) : Diag.Diagnostic :=
  if E.dead.contains x then diag Diag.p101 s!"'{x}' was freed"
  else if (E.layout.find? x).isSome then
    diag Diag.p101 s!"'{x}' is a buffer, and a buffer is not a value" (hints := [role])
  else diag Diag.p101 s!"unknown name '{x}'"

/-- The range a name denotes — a buffer's cells or a slice's — with the buffer they belong to.
A slice is flat, so what comes back is one `ArrRef` whatever the buffer's shape. -/
def Env.rangeOf (E : Env) (nm : String) : Except Diag.Diagnostic (ArrRef × String) :=
  match E.slices.lookup nm with
  | some sl => .ok (sl.ref, sl.parent)
  | none    => do let p ← E.buf? nm; pure (p.ref, nm)

/-- `#A` — how many cells the name has. Folded to a literal, so it costs nothing at run time. -/
def Env.lenOf (E : Env) (nm : String) : Except Diag.Diagnostic Nat := do
  pure (← E.rangeOf nm).1.len

/-- An expression as a compile-time number. -/
def Env.fold (E : Env) : Exp → Except Diag.Diagnostic Int
  | .num n  => .ok n
  | .name x =>
      match E.ivRegs.lookup x, E.consts.lookup x with
      | some _, _      => .error (diag Diag.p105
          s!"'{x}' is a rolled nest's loop index, so this address is only known at run time"
          (hints := [s!"write it as a subscript, A[{x}], so the access is affine in the nest"]))
      | none,   some v => .ok v
      | none,   none   => .error (E.nameErr x s!"subscript it, as {x}[i]")
  | .reg r  =>
      .error (diag Diag.p105 s!"'%{r}' is a register, so this address is only known at run time"
        (hints := [s!"write it as a subscript, A[%{r}], so the access is confined to A"]))
  | .len x   => do pure (Int.ofNat (← E.lenOf x))
  | .add a b => do pure ((← E.fold a) + (← E.fold b))
  | .sub a b => do pure ((← E.fold a) - (← E.fold b))
  | .mul a b => do pure ((← E.fold a) * (← E.fold b))
  | .min a b => do let x ← E.fold a; let y ← E.fold b; pure (if x ≤ y then x else y)
  | .max a b => do let x ← E.fold a; let y ← E.fold b; pure (if x ≤ y then y else x)
  | .div a b => do
      let d ← E.fold b
      if d == 0 then .error (diag Diag.p105 "division by zero in an address")
      else pure ((← E.fold a) / d)
  | .mod a b => do
      let d ← E.fold b
      if d == 0 then .error (diag Diag.p105 "division by zero in an address")
      else pure ((← E.fold a) % d)
  | .lt a b  => do pure (if (← E.fold a) < (← E.fold b) then 1 else 0)
  | .eq a b  => do pure (if (← E.fold a) = (← E.fold b) then 1 else 0)
  | .not a   => do pure (if (← E.fold a) = 0 then 1 else 0)
  | .input   =>
      .error (diag Diag.p108 "'input' is a statement, not part of an address"
        (hints := ["read it into a register first, with '%r := input'"]))

/-- A compile-time number that must be a size or an address. -/
def Env.foldNat (E : Env) (e : Exp) : Except Diag.Diagnostic Nat := do
  let v ← E.fold e
  if v < 0 then .error (diag Diag.p105 s!"expected a non-negative number, got {v}")
  else pure v.toNat

/-- An expression as an `AExp`: constants fold to literals, registers stay. -/
def Env.aexp (E : Env) : Exp → Except Diag.Diagnostic AExp
  | .num n  => .ok (.lit n)
  | .name x =>
      match E.ivRegs.lookup x, E.consts.lookup x with
      | some i, _      => .ok (.reg i)
      | none,   some v => .ok (.lit v)
      | none,   none   => .error (E.nameErr x s!"a value must be loaded first: %r := {x}[i]")
  | .reg r  => do pure (.reg (← E.reg r))
  | .len x  => do pure (.lit (Int.ofNat (← E.lenOf x)))
  | .add a b => do pure (.add (← E.aexp a) (← E.aexp b))
  | .sub a b => do pure (.sub (← E.aexp a) (← E.aexp b))
  | .mul a b => do pure (.mul (← E.aexp a) (← E.aexp b))
  | .div a b => do pure (.div (← E.aexp a) (← E.aexp b))
  | .min a b => do pure (.min (← E.aexp a) (← E.aexp b))
  | .max a b => do pure (.max (← E.aexp a) (← E.aexp b))
  | .lt a b  => do pure (.lt (← E.aexp a) (← E.aexp b))
  | .eq a b  => do pure (.eq (← E.aexp a) (← E.aexp b))
  | .not a   => do pure (.not (← E.aexp a))
  | .mod _ _ =>
      .error (diag Diag.p107 "'%' is not a value operator: AExp has no modulo"
        (notes := ["an address is folded while the file compiles, so it has operators a run-time \
value does not (docs/block-ir.md)"]))
  | .input   =>
      .error (diag Diag.p108 "'input' reads one value and must be the whole right-hand side"
        (hints := ["write '%r := input', then use '%r' in the expression, so values are consumed \
in the order they are written"]))

/-! ## Addresses -/

/-- Where a statement touches: a literal location, or a cell of an array chosen at run time. -/
inductive Place where
  | fixed : Loc → Place
  | dyn   : ArrRef → AExp → Place

/-- `A[lo..hi]` as a range of `A`'s cells, checked against it. `ArrRef.slice` is the range, so the
cells a slice denotes are the ones `slice_inRange` and `disjoint_of_range` reason about.
-- ref: `Paralever/Lib/ArrRef.lean`; `docs/prl.md` § Slices -/
def Env.subRange (E : Env) (nm : String) (r : ArrRef) (lo : Exp) (hi : Option Exp) :
    Except Diag.Diagnostic ArrRef := do
  let a ← E.foldNat lo
  let b ← match hi with | some h => E.foldNat h | none => pure r.len
  if b ≤ a then
    .error (diag Diag.p110 s!"'{nm}[{a}..{b}]' has no cells"
      (notes := ["a range is half-open, so 'lo..hi' needs lo < hi"]))
  else if r.len < b then
    .error (diag Diag.p110 s!"'{nm}[{a}..{b}]' runs past {nm}, which has {r.len} cells")
  else pure (r.slice a b)

/-- One subscript of a flat range: a computed index gives the data-dependent form, confined to the
range by `ArrRef.addr_mem_cells`, and a constant one a literal address. -/
def Env.atIndex (E : Env) (nm : String) (r : ArrRef) (i : Exp) :
    Except Diag.Diagnostic Place := do
  if i.dynamic then pure (.dyn r (← E.aexp i))
  else do
    let k ← E.foldNat i
    if k < r.len then pure (.fixed (r.base + k))
    else .error (diag Diag.p104 s!"'{nm}[{k}]' is outside {nm}, which has {r.len} cells")

/-- A subscript of a declared buffer, which is where a shape is honoured: `A[i, j]` is row-major,
and a computed subscript must be the only one. -/
def Env.cellOf (E : Env) (nm : String) (idx : List Exp) : Except Diag.Diagnostic Place := do
  let p ← E.buf? nm
  if idx.any Exp.dynamic then
    match idx with
    | [e] => do pure (.dyn p.ref (← E.aexp e))
    | _   => .error (diag Diag.p105 "a computed subscript must be the only one"
        (notes := [s!"{nm}[%r] indexes {nm} flat, and wraps on its {p.toBuf.size} cells"]))
  else do
    let ids ← idx.mapM E.foldNat
    if p.toBuf.inRange ids then pure (.fixed (E.layout.at nm ids))
    else .error (diag Diag.p104 s!"{nm}{ids} is outside {nm}, which has shape {p.shape}")

/-- Resolve an address. A subscript mentioning a register gives the data-dependent form, confined to
its array by `ArrRef.addr_mem_cells` — and when the array is a slice, that bound is the slice's
cells rather than the whole buffer's, which is what makes a computed index parallelizable. -/
def Env.place (E : Env) : Addr → Except Diag.Diagnostic Place
  | .raw e => do pure (.fixed (← E.foldNat e))
  | .part nm lo hi i => do
      let (r, _) ← E.rangeOf nm
      let a ← E.foldNat lo
      let sub ← E.subRange nm r lo hi
      E.atIndex s!"{nm}[{a}..{a + sub.len}]" sub i
  -- a slice is flat and takes exactly one subscript, whatever its buffer's shape
  | .cell nm [i] => match E.slices.lookup nm with
      | some sl => E.atIndex nm sl.ref i
      | none    => E.cellOf nm [i]
  | .cell nm idx => match E.slices.lookup nm with
      | some sl => .error (diag Diag.p104
          s!"'{nm}' is a slice of {sl.parent}, so it takes one subscript"
          (notes := [s!"it is {sl.ref.len} cells counted flat, whatever {sl.parent}'s shape"]))
      | none    => E.cellOf nm idx

/-! ## Declarations

Positional, because `free` is. With no `at` a buffer goes where the previous one ended (`alloc`'s
placement); with an `at` it is checked against every *live* buffer. `free` ends a lifetime, and
returns the space when the buffer is the most recent one placed. -/

/-- The live buffer this one would overlap. -/
private def clash (E : Env) (p : Placed) : Option Diag.Diagnostic :=
  (E.layout.bufs.find? (fun q =>
      !E.dead.contains q.name &&
      !(decide (q.base + q.toBuf.size ≤ p.base) || decide (p.base + p.toBuf.size ≤ q.base)))).map
    (fun q => diag Diag.p103
      s!"'{p.name}' at {p.base}..{p.base + p.toBuf.size} overlaps live '{q.name}' at \
{q.base}..{q.base + q.toBuf.size}")

/-- `n` values from the input, in order. -/
private def readCells (inp : Input) : Nat → Except Diag.Diagnostic (List Int × Input)
  | 0     => .ok ([], inp)
  | k + 1 => do
      let (w, rest) ← Input.word inp
      let v ← intOfWord w
      let (vs, rest') ← readCells rest k
      pure (v :: vs, rest')

def Env.addDecl (E : Env) : Decl → Except Diag.Diagnostic Env
  | .const x e => do
      let v ← E.fold e
      pure { E with consts := (x, v) :: E.consts }
  -- `assignRegs` owns register indices, so a `reg` statement adds nothing here
  | .reg _ _ => pure E
  -- a view: no cells are placed, so there is nothing to check against the allocator
  | .slice nm parent lo hi => do
      if (E.layout.find? nm).isSome || (E.slices.lookup nm).isSome then
        .error (diag Diag.p102 s!"'{nm}' is declared twice")
      else do
        let (r, root) ← E.rangeOf parent
        let sub ← E.subRange parent r lo hi
        pure { E with slices := (nm, ⟨root, sub⟩) :: E.slices }
  | .buf nm shape init at? => do
      let dims ← shape.mapM E.foldNat
      -- an `input` initializer consumes, so this yields the environment the next declaration sees
      let (vals, E) ← (match init with
        | .data es   => do pure (Paralever.data (← es.mapM E.fold), E)
        | .full e    => do pure (Paralever.full (← E.fold e), E)
        | .zeros     => pure (Paralever.zeros, E)
        | .ones      => pure (Paralever.ones, E)
        | .eye       => pure (Paralever.eye, E)
        | .arange    => pure (Paralever.arange, E)
        | .str s     => pure (Paralever.str s, E)
        | .input     => do
            let (xs, rest) ← readCells E.inp (cells dims)
            pure (Paralever.data xs, { E with inp := rest })
        | .inputStr  => do
            let (l, rest) ← Input.line E.inp
            pure (Paralever.str l, { E with inp := rest })
        : Except Diag.Diagnostic (Init × Env))
      let b := buf nm dims vals
      if (E.layout.find? nm).isSome then
        .error (diag Diag.p102 s!"'{nm}' is declared twice"
          (hints := [s!"to reuse its cells, 'free {nm}' first"]))
      else do
        let base ← match at? with
          | none   => pure E.next
          | some e => E.foldNat e
        let p : Placed := ⟨b, base⟩
        match clash E p with
        | some d => .error d
        | none =>
            if b.init.length > b.size then
              .error (diag Diag.p104
                s!"'{nm}' has {b.size} cells but {b.init.length} initial values")
            else pure { E with
              layout := ⟨E.layout.bufs ++ [p]⟩, next := max E.next (base + b.size) }

/-- End a buffer's lifetime. The space is returned to the allocator when this buffer is the most
recent one placed, which makes `buf`/`free` a stack; freeing out of order ends the name's scope and
leaves the hole. -/
def Env.freeBuf (E : Env) (nm : String) : Except Diag.Diagnostic Env := do
  let p ← E.buf? nm
  -- every view of it leaves scope with it, so a slice cannot outlive the cells it names
  pure { E with dead := nm :: E.dead, next := p.release E.next,
                slices := E.slices.filter (fun s => s.2.parent != nm) }

/-- A nested body may not read input. A `parallel` thread and a `parfor` index have no order
between them, and an `if` or `while` body may run any number of times, so in all four the number of
values consumed is not a property of the program text. Detected by the cursor having moved. -/
private def noConsume (E E' : Env) (what : String) : Except Diag.Diagnostic Unit :=
  if E'.inp.length == E.inp.length then .ok ()
  else .error (diag Diag.p108 s!"'input' cannot be read inside {what}"
    (hints := ["read the values before the block and pass them in registers"]))

/-- Refuse a `slice` name where only a re-readable spelling will do. A slice is erased once the
file compiles, so `to-prl` cannot write it back and a printed program mentioning one would not read
as itself. -- ref: `docs/print.md` § The surface form -/
def Env.noSlice (E : Env) (nm : String) : Except Diag.Diagnostic Unit :=
  match E.slices.lookup nm with
  | none    => .ok ()
  | some sl =>
      .error (diag Diag.p111 s!"'{nm}' is a slice, and 'print' has no spelling for one"
        (notes := [s!"'{nm}' names the {sl.ref.len} cells at {sl.ref.base}, which belong to \
'{sl.parent}'"])
        (hints := [s!"print '{sl.parent}', or the cell by its own name"]))

/-- One `print` argument, resolved against the declarations in scope. A bare name is the *whole*
buffer — the one place in the language where a name without a subscript is not a cell — because
`print k` is how a reader asks to see `k`. A `const` under the same spelling is its value.
-- ref: `docs/print.md` § The surface form -/
def Env.printItem (E : Env) : PrintArg → Except Diag.Diagnostic PrintItem
  | .text t => pure (.text t)
  | .exp e  => do pure (.exp (← E.aexp e))
  | .addr (.raw e) => do let l ← E.foldNat e; pure (.cell s!"[{l}]" [] l)
  | .addr (.cell nm []) =>
      match E.consts.lookup nm with
      | some v => pure (.exp (.lit v))
      | none   => do let _ ← E.noSlice nm; let p ← E.buf? nm; pure (.buf nm p.shape p.base)
  | .addr (.cell nm idx) => do
      let _ ← E.noSlice nm
      match ← E.place (.cell nm idx) with
      | .fixed l   => pure (.cell nm (← idx.mapM E.foldNat) l)
      | .dyn ar ix => pure (.at nm ar ix)
  | .addr (.part nm _ _ _) => do
      let _ ← E.noSlice nm
      .error (diag Diag.p111 s!"'{nm}[lo..hi][i]' has no spelling as a print argument"
        (hints := [s!"print the cell by its own name, '{nm}[i]'"]))

/-! ## Statements -/

/-- Where a statement sits. A `for`, `if` or `while` body is spliced into the chain that encloses
it, so it is a `.block` and not a new thread — which is why a `synchronize` is legal there and
refused only under a `parallel`. -/
inductive Site where
  | file | block | thread
  deriving BEq, Repr

/-- The site a `for`, `if` or `while` body sits in: inside the file's own chain it becomes a block,
and inside a thread it stays one. -/
def Site.inner : Site → Site
  | .file => .block
  | s     => s

/-! ## Rolling a nest

A `for`/`parfor` nest over more than `Roll.maxUnroll` points is carried as a `ParProg.loop` instead
of being written out: the term is the size it would be at four iterations, and `wfB` decides the
subscript maps rather than the iteration space. Below the threshold nothing changes, so every
pinned term in `Examples/` and `Test/` keeps its shape.

Every step may fail, and a failure is a **fallback, not an error** — the unrolled route still
accepts the program. So the recognizer returns `Option` throughout. -- ref: `docs/loops.md` -/

/-- The perfect nest a statement opens: one level per loop, with the name the source gave it, and
the innermost body. Descent stops at a *named* `parfor`, whose label a nest has nowhere to carry,
and at a size that does not fold — which is how a non-rectangular nest (`for j in i`) is refused,
since the sizes are folded in the environment the nest starts in. -/
private partial def peelLevels (E : Env) (base : Reg) (k : Nat) (s : Stmt) :
    Option (List (String × Roll.Level) × List Stmt) :=
  let go (i : String) (n : Exp) (body : List Stmt) (par : Bool) :
      Option (List (String × Roll.Level) × List Stmt) := do
    let sz ← (E.foldNat n).toOption
    let lvl : String × Roll.Level := (i, ⟨base + k, sz, 0, 1, par⟩)
    match body with
    | [b] => do
        let (ls, inner) ← peelLevels E base (k + 1) b
        pure (lvl :: ls, inner)
    | _   => pure ([lvl], body)
  match s with
  | .forIn i n body       => go i n body false
  | .parfor i n body none => go i n body true
  | _                     => some ([], [s])

/-- A subscript as a linear form over the nest's coordinates. A register in a subscript is a
heap-dependent address and has no form here — `Examples/Language/scatter.prl`'s shape, which stays
refused. -/
private def linOf (E : Env) (ivs : List (String × Nat)) (d : Nat) : Exp → Option Roll.Lin
  | .num n   => some (Roll.Lin.const d n)
  | .name x  =>
      match ivs.lookup x with
      | some k => some (Roll.Lin.coord d k)
      | none   => (E.consts.lookup x).map (Roll.Lin.const d)
  | .len x   => (E.lenOf x).toOption.map (fun n => Roll.Lin.const d (Int.ofNat n))
  | .add a b => do pure (Roll.Lin.add (← linOf E ivs d a) (← linOf E ivs d b))
  | .sub a b => do pure (Roll.Lin.sub (← linOf E ivs d a) (← linOf E ivs d b))
  | .mul a b => do Roll.Lin.mul (← linOf E ivs d a) (← linOf E ivs d b)
  | _        => none

/-- The access a subscript names: the buffer's base and extent, with the subscript collapsed
row-major against its shape — the same collapse `Layout.offsetOf` performs on a constant one, so a
rolled access addresses the cell the unrolled one would. A slice has no shape of its own and is not
rolled. -/
private def accessOf (E : Env) (ivs : List (String × Nat)) (d : Nat)
    (nm : String) (idx : List Exp) : Option Nest.AffAccess := do
  guard (E.slices.lookup nm).isNone
  let p ← (E.buf? nm).toOption
  guard (idx.length == p.toBuf.shape.length)
  let ls ← idx.mapM (linOf E ivs d)
  Roll.affAccess? p.base p.toBuf.size (Roll.rowMajor d p.toBuf.shape ls)

/-- One body statement as a `NestStmt`. Three forms and no more: a `print`, a `parallel`, an `if` or
a `while` inside a nest falls back, because `NestStmt` has no branch for an access to hide behind. -/
private def nestStmtOf (E : Env) (ivs : List (String × Nat)) (d : Nat) : Stmt → Option NestStmt
  -- a bare name that names a `const` is a value, not a cell, exactly as in the unrolled route
  | .load r (.cell nm []) =>
      match E.consts.lookup nm with
      | some v => do pure (.st (← (E.reg r).toOption) (.lit v))
      | none   => do pure (.rd (← (E.reg r).toOption) (← accessOf E ivs d nm []))
  | .load r (.cell nm idx)  => do pure (.rd (← (E.reg r).toOption) (← accessOf E ivs d nm idx))
  | .store (.cell nm idx) e => do pure (.wr (← accessOf E ivs d nm idx) (← (E.aexp e).toOption))
  | .set r e                => do pure (.st (← (E.reg r).toOption) (← (E.aexp e).toOption))
  | _                       => none

/-- **A `for`/`parfor` nest, rolled.** `none` falls back to unrolling. -/
private def rollNest (E : Env) (s : Stmt) : Option LoopNest := do
  let (named, body) ← peelLevels E E.nextReg 0 s
  let levels := named.map (fun nl => nl.2)
  guard (Roll.maxUnroll < Paralever.Box.prodN (levels.map (fun l => l.size)))
  let d ← Roll.parPrefix? levels
  let E' := { E with ivRegs := named.map (fun nl => (nl.1, nl.2.iv)) ++ E.ivRegs }
  let coords := named.zipIdx.map (fun (nl, k) => (nl.1, k))
  let bs ← body.mapM (nestStmtOf E' coords levels.length)
  pure (Roll.nestOf levels d bs)

mutual

/-- One statement, and the environment the next one sees. A `for` splices its unrolled iterations
into the enclosing chain rather than nesting a block in it, so the chain `AutoPar.flatten` sees is
the chain that was written. -/
partial def compileStmt (E : Env) (site : Site) :
    Stmt → Except Diag.Diagnostic (List ParProg × Env)
  -- a `slice` is allowed anywhere: it places no cells and ends no lifetime, so being visible to one
  -- thread alone is exactly what it is for — a thread naming the range it owns
  | .decl ds =>
      if site == .file || ds.all (fun d => match d with | .slice .. => true | _ => false) then
        do pure ([], ← ds.foldlM Env.addDecl E)
      else .error (diag Diag.p106 "a declaration belongs at the top level of the program"
        (notes := ["one inside a thread would be visible to that thread alone"])
        (hints := ["'slice h = A[lo..hi]' is allowed here: it names cells rather than placing \
them"]))
  | .free nm =>
      if site == .file then do pure ([], ← E.freeBuf nm)
      else .error (diag Diag.p106 "'free' belongs at the top level of the program")
  | .synchronize =>
      if site == .thread then
        .error (diag Diag.p106 "'synchronize' cannot appear inside a 'parallel' thread"
          (notes := ["it separates phases of a sequential chain, and threads of one fork have no \
barrier between them"]))
      else pure ([.synchronize], E)
  -- erased from the program, so what it observes must not depend on a schedule: inside a thread
  -- the surrounding fork fixes no order, and the value printed would be whichever one ran first
  | .print as =>
      if site == .thread then
        .error (diag Diag.p106 "'print' cannot appear inside a 'parallel' thread"
          (notes := ["a print is erased from the program, so its value is read off the sequential \
run — and threads of one fork have no order between them"])
          (hints := ["print after the block, where the heap it left is what the program means"]))
      else do pure ([.print (← as.mapM E.printItem)], E)
  -- a bare name that names a `const` is a value, not a cell: both are spelled the same way, and
  -- only the environment knows which this is
  | .load r (.cell nm []) =>
      match E.consts.lookup nm with
      | some v => do pure ([.set (← E.reg r) (.lit v)], E)
      | none   => do
          let i ← E.reg r
          match ← E.place (.cell nm []) with
          | .fixed l   => pure ([.load i l], E)
          | .dyn ar ix => pure ([.loadAt i ar ix], E)
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
  -- `%r := input` is the one place an `input` is consumed in statement position
  | .set r .input => do
      let i ← E.reg r
      let (w, rest) ← Input.word E.inp
      pure ([.set i (.lit (← intOfWord w))], { E with inp := rest })
  | .set r e => do pure ([.set (← E.reg r) (← E.aexp e)], E)
  | .par ts nm => do
      let bodies ← ts.mapM fun t => do
        let (ss, E') ← compileStmts E .thread t
        noConsume E E' "a 'parallel' thread"
        pure (ParProg.block ss)
      pure ([nm.elim id ParProg.label (.par bodies)], E)
  -- the iterations run in order, so the cursor carries across them; `consts` is restored each
  -- round so the loop variable does not accumulate
  | .forIn i n body => do
      match rollNest E (.forIn i n body) with
      | some nst => pure ([.loop nst], E)
      | none => do
      let k ← E.foldNat n
      let (parts, E') ← (List.range k).foldlM
        (fun (acc : List ParProg × Env) j => do
          let (ss, Ej) ← compileStmts { acc.2 with consts := (i, Int.ofNat j) :: E.consts }
                            site.inner body
          pure (acc.1 ++ ss, { Ej with consts := E.consts, slices := E.slices }))
        ([], E)
      pure (parts, E')
  | .parfor i n body nm => do
      -- the outermost level's label survives, so a named `parfor` keeps the name a report prints
      match rollNest E (.parfor i n body none) with
      | some nst => pure ([nm.elim id ParProg.label (.loop nst)], E)
      | none => do
      let k ← E.foldNat n
      let bodies ← (List.range k).mapM fun j => do
        let (ss, E') ← compileStmts { E with consts := (i, Int.ofNat j) :: E.consts } .thread body
        noConsume E E' "a 'parfor' body"
        pure (ParProg.block ss)
      pure ([nm.elim id ParProg.label (.par bodies)], E)
  | .ifElse c t e => do
      let (ts, Et) ← compileStmts E site.inner t
      noConsume E Et "an 'if' branch"
      let (es, Ee) ← compileStmts E site.inner e
      noConsume E Ee "an 'else' branch"
      pure ([.ifElse (← E.aexp c) (ParProg.block ts) (ParProg.block es)], E)
  | .whileIn c n body => do
      let (ss, E') ← compileStmts E site.inner body
      noConsume E E' "a 'while' body"
      pure ([ParProg.whileAtMost (← E.foldNat n) (← E.aexp c) (ParProg.block ss)], E)
  -- `Expand.expand` runs first and leaves none of these three behind
  | .defn f _ _ => .error (diag Diag.p106 s!"'def {f}' was not written out before lowering")
  | .call f _   => .error (diag Diag.p101 s!"'{f}' was not written out before lowering")
  | .assert _ l _ _ => .error (diag Diag.p106
      s!"'assert {l.callee}(…) == …' was not split off before lowering")

partial def compileStmts (E : Env) (site : Site) :
    List Stmt → Except Diag.Diagnostic (List ParProg × Env)
  | []      => .ok ([], E)
  | s :: ss => do
      let (a, E') ← compileStmt E site s
      let (b, E'') ← compileStmts E' site ss
      pure (a ++ b, E'')

end

/-- One program: every call written out, then lowered. Both sides of an `assert` go through this.
-- ref: `docs/prl.md` § Input -/
def compileOne (f : File) (stdin : String) : Except Diag.Diagnostic Compiled := do
  -- every call is written out first, so a register index is assigned to the program that runs
  -- -- ref: `docs/prl.md` § Functions
  let f ← expand f
  let (ss, E) ← compileStmts
    { regs := assignRegs f, nextReg := freshRegBase f, inp := stdin.toList } .file f.body
  pure ⟨E.layout, ParProg.block ss, E.regs, E.dead, none⟩

/-- Whether a statement is the file's claim. -/
private def isAssert : Stmt → Bool
  | .assert .. => true
  | _          => false

/-- A statement list cut at its first `assert`: what precedes it, the claim, and what follows. -/
private def cutAt :
    List Stmt → Option (List Stmt × Strength × Side × Side × List String × List Stmt)
  | []                      => none
  | .assert st l r ns :: ss => some ([], st, l, r, ns, ss)
  | s :: ss                 => (cutAt ss).map fun (b, st, l, r, ns, a) => (s :: b, st, l, r, ns, a)

/-- **The claim, taken out.** The file becomes two files that differ in one statement: where the
`assert` stood, one holds a call to the left side and the other a call to the right. Everything
else — every declaration, every initializer, every statement before and after — is shared, which
is what makes the two programs start from one heap.
-- ref: `docs/equivalence.md` § Why the surface form is two calls -/
def splitClaim (f : File) :
    Except Diag.Diagnostic (File × Option (File × Strength × Side × Side × List String)) :=
  match cutAt f.body with
  | none => .ok (f, none)
  | some (before, st, l, r, ns, after) =>
      if after.any isAssert then
        .error (diag Diag.p114 "a file states at most one 'assert'"
          (notes := ["a claim compiles the file twice, once with each side; a second claim would be a third and a fourth program"])
          (hints := ["split the file, or write one 'def' that calls the others"]))
      else
        let put := fun (sd : Side) => before ++ [Stmt.call sd.callee sd.args] ++ after
        .ok ({ f with body := put l }, some ({ f with body := put r }, st, l, r, ns))

/-- The cells a claim compares: the named buffers' in the order named, or every live buffer's when
the `on` list was omitted. A name that is not a live buffer is `P101` — at the claim it does not
name memory. -/
def claimCells (L : Layout) (dead bufs : List String) :
    Except Diag.Diagnostic (List String × List Loc) := do
  let names := if bufs.isEmpty then (L.bufs.map (·.name)).filter (fun n => !dead.contains n)
               else bufs
  let cs ← names.mapM fun n =>
    match L.find? n with
    | none =>
        .error (diag Diag.p101 s!"'{n}' is compared by the 'assert' and is not a declared buffer"
          (notes := if L.bufs.isEmpty then ["the file declares no buffers"]
                    else [s!"the file declares: {", ".intercalate (L.bufs.map (·.name))}"])
          (hints := ["'on' names buffers; omit it to compare every one of them"]))
    | some p =>
        if dead.contains n then
          .error (diag Diag.p101 s!"'{n}' is compared by the 'assert' and was freed"
            (notes := ["a freed buffer's cells belong to whatever was placed on them next"])
            (hints := [s!"compare '{n}' before the 'free', or name the buffer that holds the answer"]))
        else .ok ((List.range p.toBuf.size).map (fun k => p.base + k))
  pure (names, cs.flatten)

/-- **The registers a claim compares**, for `assertParSeq`: both sides' written registers. A
register neither side writes holds `ρ r` in both outcomes, so leaving it out loses nothing, and
deriving the list means a file cannot name the wrong set. A `.heap` claim compares none.
-- ref: `docs/equivalence.md` § What `assertParSeq` adds -/
def claimRegs : Strength → ParProg → ParProg → List Reg
  | .heap,   _, _ => []
  | .parSeq, p, q =>
      ((ParProg.regFootprint p).writes ++ (ParProg.regFootprint q).writes).eraseDups

/-- **Compile a file**, with the text its `input` forms draw from. The default is empty, so a
program with no `input` compiles exactly as before and no caller has to supply a stream.

A file with an `assert` is compiled twice. The left side is the `Compiled`'s own program, so every
command and every theorem that reads one reads the left program and nothing changed for a file
without a claim. -/
def compile (f : File) (stdin : String := "") : Except Diag.Diagnostic Compiled := do
  let (fl, claim?) ← splitClaim f
  let c ← compileOne fl stdin
  match claim? with
  | none => pure c
  | some (fr, st, l, r, bufs) => do
      let c' ← compileOne fr stdin
      let (names, cells) ← claimCells c.layout c.dead bufs
      let cl : Claim :=
        ⟨l.callee, r.callee, c'.prog, names, cells, st, claimRegs st c.prog c'.prog⟩
      pure { c with claim := some cl }

/-- **Read and compile `.prl` text.** -/
def ofString (src : String) (stdin : String := "") : Except Diag.Diagnostic Compiled := do
  compile (← parse src) stdin

end Paralever.Lang
