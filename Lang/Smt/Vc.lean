import Lang.Core.Prog
import Lang.Smt.Ast

/-! # The independence obligation, as an SMT query

`wfB` reads a footprint off the syntax, so a computed address contributes every cell of its buffer
and two threads that provably touch different cells are refused (`docs/block-ir.md`). This file
emits the obligation *symbolically* instead: a thread's address is an expression, and the fork is
independent exactly when no two threads' expressions can denote one cell.

Registers are substituted away, so the only unknown is a value read from the heap. What survives
substitution and folding is sent to a solver; what folds to a literal is decided here.

Rationale, the encoding table, and the trust boundary: `docs/smt-vc.md`. -/

namespace Paralever.Smt

open Paralever Paralever.Lang

/-! ## Symbolic values -/

/-- A value a thread computes, with every register substituted away. Mirrors `AExp` except that
`reg` becomes `opaque k` — a value read from memory, which symbolic evaluation cannot determine.
The type is the record that substitution has happened. -/
inductive Sym where
  | lit    : Int → Sym
  | opaque : Nat → Sym
  | add    : Sym → Sym → Sym
  | sub    : Sym → Sym → Sym
  | mul    : Sym → Sym → Sym
  | min    : Sym → Sym → Sym
  | max    : Sym → Sym → Sym
  | div    : Sym → Sym → Sym
  | lt     : Sym → Sym → Sym
  | eq     : Sym → Sym → Sym
  | not    : Sym → Sym
  deriving Repr, Inhabited, BEq

namespace Sym

/-- Evaluate the closed part. A thread whose index folds to a literal needs no solver, which is
what turns an unrolled `parfor` into concrete cells. The cases agree with `AExp.eval`. -/
partial def fold : Sym → Sym
  | .lit n    => .lit n
  | .opaque k => .opaque k
  | .add a b  => bin (· + ·) .add a b
  | .sub a b  => bin (· - ·) .sub a b
  | .mul a b  => bin (· * ·) .mul a b
  | .min a b  => bin (fun x y => if x ≤ y then x else y) .min a b
  | .max a b  => bin (fun x y => if x ≤ y then y else x) .max a b
  | .div a b  => bin (· / ·) .div a b
  | .lt a b   => bin (fun x y => if x < y then 1 else 0) .lt a b
  | .eq a b   => bin (fun x y => if x = y then 1 else 0) .eq a b
  | .not a    => match a.fold with
      | .lit n => .lit (if n = 0 then 1 else 0)
      | a'     => .not a'
where
  bin (f : Int → Int → Int) (k : Sym → Sym → Sym) (a b : Sym) : Sym :=
    match a.fold, b.fold with
    | .lit x, .lit y => .lit (f x y)
    | a',     b'     => k a' b'

/-- The value at an assignment of the unknowns. What makes a `sat` answer self-certifying: the
collision it claims is recomputed here, in Lean, rather than taken on the solver's word. The cases
agree with `AExp.eval`. -/
partial def evalWith (m : Nat → Int) : Sym → Int
  | .lit n    => n
  | .opaque k => m k
  | .add a b  => a.evalWith m + b.evalWith m
  | .sub a b  => a.evalWith m - b.evalWith m
  | .mul a b  => a.evalWith m * b.evalWith m
  | .min a b  => let x := a.evalWith m; let y := b.evalWith m; if x ≤ y then x else y
  | .max a b  => let x := a.evalWith m; let y := b.evalWith m; if x ≤ y then y else x
  | .div a b  => a.evalWith m / b.evalWith m
  | .lt a b   => if a.evalWith m < b.evalWith m then 1 else 0
  | .eq a b   => if a.evalWith m = b.evalWith m then 1 else 0
  | .not a    => if a.evalWith m = 0 then 1 else 0

/-- The SMT-LIB term. Lean's `/` on `Int` is Euclidean, which is SMT-LIB's `div`, so only the
division-by-zero convention needs pinning. -- ref: `docs/smt-vc.md` § The encoding -/
partial def toSx : Sym → Sx
  | .lit n    => .int n
  | .opaque k => .atom (Query.unknownName k)
  | .add a b  => .app "+" [a.toSx, b.toSx]
  | .sub a b  => .app "-" [a.toSx, b.toSx]
  | .mul a b  => .app "*" [a.toSx, b.toSx]
  | .min a b  => .app "ite" [.app "<=" [a.toSx, b.toSx], a.toSx, b.toSx]
  | .max a b  => .app "ite" [.app "<=" [a.toSx, b.toSx], b.toSx, a.toSx]
  | .div a b  => .app "ite" [.app "=" [b.toSx, .int 0], .int 0, .app "div" [a.toSx, b.toSx]]
  | .lt a b   => .app "ite" [.app "<" [a.toSx, b.toSx], .int 1, .int 0]
  | .eq a b   => .app "ite" [.app "=" [a.toSx, b.toSx], .int 1, .int 0]
  | .not a    => .app "ite" [.app "=" [a.toSx, .int 0], .int 1, .int 0]

end Sym

/-! ## Symbolic addresses -/

/-- A cell a thread touches: one known cell, or `A[i]` for a computed `i`. -/
inductive SAddr where
  | fixed : Loc → SAddr
  | at    : ArrRef → Sym → SAddr
  deriving Repr, Inhabited, BEq

namespace SAddr

/-- Fold the index, and turn a computed address with a literal index into the cell it names. This is
where an unrolled `parfor` stops needing a solver. -/
def norm : SAddr → SAddr
  | .fixed l => .fixed l
  | .at a i  => match i.fold with
      | .lit n => .fixed (a.addr n)
      | i'     => .at a i'

/-- `a.base + i.toNat % max a.len 1` — `ArrRef.addr`, written out. The `mod` is reproduced exactly:
the wrap is the semantics, so no in-range premise is added. -/
def toSx : SAddr → Sx
  | .fixed l => .nat l
  | .at a i  =>
      .app "+" [.nat a.base,
        .app "mod" [.app "ite" [.app "<" [i.toSx, .int 0], .int 0, i.toSx],
                    .nat (Nat.max a.len 1)]]

/-- The cell this address names at an assignment of the unknowns. -/
def evalWith (m : Nat → Int) : SAddr → Loc
  | .fixed l => l
  | .at a i  => a.addr (i.evalWith m)

/-- The buffer and index as text, for a report. -/
def render : SAddr → String
  | .fixed l => s!"[{l}]"
  | .at a i  => s!"@{a.base}+{a.len}[{repr i}]"

end SAddr

/-- Where an unknown came from. A query is unreadable without this: `u0` means nothing, but "the
value read from `idx[0]`" is the fact a reader needs to state an assumption about it. Rendered with
the layout's names by the reporting layer, which is why this is data and not a string. -/
inductive Origin where
  /-- A `load` from a cell the syntax names. -/
  | cell     : Loc → Origin
  /-- A `loadAt` whose cell is itself computed, so only the buffer is known. -/
  | computed : ArrRef → Origin
  /-- A register with no assignment before its use, or one assigned inside a branch that may not
  have run: unknown for every register file, as `wfB`'s answer is. -/
  | reg      : Reg → Origin
  deriving Repr, Inhabited

/-- One thread's symbolic footprint: the same two lists `Footprint` carries, with expressions in
place of locations. -/
structure SFootprint where
  reads  : List SAddr := []
  writes : List SAddr := []
  deriving Repr, Inhabited

namespace SFootprint

def empty : SFootprint := {}

def union (f g : SFootprint) : SFootprint :=
  ⟨f.reads ++ g.reads, f.writes ++ g.writes⟩

def unionAll : List SFootprint → SFootprint
  | []      => empty
  | f :: fs => union f (unionAll fs)

end SFootprint

/-! ## Walking a thread

Registers are thread-private (`Lang/Core/Prog.lean`), so one walk per thread, each from the register
file its fork was entered with. A register never assigned is a fresh unknown rather than zero, which
keeps the answer valid for every register file — as `wfB`'s is. -/

/-- The substitution: what each register holds, and the next unused unknown. -/
structure Env where
  regs  : List (Reg × Sym) := []
  fresh : Nat := 0
  /-- Newest first; `obligations` reverses it. -/
  origins : List (Nat × Origin) := []
  deriving Repr, Inhabited

namespace Env

/-- A new unknown, for a value symbolic evaluation cannot determine, and where it came from. -/
def newUnknown (E : Env) (o : Origin) : Sym × Env :=
  (.opaque E.fresh, { E with fresh := E.fresh + 1, origins := (E.fresh, o) :: E.origins })

def setReg (E : Env) (r : Reg) (v : Sym) : Env := { E with regs := (r, v) :: E.regs }

/-- `E`'s registers, but `F`'s unknown counter. Entering a thread or a branch restores the register
file it was given while keeping unknowns globally numbered, so no two loads share a name. -/
def keep (E F : Env) : Env := { E with fresh := F.fresh, origins := F.origins }

/-- What a register holds. An unmentioned register is an unknown, allocated on first use. -/
def getReg (E : Env) (r : Reg) : Sym × Env :=
  match E.regs.lookup r with
  | some v => (v, E)
  | none   => let (v, E') := E.newUnknown (.reg r); (v, E'.setReg r v)

/-- Substitute the registers out of an expression. -/
partial def subst (E : Env) : AExp → Sym × Env
  | .lit n   => (.lit n, E)
  | .reg r   => E.getReg r
  | .add a b => bin .add a b
  | .sub a b => bin .sub a b
  | .mul a b => bin .mul a b
  | .min a b => bin .min a b
  | .max a b => bin .max a b
  | .div a b => bin .div a b
  | .lt a b  => bin .lt a b
  | .eq a b  => bin .eq a b
  | .not a   => let (x, E') := E.subst a; (.not x, E')
where
  bin (k : Sym → Sym → Sym) (a b : AExp) : Sym × Env :=
    let (x, E') := E.subst a
    let (y, E'') := E'.subst b
    (k x y, E'')

end Env

/-- Registers a statement may assign. Needed at an `ifElse`, where which branch ran is unknown, so
anything either branch assigns becomes unknown afterwards. -/
partial def assignedRegs : ParProg → List Reg
  | .load r _      => [r]
  | .store _ _     => []
  | .set r _       => [r]
  | .seq a b       => assignedRegs a ++ assignedRegs b
  -- a fork hands back the register file it was given (`execPar`), so its threads assign nothing
  | .par _         => []
  | .label _ s     => assignedRegs s
  | .loadAt r _ _  => [r]
  | .storeAt _ _ _ => []
  | .ifElse _ t e  => assignedRegs t ++ assignedRegs e
  | .synchronize   => []
  | .print _       => []
  | .loop _        => []

/-! ## The obligation at one fork -/

/-- What is known about one `parallel` block, before any solver runs. -/
inductive Status where
  /-- Every pair was decided here: the threads are independent, no solver needed. -/
  | independent : Status
  /-- Two threads touch one *known* cell. `wfB` sees this too; it is a race, not a gap. -/
  | collides : Loc → Status
  /-- What is left for a solver: unsatisfiable means independent. The pairs are kept beside the
  query so a `sat` model can be attributed to the two cells it collides. -/
  | query : Query → List (SAddr × SAddr) → Status
  deriving Repr, Inhabited

/-- One fork's obligation. -/
structure Vc where
  /-- The enclosing `label`, or `fork N` in traversal order. -/
  name    : String
  threads : Nat
  status  : Status
  /-- Where each `uN` in the query came from, lowest first. -/
  origins : List (Nat × Origin) := []
  /-- Whether a thread's footprint was **widened** rather than computed — which happens at an
  `ifElse`, where both branches contribute although only one runs. A collision between widened
  footprints is a possibility, not a race, and the report must not call it one. -/
  approx  : Bool := false
  deriving Repr, Inhabited

/-- The pairs Bernstein requires to differ: W∩W, W∩R and R∩W. There is no R∩R clause — shared reads
are allowed. -- ref: `Paralever/Core/Access.lean` -/
def crossPairs (f g : SFootprint) : List (SAddr × SAddr) :=
  (f.writes.flatMap fun a => g.writes.map fun b => (a, b))
    ++ (f.writes.flatMap fun a => g.reads.map fun b => (a, b))
    ++ (g.writes.flatMap fun a => f.reads.map fun b => (a, b))

/-- Every unordered pair of distinct threads. -/
def threadPairs : List SFootprint → List (SFootprint × SFootprint)
  | []      => []
  | f :: fs => fs.map (fun g => (f, g)) ++ threadPairs fs

/-- The obligation for one fork. A pair of known cells is decided here — that is `disjointB`'s job
and it is already exact — so only a pair with a computed address reaches the solver. -/
def obligationOf (unknowns : Nat) (origins : List (Nat × Origin)) (approx : Bool) (name : String)
    (fs : List SFootprint) : Vc :=
  let pairs := (threadPairs fs).flatMap (fun (f, g) => crossPairs f g)
  let norm  := pairs.map (fun (a, b) => (a.norm, b.norm))
  let hit   := norm.findSome? fun
    | (.fixed l, .fixed m) => if l == m then some l else none
    | _                    => none
  match hit with
  | some l => ⟨name, fs.length, .collides l, origins, approx⟩
  | none   =>
      let open' := norm.filter fun
        | (.fixed _, .fixed _) => false
        | _                    => true
      if open'.isEmpty then ⟨name, fs.length, .independent, origins, approx⟩
      else
        let disj := open'.map fun (a, b) => Sx.app "=" [a.toSx, b.toSx]
        let notes := [ s!"paralever: independence of '{name}' ({fs.length} threads)",
                       "unsat means the threads touch pairwise-disjoint cells (Bernstein)" ]
        let q : Query := { unknowns := unknowns, goal := Sx.orAll disj, notes := notes }
        ⟨name, fs.length, .query q open', origins, approx⟩

/-! ## Walking a program -/

private structure St where
  env  : Env := {}
  vcs  : List Vc := []       -- in reverse traversal order
  next : Nat := 0            -- names an unlabelled fork
  /-- Set once a branch has widened a footprint; see `Vc.approx`. -/
  wide : Bool := false
  deriving Inhabited

mutual

/-- One statement's symbolic footprint, the environment after it, and every fork inside it. -/
private partial def walk (lbl : String) (S : St) : ParProg → SFootprint × St
  | .load r l =>
      let (v, E) := S.env.newUnknown (.cell l)
      (⟨[.fixed l], []⟩, { S with env := E.setReg r v })
  | .store l _ => (⟨[], [.fixed l]⟩, S)
  | .set r e =>
      let (v, E) := S.env.subst e
      (.empty, { S with env := E.setReg r v })
  | .seq a b =>
      let (fa, S') := walk lbl S a
      let (fb, S'') := walk lbl S' b
      (fa.union fb, S'')
  | .par ss =>
      -- each thread starts from this register file and its updates are discarded (`execPar`)
      -- `wide` is reset so it reports *this* fork's threads, and restored so a branch outside the
      -- fork does not taint it either way
      let (fs, S') := walkThreads lbl { S with wide := false } ss
      let name := if lbl.isEmpty then s!"fork {S'.next}" else lbl
      let vc := obligationOf S'.env.fresh S'.env.origins.reverse S'.wide name fs
      (SFootprint.unionAll fs,
        { S' with vcs := vc :: S'.vcs, next := S'.next + 1, wide := S.wide })
  | .label nm s => walk nm S s
  | .loadAt r a e =>
      let (i, E) := S.env.subst e
      let (v, E') := E.newUnknown (.computed a)
      (⟨[.at a i], []⟩, { S with env := E'.setReg r v })
  | .storeAt a e _ =>
      let (i, E) := S.env.subst e
      (⟨[], [.at a i]⟩, { S with env := E })
  | .ifElse _ t e =>
      -- both branches contribute, as in `footprintOf`; a register either assigns becomes unknown
      let (ft, S') := walk lbl { S with wide := true } t
      let (fe, S'') := walk lbl { S' with env := S.env.keep S'.env } e
      let E := (assignedRegs t ++ assignedRegs e).foldl
        (fun E r => let (v, E') := E.newUnknown (.reg r); E'.setReg r v) S''.env
      (ft.union fe, { S'' with env := E })
  | .synchronize => (.empty, S)
  -- erased: a print touches no memory, so it contributes no symbolic address
  | .print _     => (.empty, S)
  | .loop n =>
      -- a nest's cells are the buffer bound `footprintOf` gives it, so the query is the same
      -- approximation `wfB` works with and `wide` records that it is one -- ref: `docs/loops.md`
      (⟨n.footprint.reads.map .fixed, n.footprint.writes.map .fixed⟩, { S with wide := true })

private partial def walkThreads (lbl : String) (S : St) :
    List ParProg → List SFootprint × St
  | []      => ([], S)
  | s :: ss =>
      -- the fork's own register file, not the previous thread's
      let (f, S') := walk lbl S s
      let (fs, S'') := walkThreads lbl { S' with env := S.env.keep S'.env } ss
      (f :: fs, S'')

end

/-- Every `parallel` block in the program, with its obligation, in traversal order. -/
def obligations (p : ParProg) : List Vc := ((walk "" {} p).2).vcs.reverse

end Paralever.Smt
