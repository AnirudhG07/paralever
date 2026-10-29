import Lang.Compile.Input

/-! # `def` — writing the calls out

A call is expanded, not performed: `ParM` has no call constructor and the machine has no stack, so a
`def` is a named piece of program text. `expand` collects the `def`s, checks what can be decided
without knowing a call's arguments, and writes each body out where its call stood — substituting the
arguments and renaming the registers and slices the body declares itself.

Rationale, the parameter kinds, and what a body may not contain: `docs/prl.md` § Functions. -/

namespace Paralever.Lang

/-- A diagnostic under a named rule. The span is left out: the surface AST carries no positions, so
one found after the read names the rule and the reason but not the column.
-- ref: `docs/diagnostics.md` § What is not here yet -/
def diag (c : Diag.Code) (msg : String) (notes : List String := [])
    (hints : List String := []) : Diag.Diagnostic :=
  { code := some c, msg := msg, notes := notes, hints := hints }

/-- A register written as a number names that index wherever it occurs, so it is never renamed. -/
def isNum (s : String) : Bool := !s.isEmpty && s.all Char.isDigit

/-! ## Register tokens

Every `%name` the file writes. `Lower.assignRegs` gives each an index; expansion needs the same list
to rename a body's locals to names the file does not already use. -/

def Exp.regTokens : Exp → List String
  | .num _ | .name _ | .len _ | .input => []
  | .reg r  => [r]
  | .add a b | .sub a b | .mul a b | .div a b | .mod a b | .min a b | .max a b
  | .lt a b | .eq a b => a.regTokens ++ b.regTokens
  | .not a  => a.regTokens

def Addr.regTokens : Addr → List String
  | .raw e     => e.regTokens
  | .cell _ es => es.flatMap Exp.regTokens
  | .part _ lo hi i => lo.regTokens ++ (hi.elim [] Exp.regTokens) ++ i.regTokens

def Arg.regTokens : Arg → List String
  | .exp e => e.regTokens
  | .reg r => [r]

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
  | .synchronize   => []
  | .defn _ ps b   => ps.filterMap (fun p => match p with | .reg x => some x | _ => none)
                        ++ stmtTokens b
  | .call _ as     => as.flatMap Arg.regTokens
  | .assert _ l r _ => l.args.flatMap Arg.regTokens ++ r.args.flatMap Arg.regTokens
  | .print as      => as.flatMap fun
      | .exp e  => e.regTokens
      | .addr a => a.regTokens
      | .text _ => []

def stmtTokens : List Stmt → List String
  | []      => []
  | s :: ss => s.regTokens ++ stmtTokens ss

def threadTokens : List (List Stmt) → List String
  | []      => []
  | t :: ts => stmtTokens t ++ threadTokens ts

end

/-! ## The table -/

/-- A `def`, as expansion uses it. -/
structure Func where
  params : List Param
  body   : List Stmt
  deriving Repr, Inhabited

/-- The `def`s of a file, by name. -/
abbrev Table := List (String × Func)

def Param.nameOf : Param → String
  | .name p | .reg p => p

def Param.isReg : Param → Bool
  | .reg _  => true
  | .name _ => false

def Param.show : Param → String
  | .name p => p
  | .reg p  => "%" ++ p

def Arg.isReg : Arg → Bool
  | .reg _ => true
  | .exp _ => false

/-- The `def`s, and the statements with them taken out. A call may precede the `def` it names,
because the table is complete before any body is written out. -/
def collect : List Stmt → Except Diag.Diagnostic (Table × List Stmt)
  | []      => .ok ([], [])
  | s :: ss => do
      let (fs, rest) ← collect ss
      match s with
      | .defn f ps b =>
          if (fs.lookup f).isSome then
            .error (diag Diag.p102 s!"'{f}' is defined twice"
              (hints := ["give the second one another name"]))
          else .ok ((f, ⟨ps, b⟩) :: fs, rest)
      | _ => .ok (fs, s :: rest)

/-! ## What a body holds

One walk answers the three questions the checks below ask of a `def` body: which calls it makes,
which slices it declares, and whether it holds a statement whose meaning is positional in the file. -/

structure BodyInfo where
  calls  : List (String × List Arg) := []
  slices : List String := []
  /-- A statement a body may not hold, spelled as the diagnostic names it. -/
  bad    : List String := []
  /-- A nested `def`. -/
  defns  : List String := []
  /-- An `assert`, as the two names it compares. -/
  claims : List (String × String) := []

instance : Append BodyInfo where
  append a b := { calls := a.calls ++ b.calls, slices := a.slices ++ b.slices
                , bad := a.bad ++ b.bad, defns := a.defns ++ b.defns
                , claims := a.claims ++ b.claims }

private def declInfo : Decl → BodyInfo
  | .buf nm _ _ _ => { bad := [s!"buf {nm}"] }
  | .const nm _   => { bad := [s!"const {nm}"] }
  | .reg nm _     => { bad := [s!"reg {nm}"] }
  | .slice nm _ _ _ => { slices := [nm] }

mutual

def Stmt.info : Stmt → BodyInfo
  | .load .. | .store .. | .set .. | .synchronize | .print _ => {}
  | .free nm       => { bad := [s!"free {nm}"] }
  | .decl ds       => ds.foldl (fun acc d => acc ++ declInfo d) {}
  | .defn f _ b    => { defns := [f] } ++ stmtsInfo b
  | .call f as     => { calls := [(f, as)] }
  -- both sides are checked as the calls they are, wherever the claim sits
  | .assert _ l r _ => { claims := [(l.callee, r.callee)]
                       , calls  := [(l.callee, l.args), (r.callee, r.args)] }
  | .par ts _      => threadsInfo ts
  | .forIn _ _ b   => stmtsInfo b
  | .parfor _ _ b _ => stmtsInfo b
  | .ifElse _ t e  => stmtsInfo t ++ stmtsInfo e
  | .whileIn _ _ b => stmtsInfo b

def stmtsInfo : List Stmt → BodyInfo
  | []      => {}
  | s :: ss => s.info ++ stmtsInfo ss

def threadsInfo : List (List Stmt) → BodyInfo
  | []      => {}
  | t :: ts => stmtsInfo t ++ threadsInfo ts

end

/-! ## The checks that do not need the arguments

A `def` that is never called is checked too: a call it makes names a `def` that exists, with the
right number of arguments of the right kinds, and no chain of calls closes a cycle. -/

/-- One call, against the `def` it names. -/
def checkCall (fs : Table) (where' : String) (f : String) (args : List Arg) :
    Except Diag.Diagnostic Unit :=
  match fs.lookup f with
  | none =>
      .error (diag Diag.p101 s!"'{f}' is called {where'} and is not defined"
        (notes := if fs.isEmpty then ["the file defines no functions"]
                  else [s!"the file defines: {", ".intercalate (fs.map (·.1))}"])
        (hints := ["a call is 'f(a, b)'; define it with 'def f(x, y) { … }'"]))
  | some fn =>
      if fn.params.length != args.length then
        .error (diag Diag.p112
          s!"'{f}' takes {fn.params.length} arguments and the call {where'} passes {args.length}"
          (notes := [s!"def {f}({", ".intercalate (fn.params.map Param.show)})"]))
      else
        match (fn.params.zip args).find? (fun pa => pa.1.isReg != pa.2.isReg) with
        | none => .ok ()
        | some (p, _) =>
            if p.isReg then
              .error (diag Diag.p112 s!"'{p.show}' of '{f}' is a register, and the call {where'} \
passes a value for it"
                (hints := [s!"pass a register, as '{f}(…, %r, …)'"]))
            else
              .error (diag Diag.p112 s!"'{p.show}' of '{f}' is a name, and the call {where'} \
passes a register for it"
                (notes := ["a register's value is a value, and '%r' alone is the register itself"])
                (hints := [s!"write '{p.show}' as a register parameter, '%{p.show}', or pass a \
value"]))

/-- A `def` body holds statements, and not the ones whose meaning is positional in the file as a
whole: `buf`, `const`, `reg` and `free` place memory and end its lifetime, and would do so once per
call; `input` is consumed in the order the file reads it; a nested `def` would make a name visible
to one body alone. -/
def checkBody (fs : Table) (f : String) (fn : Func) : Except Diag.Diagnostic Unit := do
  let info := stmtsInfo fn.body
  match info.bad with
  | b :: _ =>
      .error (diag Diag.p106 s!"'{b}' cannot appear in a 'def' body"
        (notes := [s!"'{f}' is written out at every call site, so a declaration in it would place \
memory once per call"])
        (hints := ["declare the memory at the top level and pass its name in"]))
  | [] => do
  match info.defns with
  | g :: _ =>
      .error (diag Diag.p106 s!"'def {g}' cannot appear inside 'def {f}'"
        (hints := ["define it at the top level; a call may precede the 'def' it names"]))
  | [] => do
  match info.claims with
  | (l, _) :: _ =>
      .error (diag Diag.p106 s!"'assert {l}(…) == …' cannot appear in a 'def' body"
        (notes := ["each side of an 'assert' is a whole program, and a 'def' body is a statement list inside one"])
        (hints := ["state the claim at the top level of the file"]))
  | [] => do
  if stmtsUseInput fn.body then
    .error (diag Diag.p106 s!"'input' cannot appear in a 'def' body"
      (notes := ["the values a program reads, and the order it reads them in, are fixed by the \
file, and a call site is not"])
      (hints := ["read the values at the top level and pass them in registers"]))
  else do
  let params := fn.params.map Param.nameOf
  match info.slices.find? (fun s => params.contains s) with
  | some s =>
      .error (diag Diag.p102 s!"'slice {s}' in '{f}' has the name of a parameter"
        (hints := [s!"name the slice something else: '{s}' already names what the call passed"]))
  | none => info.calls.forM (fun c => checkCall fs s!"in 'def {f}'" c.1 c.2)

/-- No chain of calls closes a cycle. Expansion would not terminate, and `ParM` is inductive, so a
recursive program has no representation to expand into either. -/
partial def checkAcyclic (fs : Table) : Except Diag.Diagnostic Unit :=
  fs.forM (fun fn => walk [fn.1] fn.1)
where
  walk (stack : List String) (f : String) : Except Diag.Diagnostic Unit :=
    match fs.lookup f with
    | none    => .ok ()
    | some fn => (stmtsInfo fn.body).calls.forM fun c =>
        if stack.contains c.1 then
          .error (diag Diag.p113 s!"'{c.1}' calls itself"
            (notes := [s!"the chain is {" → ".intercalate (stack ++ [c.1])}"])
            (hints := ["a call is written out where it stands, so a recursive one has no end; \
'while c in n' is the language's bounded repetition"]))
        else walk (stack ++ [c.1]) c.1

/-! ## Substitution

What one call does to the body it names: a name parameter is replaced in both roles a name has — as
a value and as the name of cells — and a register parameter in the one role a register has. -/

structure Subst where
  /-- A name parameter, as a value. -/
  vals  : List (String × Exp) := []
  /-- A name parameter whose argument names cells, and the body's own slices renamed. -/
  names : List (String × String) := []
  /-- Register parameters, and the body's own registers renamed. -/
  regs  : List (String × String) := []

namespace Subst

def reg (σ : Subst) (r : String) : String := (σ.regs.lookup r).getD r

/-- A name position. A parameter the call gave a bare name for is that name; one it gave a value for
is refused here, because a value does not name cells. -/
def nameAt (σ : Subst) (nm : String) : Except Diag.Diagnostic String :=
  match σ.names.lookup nm with
  | some n => .ok n
  | none   =>
      if (σ.vals.lookup nm).isSome then
        .error (diag Diag.p112 s!"'{nm}' names cells here, and the call passed a value for it"
          (notes := ["a name parameter takes a buffer, a slice, or a compile-time value, and only \
the first two name cells"])
          (hints := [s!"pass a buffer or a slice for '{nm}'"]))
      else .ok nm

/-- A loop variable shadows a parameter of the same name, as it would a `const`. -/
def shadow (σ : Subst) (nm : String) : Subst :=
  { σ with vals := σ.vals.filter (·.1 != nm), names := σ.names.filter (·.1 != nm) }

end Subst

def Exp.subst (σ : Subst) : Exp → Except Diag.Diagnostic Exp
  | .num n   => .ok (.num n)
  | .name x  => .ok ((σ.vals.lookup x).getD (.name x))
  | .reg r   => .ok (.reg (σ.reg r))
  | .input   => .ok .input
  | .len x   => do pure (.len (← σ.nameAt x))
  | .not a   => do pure (.not (← Exp.subst σ a))
  | .add a b => do pure (.add (← Exp.subst σ a) (← Exp.subst σ b))
  | .sub a b => do pure (.sub (← Exp.subst σ a) (← Exp.subst σ b))
  | .mul a b => do pure (.mul (← Exp.subst σ a) (← Exp.subst σ b))
  | .div a b => do pure (.div (← Exp.subst σ a) (← Exp.subst σ b))
  | .mod a b => do pure (.mod (← Exp.subst σ a) (← Exp.subst σ b))
  | .min a b => do pure (.min (← Exp.subst σ a) (← Exp.subst σ b))
  | .max a b => do pure (.max (← Exp.subst σ a) (← Exp.subst σ b))
  | .lt a b  => do pure (.lt (← Exp.subst σ a) (← Exp.subst σ b))
  | .eq a b  => do pure (.eq (← Exp.subst σ a) (← Exp.subst σ b))

def Addr.subst (σ : Subst) : Addr → Except Diag.Diagnostic Addr
  | .raw e     => do pure (.raw (← Exp.subst σ e))
  | .cell nm es => do pure (.cell (← σ.nameAt nm) (← es.mapM (Exp.subst σ)))
  | .part nm lo hi i => do
      pure (.part (← σ.nameAt nm) (← Exp.subst σ lo)
              (← hi.mapM (Exp.subst σ)) (← Exp.subst σ i))

def Arg.subst (σ : Subst) : Arg → Except Diag.Diagnostic Arg
  | .exp e => do pure (.exp (← Exp.subst σ e))
  | .reg r => .ok (.reg (σ.reg r))

def BufInit.subst (σ : Subst) : BufInit → Except Diag.Diagnostic BufInit
  | .full e  => do pure (.full (← Exp.subst σ e))
  | .data es => do pure (.data (← es.mapM (Exp.subst σ)))
  | i        => .ok i

def Decl.subst (σ : Subst) : Decl → Except Diag.Diagnostic Decl
  | .buf nm shape init at? => do
      pure (.buf nm (← shape.mapM (Exp.subst σ)) (← BufInit.subst σ init)
              (← at?.mapM (Exp.subst σ)))
  | .const nm e => do pure (.const nm (← Exp.subst σ e))
  | .reg nm k   => .ok (.reg nm k)
  | .slice nm src lo hi => do
      pure (.slice ((σ.names.lookup nm).getD nm) (← σ.nameAt src)
              (← Exp.subst σ lo) (← hi.mapM (Exp.subst σ)))

def PrintArg.subst (σ : Subst) : PrintArg → Except Diag.Diagnostic PrintArg
  | .text t => .ok (.text t)
  | .exp e  => do pure (.exp (← Exp.subst σ e))
  | .addr a => do pure (.addr (← Addr.subst σ a))

/-! ## Writing the bodies out -/

/-- The gensym: a counter, and the names it may not produce. -/
structure Gen where
  next  : Nat := 1
  taken : List String := []

abbrev M (α : Type) := StateT Gen (Except Diag.Diagnostic) α

private def ok (x : Except Diag.Diagnostic α) : M α :=
  match x with
  | .ok a    => pure a
  | .error e => throw e

/-- A name the file does not use: `t` becomes `t'1`, `t'2`, …. Both characters are ones `ident`
accepts, so the expanded program is still one a person could have written. -/
partial def fresh (base : String) : M String := do
  let g ← get
  let cand := base ++ "'" ++ toString g.next
  set { g with next := g.next + 1 }
  if g.taken.contains cand then fresh base
  else do modify (fun g' => { g' with taken := cand :: g'.taken }); pure cand

mutual

/-- One statement, with the enclosing substitution applied and every call in it written out. -/
partial def expandStmt (fs : Table) (σ : Subst) : Stmt → M (List Stmt)
  | .load r a      => do pure [.load (σ.reg r) (← ok (Addr.subst σ a))]
  | .store a e     => do pure [.store (← ok (Addr.subst σ a)) (← ok (Exp.subst σ e))]
  | .set r e       => do pure [.set (σ.reg r) (← ok (Exp.subst σ e))]
  | .decl ds       => do pure [.decl (← ds.mapM (fun d => ok (Decl.subst σ d)))]
  | .free nm       => do pure [.free (← ok (σ.nameAt nm))]
  | .synchronize   => pure [.synchronize]
  | .print as      => do pure [.print (← as.mapM (fun a => ok (PrintArg.subst σ a)))]
  | .par ts nm     => do pure [.par (← ts.mapM (expandStmts fs σ)) nm]
  | .forIn i n b   => do
      pure [.forIn i (← ok (Exp.subst σ n)) (← expandStmts fs (σ.shadow i) b)]
  | .parfor i n b nm => do
      pure [.parfor i (← ok (Exp.subst σ n)) (← expandStmts fs (σ.shadow i) b) nm]
  | .ifElse c t e  => do
      pure [.ifElse (← ok (Exp.subst σ c)) (← expandStmts fs σ t) (← expandStmts fs σ e)]
  | .whileIn c n b => do
      pure [.whileIn (← ok (Exp.subst σ c)) (← ok (Exp.subst σ n)) (← expandStmts fs σ b)]
  -- `collect` took the file's own `def`s out, so one reached here is nested
  | .defn f _ _    => throw (diag Diag.p106 s!"'def {f}' belongs at the top level of the program"
      (notes := ["a 'def' inside a block or a thread would name a body that only that block \
could call"])
      (hints := ["define it at the top level; a call may precede the 'def' it names"]))
  -- `splitClaim` took the file's own claim out, so one reached here is nested in a block
  | .assert _ l _ _ => throw (diag Diag.p106
      s!"'assert {l.callee}(…) == …' belongs at the top level of the program"
      (notes := ["each side of an 'assert' is the whole program with that side's body written out, not a statement reached at a point in a run"])
      (hints := ["move the claim to the top level; wrap the surrounding block in a 'def' if both sides need it"]))
  | .call f args   => do
      let args ← args.mapM (fun a => ok (Arg.subst σ a))
      match fs.lookup f with
      | none    => throw (diag Diag.p101 s!"'{f}' is called and not defined")
      | some fn => do
          let σ' ← bindArgs f fn args
          expandStmts fs σ' fn.body

partial def expandStmts (fs : Table) (σ : Subst) : List Stmt → M (List Stmt)
  | []      => pure []
  | s :: ss => do pure ((← expandStmt fs σ s) ++ (← expandStmts fs σ ss))

/-- The substitution one call makes: its arguments for the parameters, and a fresh name for every
register and slice the body declares itself. -/
partial def bindArgs (f : String) (fn : Func) (args : List Arg) : M Subst := do
  let σ₀ ← (fn.params.zip args).foldlM (fun (σ : Subst) (pa : Param × Arg) =>
    match pa.1, pa.2 with
    | .name x, .exp e => pure { σ with
        vals  := (x, e) :: σ.vals
        names := match e with | .name y => (x, y) :: σ.names | _ => σ.names }
    | .name x, .reg r => pure { σ with vals := (x, Exp.reg r) :: σ.vals }
    | .reg x,  .reg r => pure { σ with regs := (x, r) :: σ.regs }
    | _, _ => throw (diag Diag.p112 s!"the call to '{f}' does not match its 'def'"))
    ({} : Subst)
  -- the body's own registers, which no call shares and no caller holds
  let regParams := fn.params.filterMap (fun p => match p with | .reg x => some x | _ => none)
  let locals := (stmtTokens fn.body).eraseDups.filter
                  (fun t => !isNum t && !regParams.contains t)
  let σ₁ ← locals.foldlM (fun (σ : Subst) t => do
    pure { σ with regs := (t, ← fresh t) :: σ.regs }) σ₀
  (stmtsInfo fn.body).slices.eraseDups.foldlM (fun (σ : Subst) s => do
    let s' ← fresh s
    pure { σ with names := (s, s') :: σ.names, vals := (s, Exp.name s') :: σ.vals }) σ₁

end

/-- **Write out every call**, so that what the rest of the compiler sees is a file with no `def` and
no call in it. -/
def expand (f : File) : Except Diag.Diagnostic File := do
  let (fs, body) ← collect f.body
  fs.forM (fun fn => checkBody fs fn.1 fn.2)
  checkAcyclic fs
  (stmtsInfo body).calls.forM (fun c => checkCall fs "at the top level" c.1 c.2)
  let taken := (stmtTokens f.body).eraseDups
  let (body, _) ← (expandStmts fs {} body).run { taken := taken }
  pure { f with body := body }

end Paralever.Lang
