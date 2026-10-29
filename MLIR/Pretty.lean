import MLIR.Parse

/-! # A reader for MLIR custom (pretty) form

`affine.for %i = 0 to 8 { … }` rather than `"affine.for"() ({ … }) {lowerBoundMap = …}`. Every
file written by hand or printed by `mlir-opt` without `--mlir-print-op-generic` is in this form, so
without this module a program from outside is unreadable.

Nothing here is a second AST or a second lowering: each construct is **desugared** to the `Op`
MLIR's own generic printer would have produced, so `Lower`, `Eval`, `Emit` and `Corpus` never learn
that pretty form exists. The desugaring table, the vocabulary and the refusals are
`docs/mlir-pretty.md`. -- ref: `docs/mlir-pretty.md` -/

namespace Paralever.MLIR
namespace Pretty

open P

/-- Map aliases in scope: a top-level `#map = affine_map<…>` is a file-local abbreviation, so it is
substituted on use and never reaches `Op`. -/
abbrev Aliases := List (String × AffMap)

/-- A memref's element type; anything else is its own element type. -/
def eltOf : MTy → MTy
  | .memref _ e => e
  | t           => t

/-- `@name`, quoted or bare. -/
def symName : P String := do
  skipWs
  if ← tryCh '@' then do
    skipWs
    if (← peek) == some '"' then strLit else ident
  else err "expected a symbol name beginning with '@'"

/-- `(d0, …, dₙ₋₁) -> (results)`, the map an index list desugars to. -/
def mapOver (n : Nat) (rs : List AffExp) : AffMap :=
  ⟨(List.range n).map (fun k => "d" ++ toString k), [], rs⟩

/-- A map with no arguments and constant results: what a loop bound becomes. -/
def constMap (ks : List Int) : AffMap := ⟨[], [], ks.map AffExp.const⟩

/-- `index` repeated, the type of a flattened subscript operand list. -/
def indexTys (n : Nat) : List MTy := (List.range n).map (fun _ => MTy.index)

/-! ## Index expressions

MLIR writes the affine expression inline (`%A[%i, %j + 1]`) where generic form carries a `map`
attribute and a flat operand list. The dimensions are therefore discovered while parsing: each SSA
name becomes a dimension at its first use, and the accumulated list is the operand list. A
`symbol(%s)` is read as one more dimension — `Lower.subscript` applies the map to the operands in
order, so where the boundary between dimensions and symbols falls makes no difference to it. -/

/-- The dimension this name stands for, adding it if it is new. -/
def dimOf (v : String) (ds : List String) : AffExp × List String :=
  match ds.findIdx? (· == v) with
  | some k => (.dim k, ds)
  | none   => (.dim ds.length, ds ++ [v])

mutual

partial def idxSum (ds : List String) : P (AffExp × List String) := do
  let (a, ds) ← idxProd ds
  idxSumTail ds a

partial def idxSumTail (ds : List String) (a : AffExp) : P (AffExp × List String) := do
  skipWs
  if ← tryCh '+' then do let (b, ds) ← idxProd ds; idxSumTail ds (.add a b)
  else if (← peek) == some '-' then do
    bump
    let (b, ds) ← idxProd ds
    idxSumTail ds (.sub a b)
  else pure (a, ds)

partial def idxProd (ds : List String) : P (AffExp × List String) := do
  let (a, ds) ← idxAtom ds
  idxProdTail ds a

partial def idxProdTail (ds : List String) (a : AffExp) : P (AffExp × List String) := do
  skipWs
  if ← tryCh '*' then do let (b, ds) ← idxAtom ds; idxProdTail ds (.mul a b)
  else if ← tryKw "floordiv" then do let (b, ds) ← idxAtom ds; idxProdTail ds (.floorDiv a b)
  else if ← tryKw "ceildiv" then do let (b, ds) ← idxAtom ds; idxProdTail ds (.ceilDiv a b)
  else if ← tryKw "mod" then do let (b, ds) ← idxAtom ds; idxProdTail ds (.mod a b)
  else pure (a, ds)

partial def idxAtom (ds : List String) : P (AffExp × List String) := do
  skipWs
  if ← tryCh '(' then do
    let (e, ds) ← idxSum ds
    let _ ← ch ')'
    pure (e, ds)
  else if (← peek) == some '-' then do
    bump
    let (e, ds) ← idxAtom ds
    pure (.sub (.const 0) e, ds)
  else if ← tryKw "symbol" then do
    let _ ← ch '('
    let v ← valueId
    let _ ← ch ')'
    pure (dimOf v ds)
  else if (← peek) == some '%' then do
    let v ← valueId
    pure (dimOf v ds)
  else do
    let n ← natLit
    pure (.const (n : Int), ds)

end

/-- Subscripts up to `]`, the `[` already consumed. -/
partial def idxList (ds : List String) (acc : List AffExp) : P (List AffExp × List String) := do
  skipWs
  if ← tryCh ']' then pure (acc.reverse, ds)
  else do
    let (e, ds) ← idxSum ds
    skipWs
    if ← tryCh ',' then idxList ds (e :: acc)
    else do let _ ← ch ']'; pure ((e :: acc).reverse, ds)

/-! ## Small pieces of the grammar -/

/-- SSA names before the `=`. -/
partial def resultNames (acc : List String) : P (List String) := do
  let v ← valueId
  skipWs
  if (← peek) == some ':' then err "multi-result shorthand '%x:n' is not supported"
  else if ← tryCh ',' then resultNames (v :: acc)
  else pure (v :: acc).reverse

/-- Comma-separated SSA names, however many are there. -/
partial def valueList (acc : List String) : P (List String) := do
  skipWs
  if (← peek) != some '%' then pure acc.reverse
  else do
    let v ← valueId
    skipWs
    if ← tryCh ',' then valueList (v :: acc)
    else pure (v :: acc).reverse

/-- Comma-separated SSA names up to `]`, the `[` already consumed: a non-affine subscript. -/
partial def valueListUntil (close : Char) (acc : List String) : P (List String) := do
  skipWs
  if ← tryCh close then pure acc.reverse
  else do
    let v ← valueId
    skipWs
    if ← tryCh ',' then valueListUntil close (v :: acc)
    else do let _ ← ch close; pure (v :: acc).reverse

/-- A type, or a parenthesised list of them: an op trailer's two halves. -/
partial def typeOrList : P (List MTy) := do
  skipWs
  if ← tryCh '(' then do
    skipWs
    if ← tryCh ')' then pure []
    else do
      let t ← parseType
      let ts ← parseTypeListTail [t]
      pure ts
  else do let t ← parseType; pure [t]

/-- A loop bound that `Lower` can unroll. Everything else is named rather than approximated: the
unrolling needs the trip count, so an operand or a `max` of maps has no number to unroll over. -/
partial def constBound (which : String) : P Int := do
  skipWs
  if (← peek) == some '%' then
    err s!"{which} bound is an operand; only constant bounds are unrolled (docs/mlir-pretty.md)"
  else if (← lookingAt "max") || (← lookingAt "min") then
    err s!"{which} bound is a max/min of affine maps; only constant bounds are unrolled"
  else if (← peek) == some '#' then
    err s!"{which} bound is a map alias applied to operands; only constant bounds are unrolled"
  else if ← lookingAt "affine_map" then
    err s!"{which} bound is an affine map applied to operands; only constant bounds are unrolled"
  else do
    let neg ← tryCh '-'
    let n ← natLit
    pure (if neg then -(n : Int) else (n : Int))

/-- Comma-separated integers in `(…)`, as `affine.parallel`'s bounds and steps are written. -/
partial def constTuple (what : String) (acc : List Int) : P (List Int) := do
  skipWs
  if ← tryCh ')' then pure acc.reverse
  else do
    let k ← constBound what
    skipWs
    if ← tryCh ',' then constTuple what (k :: acc)
    else do let _ ← ch ')'; pure (k :: acc).reverse

/-- The map an `affine.apply` or a bound names: written out, or an alias defined above. -/
def mapRef (al : Aliases) : P AffMap := do
  skipWs
  if ← lookingAt "affine_map" then parseAffineMap
  else if ← tryCh '#' then do
    let nm ← ident
    match al.find? (fun p => p.1 == nm) with
    | some (_, m) => pure m
    | none        => err s!"undefined affine map alias '#{nm}'"
  else err "expected an affine map"

/-- One bound of an `affine.for`: a constant, an operand, or a map applied to operands, optionally
behind `max`/`min` (which MLIR spells as a map with several results). Everything parses; a bound
that is not constant is refused by the lowering, which unrolls and therefore needs the trip count.
-- ref: `docs/mlir-pretty.md` -/
def forBound (al : Aliases) : P (AffMap × List String) := do
  skipWs
  let _ ← tryKw "max"
  let _ ← tryKw "min"
  skipWs
  if (← peek) == some '%' then do
    let v ← valueId
    pure (⟨["d0"], [], [.dim 0]⟩, [v])
  else if (← lookingAt "affine_map") || (← peek) == some '#' then do
    let m ← mapRef al
    let ds ← if ← tryCh '(' then valueListUntil ')' [] else pure []
    let ss ← if ← tryCh '[' then valueListUntil ']' [] else pure []
    pure (m, ds ++ ss)
  else do
    let neg ← tryCh '-'
    let n ← natLit
    pure (constMap [if neg then -(n : Int) else (n : Int)], [])

/-- `fastmath<fast>` and friends: a flag the lowering does not read, kept so nothing is dropped
silently. -/
def optFastmath : P (List (String × MAttr)) := do
  skipWs
  if ← tryKw "fastmath" then do
    let _ ← ch '<'
    let v ← ident
    let _ ← ch '>'
    pure [("fastmath", .str v)]
  else pure []

/-- `{a = 1, b = 2}`, when the op carries an attribute dictionary of its own. -/
def optAttrDict : P (List (String × MAttr)) := do
  skipWs
  if ← tryCh '{' then parseAttrDictTail [] else pure []

/-- Binary `arith` operations: one syntax, `%a, %b : ty`. -/
def binaryOps : List String :=
  [ "arith.addi", "arith.subi", "arith.muli", "arith.divsi", "arith.divui", "arith.remsi"
  , "arith.remui", "arith.maxsi", "arith.minsi", "arith.maxui", "arith.minui", "arith.andi"
  , "arith.ori", "arith.xori", "arith.shli", "arith.shrsi", "arith.shrui"
  , "arith.addf", "arith.subf", "arith.mulf", "arith.divf", "arith.remf", "arith.maxnumf"
  , "arith.minnumf", "arith.maximumf", "arith.minimumf" ]

/-- Casts and other one-operand `arith` operations: `%a : T to U`. -/
def castOps : List String :=
  [ "arith.index_cast", "arith.index_castui", "arith.extsi", "arith.extui", "arith.trunci"
  , "arith.sitofp", "arith.uitofp", "arith.fptosi", "arith.fptoui", "arith.extf", "arith.truncf"
  , "arith.bitcast", "arith.negf" ]

/-! ## Operations -/

mutual

/-- One operation. A generic-form operation inside a pretty file — which is how an unregistered
dialect is printed — is read by the generic reader where it stands. -/
partial def parseOne (al : Aliases) : P Op := do
  match ← attempt parseOp with
  | some o => pure o
  | none   => parsePretty al

partial def parsePretty (al : Aliases) : P Op := do
  skipWs
  let results ← if (← peek) == some '%' then do
        let rs ← resultNames []
        let _ ← ch '='
        pure rs
      else pure []
  let name ← ident
  match name with
  | "module" => do
      let attrs ← if ← tryKw "attributes" then do let _ ← ch '{'; parseAttrDictTail [] else pure []
      let _ ← ch '{'
      let ops ← parseOpsBrace al []
      pure ⟨"builtin.module", [], [], attrs, [⟨[], ops⟩], [], []⟩
  | "func.func" => do
      skipWs
      let _ ← tryKw "private"
      let _ ← tryKw "public"
      let _ ← tryKw "nested"
      let nm ← symName
      let _ ← ch '('
      let args ← parseBlockArgs []
      let rets ← if ← tryKw "->" then typeOrList else pure []
      let attrs ← if ← tryKw "attributes" then do let _ ← ch '{'; parseAttrDictTail [] else pure []
      skipWs
      if (← peek) != some '{' then
        err s!"func.func '{nm}' has no body: a declaration has no program to check"
      let _ ← ch '{'
      let ops ← parseOpsBrace al []
      pure ⟨"func.func", [], [], [("function_type", .ty (.fn (args.map Prod.snd) rets)),
                                  ("sym_name", .str nm)] ++ attrs,
            [⟨args, ops⟩], [], []⟩
  | "return" => do
      let vs ← valueList []
      let tys ← if ← tryCh ':' then typeOrList else pure []
      pure ⟨"func.return", [], vs, [], [], tys, []⟩
  | "affine.yield" | "scf.yield" => do
      let vs ← valueList []
      let tys ← if ← tryCh ':' then typeOrList else pure []
      pure ⟨if name == "affine.yield" then "affine.yield" else "scf.yield", [], vs, [], [], tys, []⟩
  | "affine.for" => do
      let iv ← valueId
      let _ ← ch '='
      let (lo, loOps) ← forBound al
      let _ ← kw "to"
      let (hi, hiOps) ← forBound al
      let step ← if ← tryKw "step" then do let n ← natLit; pure (n : Int) else pure 1
      skipWs
      if ← lookingAt "iter_args" then
        err "affine.for with iter_args: a loop-carried value is a reduction, which is the \
             dependence wfB exists to refuse"
      let _ ← ch '{'
      let ops ← parseOpsBrace al []
      pure ⟨"affine.for", [], loOps ++ hiOps,
            [ ("lowerBoundMap", .affine lo)
            , ("upperBoundMap", .affine hi)
            , ("step", .ann (.int step) .index) ],
            [⟨[(iv, .index)], ops⟩], [], []⟩
  | "affine.parallel" => do
      let _ ← ch '('
      let ivs ← valueListUntil ')' []
      let _ ← ch '='
      let _ ← ch '('
      let los ← constTuple "affine.parallel lower" []
      let _ ← kw "to"
      let _ ← ch '('
      let his ← constTuple "affine.parallel upper" []
      let steps ← if ← tryKw "step" then do let _ ← ch '('; constTuple "affine.parallel step" []
                  else pure (los.map (fun _ => 1))
      skipWs
      if ← lookingAt "reduce" then
        err "affine.parallel with a reduce clause: a reduction is the dependence wfB exists to \
             refuse"
      let _ ← ch '{'
      let ops ← parseOpsBrace al []
      pure ⟨"affine.parallel", [], [],
            [ ("lowerBoundsMap", .affine (constMap los))
            , ("upperBoundsMap", .affine (constMap his))
            , ("steps", .arr (steps.map MAttr.int)) ],
            [⟨ivs.map (fun v => (v, MTy.index)), ops⟩], [], []⟩
  | "affine.load" => do
      let mr ← valueId
      let _ ← ch '['
      let (es, ds) ← idxList [] []
      let _ ← ch ':'
      let t ← parseType
      pure ⟨"affine.load", results, mr :: ds, [("map", .affine (mapOver ds.length es))], [],
            t :: indexTys ds.length, [eltOf t]⟩
  | "affine.store" => do
      let v ← valueId
      let _ ← ch ','
      let mr ← valueId
      let _ ← ch '['
      let (es, ds) ← idxList [] []
      let _ ← ch ':'
      let t ← parseType
      pure ⟨"affine.store", [], v :: mr :: ds, [("map", .affine (mapOver ds.length es))], [],
            eltOf t :: t :: indexTys ds.length, []⟩
  | "affine.apply" => do
      let m ← mapRef al
      let _ ← ch '('
      let ds ← valueListUntil ')' []
      let ss ← if ← tryCh '[' then valueListUntil ']' [] else pure []
      pure ⟨"affine.apply", results, ds ++ ss, [("map", .affine m)], [],
            indexTys (ds.length + ss.length), [.index]⟩
  | "memref.alloc" | "memref.alloca" => do
      let _ ← ch '('
      let dyn ← valueListUntil ')' []
      if !dyn.isEmpty then
        err s!"{name} with a dynamic size: a buffer's shape has to be known to place it"
      let _ ← if ← tryCh '[' then do let _ ← valueListUntil ']' []; pure () else pure ()
      let attrs ← optAttrDict
      let _ ← ch ':'
      let t ← parseType
      pure ⟨name, results, [], attrs, [], [], [t]⟩
  | "memref.dealloc" => do
      let v ← valueId
      let _ ← ch ':'
      let t ← parseType
      pure ⟨"memref.dealloc", [], [v], [], [], [t], []⟩
  | "memref.global" => do
      skipWs
      let vis ← if (← peek) == some '"' then do let s ← strLit; pure [("sym_visibility", MAttr.str s)]
                else pure []
      let _ ← tryKw "constant"
      let nm ← symName
      let _ ← ch ':'
      let t ← parseType
      let init ← if ← tryCh '=' then do
            skipWs
            if ← tryKw "uninitialized" then pure []
            else do let a ← parseAttrValue; pure [("initial_value", a)]
          else pure []
      pure ⟨"memref.global", [], [], vis ++ [("sym_name", .str nm), ("type", .ty t)] ++ init,
            [], [], []⟩
  | "memref.get_global" => do
      let nm ← symName
      let _ ← ch ':'
      let t ← parseType
      pure ⟨"memref.get_global", results, [], [("name", .sym nm)], [], [], [t]⟩
  | "memref.load" | "memref.store" => do
      let v ← if name == "memref.store" then do let x ← valueId; let _ ← ch ','; pure (some x)
              else pure none
      let mr ← valueId
      let _ ← ch '['
      let idx ← valueListUntil ']' []
      let _ ← ch ':'
      let t ← parseType
      match v with
      | some x => pure ⟨"memref.store", [], x :: mr :: idx, [], [],
                        eltOf t :: t :: indexTys idx.length, []⟩
      | none   => pure ⟨"memref.load", results, mr :: idx, [], [],
                        t :: indexTys idx.length, [eltOf t]⟩
  | "arith.constant" => do
      let a ← parseAttrValue
      let t := match a with | .ann _ t => [t] | _ => []
      pure ⟨"arith.constant", results, [], [("value", a)], [], [], t⟩
  | "arith.select" => do
      let c ← valueId
      let _ ← ch ','
      let a ← valueId
      let _ ← ch ','
      let b ← valueId
      let _ ← ch ':'
      let t ← parseType
      pure ⟨"arith.select", results, [c, a, b], [], [], [.int 1, t, t], [t]⟩
  | "arith.cmpi" | "arith.cmpf" => do
      let pred ← ident
      let _ ← ch ','
      let a ← valueId
      let _ ← ch ','
      let b ← valueId
      let _ ← ch ':'
      let t ← parseType
      pure ⟨name, results, [a, b], [("predicate", .str pred)], [], [t, t], [.int 1]⟩
  | nm =>
      if binaryOps.contains nm then do
        let a ← valueId
        let _ ← ch ','
        let b ← valueId
        let fm ← optFastmath
        let attrs ← optAttrDict
        let _ ← ch ':'
        let t ← parseType
        pure ⟨nm, results, [a, b], fm ++ attrs, [], [t, t], [t]⟩
      else if castOps.contains nm then do
        let a ← valueId
        let fm ← optFastmath
        let _ ← ch ':'
        let t ← parseType
        let u ← if ← tryKw "to" then parseType else pure t
        pure ⟨nm, results, [a], fm, [], [t], [u]⟩
      else
        err s!"pretty form of '{nm}' is not in the vocabulary (docs/mlir-pretty.md); print it with \
               mlir-opt --mlir-print-op-generic"

/-- Operations up to the closing `}`, the brace already consumed. -/
partial def parseOpsBrace (al : Aliases) (acc : List Op) : P (List Op) := do
  skipWs
  if ← tryCh '}' then pure acc.reverse
  else if (← peek) == some '^' then
    err "multi-block region: unstructured control flow is not representable in ParM"
  else if ← atEnd then err "expected '}', found end of input"
  else do
    let o ← parseOne al
    parseOpsBrace al (o :: acc)

end

/-- Operations to the end of input, collecting map aliases as they are defined. -/
partial def parseTop (al : Aliases) (acc : List Op) : P (List Op) := do
  skipWs
  if ← atEnd then pure acc.reverse
  else if (← peek) == some '#' then do
    bump
    let nm ← ident
    let _ ← ch '='
    skipWs
    if ← lookingAt "affine_set" then err "integer sets (affine_set) are not supported"
    let m ← parseAffineMap
    parseTop ((nm, m) :: al) acc
  else do
    let o ← parseOne al
    parseTop al (o :: acc)

/-- **Read a file of MLIR custom form.** -/
def parse (src : String) : Except String (List Op) :=
  let cs := src.toList.toArray
  match parseTop [] [] ⟨cs, 0⟩ with
  | .ok (ops, _) => .ok ops
  | .error e     => .error (P.render cs e)

/-! ## One function at a time

A real file holds many functions and this reader will not read all of them: `iter_args` is a
reduction, a dynamic memref has no shape, and `tensor.empty` is not in the vocabulary. Refusing the
*file* for one function would hide the nineteen that are readable, so the text is split at the
`func.func` lines first and each piece read on its own. Every piece gets an answer — an `Op` or the
reason — and nothing is skipped silently. -- ref: `docs/mlir-pretty.md` § One function out of twenty
-/

/-- `src` in groups: the preamble — map aliases, and anything before the first function — then one
group per `func.func` beginning at column zero. -/
partial def groupsGo (ls : List String) (cur : List String) (acc : List String) : List String :=
  match ls with
  | []        => (("\n".intercalate cur.reverse) :: acc).reverse
  | l :: rest =>
      if l.startsWith "func.func" && !cur.isEmpty then
        groupsGo rest [l] (("\n".intercalate cur.reverse) :: acc)
      else groupsGo rest (l :: cur) acc

def groupsOf (src : String) : List String := groupsGo (src.splitOn "\n") [] []

/-- The name a `func.func` group declares, if it declares one. -/
def funcName? (chunk : String) : Option String :=
  match chunk.toList.dropWhile (· != '@') with
  | []      => none
  | _ :: cs =>
      let nm := String.ofList (cs.takeWhile (fun c => c.isAlphanum || c == '_' || c == '$'))
      if nm.isEmpty then none else some nm

/-- **Every function in a pretty file, read on its own**, in the order written. The preamble is
prepended to each group, because a map alias is file-scoped. -/
def parseFunctions (src : String) : List (String × Except String (List Op)) :=
  match groupsOf src with
  | pre :: f :: fs =>
      (f :: fs).filterMap fun g =>
        (funcName? g).map fun nm => (nm, parse (pre ++ "\n" ++ g))
  -- no function begins at column zero, so the file is one unit — a `module { … }` wrapper — and is
  -- read as one. Each row then carries the whole module, which is what the lowering wants anyway:
  -- the globals live outside the function.
  | _ =>
      match parse src with
      | .error e => [("<the module>", .error e)]
      | .ok ops  => (funcsOf ops).map fun f =>
          (((f.symAttr? "sym_name").getD "?"), .ok ops)

end Pretty

/-! ## Choosing a reader

Generic form's operations begin with a quoted name, custom form's with a bare identifier, and that
is the whole difference at the door. A file may mix them: an unregistered dialect inside a pretty
file is printed generically, and the pretty reader passes such an operation to the generic one. -/

/-- Whether the first operation in this text is in generic form: skipping comments, map aliases and
a result list, the name that follows is quoted. -/
partial def looksGenericGo : List Char → Bool
  | []               => false
  | '/' :: '/' :: cs => looksGenericGo (cs.dropWhile (· != '\n'))
  | c :: cs =>
      if c == ' ' || c == '\n' || c == '\t' || c == '\r' || c == '=' then looksGenericGo cs
      else if c == '#' then looksGenericGo (cs.dropWhile (· != '\n'))
      else if c == '%' then looksGenericGo (cs.dropWhile (fun d => d != '=' && d != '\n'))
      else c == '"'

def looksGeneric (src : String) : Bool := looksGenericGo src.toList

/-- **Read a file in either form.** -/
def parseAny (src : String) : Except String (List Op) :=
  if looksGeneric src then parse src else Pretty.parse src

end Paralever.MLIR
