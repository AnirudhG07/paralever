import MLIR.Ast

/-! # A reader for MLIR generic form

Generic form (`--mlir-print-op-generic`) is one grammar for every dialect:

```text
%0 = "affine.load"(%A, %i) {map = affine_map<(d0) -> (d0)>} : (memref<8xi32>, index) -> i32
```

Each dialect's *custom* assembly (`affine.for %i = 0 to 8 { … }`) would need a parser apiece, so
the generic form is what makes "N languages, one converter" true. -- ref: `docs/mlir.md`

This reader is **untrusted**, exactly as `Search/RaceSearch.lean`'s phase 2 is: nothing downstream
believes it. `render` is its inverse, and `MLIR/Corpus.lean` gates `render ∘ parse` for idempotence
on every pilot, which is what catches a rule that reads a file in a way nobody intended.

Constructs rejected rather than approximated, each with a named error: multi-block regions
(unstructured control flow, which `ParM` cannot represent — `CLAUDE.md` fact 4), dynamic `memref`
dimensions, `memref` layout maps, integer sets (`affine_set`), and hexadecimal float literals. -/

namespace Paralever.MLIR

/-- `10 ^ k` as a rational, by recursion: core's `Rat` carries no `HPow`. -/
def pow10 : Nat → Rat
  | 0     => 1
  | k + 1 => 10 * pow10 k

/-! ## The reader monad -/

/-- Input as characters, plus a position. An `Array Char` rather than `String.Pos` so that
lookahead and backtracking are `Nat` arithmetic. -/
structure PState where
  cs : Array Char
  i  : Nat
  deriving Inhabited

/-- A reader: consumes input, or fails with a message naming the offset. -/
abbrev P (α : Type) := StateT PState (Except String) α

namespace P

/-- Fail, quoting where. The snippet is what turns "parse error" into something a corpus report can
act on. -/
def err (msg : String) : P α := do
  let st ← get
  let near := String.ofList ((st.cs.toList.drop st.i).take 48)
  StateT.lift (Except.error (msg ++ " (offset " ++ toString st.i ++ ", near: " ++ near ++ ")"))

/-- Run `p`, and on failure consume nothing. The one piece of backtracking the grammar needs: a
`memref`'s shape is a run of `N x` groups whose end is only known by trying to read one more. -/
def attempt (p : P α) : P (Option α) := fun st =>
  match p st with
  | .ok (a, st') => .ok (some a, st')
  | .error _     => .ok (none, st)

def atEnd : P Bool := do let st ← get; pure (st.cs.size ≤ st.i)

/-- The character at the cursor, without consuming it. -/
def peek : P (Option Char) := do
  let st ← get
  pure (if st.i < st.cs.size then some st.cs[st.i]! else none)

/-- The character `k` ahead. -/
def peekAt (k : Nat) : P (Option Char) := do
  let st ← get
  pure (if st.i + k < st.cs.size then some st.cs[st.i + k]! else none)

def bump : P Unit := modify fun st => { st with i := st.i + 1 }

/-- Whether the input continues with `s`, without consuming it. -/
def lookingAt (s : String) : P Bool := do
  let st ← get
  pure (s.toList.zipIdx.all fun (c, k) => st.i + k < st.cs.size && st.cs[st.i + k]! == c)

end P

open P

/-! ## Lexical layer -/

/-- Whitespace and `//` comments. -/
partial def skipWs : P Unit := do
  match ← peek with
  | some c =>
      if c == ' ' || c == '\n' || c == '\t' || c == '\r' then
        bump; skipWs
      else if c == '/' && (← peekAt 1) == some '/' then
        let rec line : P Unit := do
          match ← peek with
          | some d => if d == '\n' then bump else do bump; line
          | none   => pure ()
        line; skipWs
      else pure ()
  | none => pure ()

/-- The longest run of characters satisfying `p`, possibly empty. -/
partial def takeWhile (p : Char → Bool) : P String := do
  let rec go (acc : List Char) : P (List Char) := do
    match ← peek with
    | some c => if p c then do bump; go (c :: acc) else pure acc
    | none   => pure acc
  pure (String.ofList (← go []).reverse)

/-- Consume exactly this character. -/
def ch (c : Char) : P Unit := do
  skipWs
  if (← peek) == some c then bump else err s!"expected '{c}'"

/-- Consume this character if it is there. -/
def tryCh (c : Char) : P Bool := do
  skipWs
  if (← peek) == some c then do bump; pure true else pure false

/-- Consume this literal string. -/
def kw (s : String) : P Unit := do
  skipWs
  if ← lookingAt s then modify (fun st => { st with i := st.i + s.length })
  else err s!"expected '{s}'"

def tryKw (s : String) : P Bool := do
  skipWs
  if ← lookingAt s then do modify (fun st => { st with i := st.i + s.length }); pure true
  else pure false

private def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_' || c == '$'
private def isIdentCont (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '$' || c == '.' || c == '-'

/-- A bare identifier: an op or attribute name, or a dimension name in an affine map. -/
def ident : P String := do
  skipWs
  match ← peek with
  | some c =>
      if isIdentStart c then takeWhile isIdentCont
      else err "expected an identifier"
  | none => err "expected an identifier, found end of input"

/-- An SSA name, stored without its `%`. -/
def valueId : P String := do
  skipWs
  if (← peek) == some '%' then
    bump
    let nm ← takeWhile (fun c => c.isAlphanum || c == '_' || c == '$' || c == '.' || c == '-')
    if nm.isEmpty then err "expected a name after '%'" else pure nm
  else err "expected an SSA name beginning with '%'"

/-- A double-quoted string, with `\"`, `\\` and `\n` escapes. -/
partial def strLit : P String := do
  skipWs
  if (← peek) != some '"' then err "expected a quoted string"
  else do
    bump
    let rec go (acc : List Char) : P (List Char) := do
      match ← peek with
      | none      => err "unterminated string"
      | some '"'  => do bump; pure acc
      | some '\\' => do
          bump
          match ← peek with
          | some 'n'  => do bump; go ('\n' :: acc)
          | some 't'  => do bump; go ('\t' :: acc)
          | some d    => do bump; go (d :: acc)
          | none      => err "unterminated escape"
      | some c    => do bump; go (c :: acc)
    pure (String.ofList (← go []).reverse)

def natLit : P Nat := do
  skipWs
  let ds ← takeWhile Char.isDigit
  if ds.isEmpty then err "expected a number" else pure ds.toNat!

/-- A decimal number: an `Int` when it has neither a fractional part nor an exponent, and otherwise
the `Rat` the literal names exactly. -/
def numLit : P (Int ⊕ Rat) := do
  skipWs
  let neg ← tryCh '-'
  if ← lookingAt "0x" then err "hexadecimal float literals are not supported"
  let ip ← takeWhile Char.isDigit
  if ip.isEmpty then err "expected a number"
  let frac ← if (← peek) == some '.' then do bump; takeWhile Char.isDigit else pure ""
  let hasExp ← pure ((← peek) == some 'e' || (← peek) == some 'E')
  let expv ← if hasExp then do
        bump
        let esign ← if (← peek) == some '-' then do bump; pure (-1 : Int)
                    else do let _ ← tryCh '+'; pure 1
        let ed ← takeWhile Char.isDigit
        if ed.isEmpty then err "expected exponent digits" else pure (esign * (ed.toNat! : Int))
      else pure 0
  let sign : Int := if neg then -1 else 1
  if frac.isEmpty && !hasExp then
    pure (.inl (sign * (ip.toNat! : Int)))
  else
    let mant : Int := sign * ((ip ++ frac).toNat! : Int)
    let scale : Rat := pow10 frac.length
    let base : Rat := (mant : Rat) / scale
    let e10 : Rat := if expv < 0 then 1 / pow10 (-expv).toNat else pow10 expv.toNat
    pure (.inr (base * e10))

/-! ## Types -/

/-! A `memref`'s shape is a run of `N x` groups, then the element type. The end of the run is found
by reading one group speculatively, which is what `attempt` is for. -/

mutual

partial def parseType : P MTy := do
  skipWs
  if ← lookingAt "index" then do let _ ← kw "index"; pure .index
  else if ← lookingAt "memref" then do
    let _ ← kw "memref"
    let _ ← ch '<'
    let dims ← parseDims []
    let elt ← parseType
    skipWs
    if (← peek) == some ',' then err "memref with a layout map or memory space is not supported"
    let _ ← ch '>'
    pure (.memref dims elt)
  else if ← lookingAt "tensor" then do
    let _ ← kw "tensor"
    let _ ← ch '<'
    let dims ← parseDims []
    let elt ← parseType
    let _ ← ch '>'
    pure (.tensor dims elt)
  else if ← lookingAt "none" then do let _ ← kw "none"; pure (.other "none")
  else if (← peek) == some '!' then do
    bump
    let s ← ident
    pure (.other ("!" ++ s))
  else if (← peek) == some '(' then do
    let _ ← ch '('
    let ts ← parseTypeListTail []
    skipWs
    if ← tryKw "->" then do
      skipWs
      if (← peek) == some '(' then do
        let _ ← ch '('
        let outs ← parseTypeListTail []
        pure (.fn ts outs)
      else do
        let t ← parseType
        pure (.fn ts [t])
    else pure (.tuple ts)
  else match ← peek with
    | some 'i' => do
        bump
        let w ← takeWhile Char.isDigit
        if w.isEmpty then err "expected an integer width after 'i'" else pure (.int w.toNat!)
    | some 'f' => do
        bump
        let w ← takeWhile Char.isDigit
        if w.isEmpty then err "expected a float width after 'f'" else pure (.float w.toNat!)
    | some c   =>
        if isIdentStart c then do let s ← ident; pure (.other s)
        else err "expected a type"
    | none     => err "expected a type, found end of input"

/-- Dimensions of a `memref`, each a number followed by `x`. -/
partial def parseDims (acc : List Nat) : P (List Nat) := do
  skipWs
  if (← peek) == some '?' then err "dynamic memref dimension '?' is not supported"
  match ← attempt (do let n ← natLit; let _ ← ch 'x'; pure n) with
  | some n => parseDims (n :: acc)
  | none   => pure acc.reverse

/-- Types up to a closing `)`, the opening paren already consumed. -/
partial def parseTypeListTail (acc : List MTy) : P (List MTy) := do
  skipWs
  if ← tryCh ')' then pure acc.reverse
  else do
    let t ← parseType
    skipWs
    if ← tryCh ',' then parseTypeListTail (t :: acc)
    else do let _ ← ch ')'; pure (t :: acc).reverse

end

/-- The `(ins) -> outs` trailer every generic-form op carries. A single unparenthesised result type
is MLIR's own shorthand, so both forms are read. -/
def parseFunctionType : P (List MTy × List MTy) := do
  let _ ← ch '('
  let ins ← parseTypeListTail []
  let _ ← kw "->"
  skipWs
  if (← peek) == some '(' then do
    let _ ← ch '('
    let outs ← parseTypeListTail []
    pure (ins, outs)
  else do
    let t ← parseType
    pure (ins, [t])

/-! ## Affine maps -/

/-! An affine expression, resolving names against the map's own dimension and symbol lists. -/

mutual

partial def parseAff (ds ss : List String) : P AffExp := do
  let a ← parseAffMul ds ss
  parseAffAdd ds ss a

partial def parseAffAdd (ds ss : List String) (a : AffExp) : P AffExp := do
  skipWs
  if ← tryCh '+' then do let b ← parseAffMul ds ss; parseAffAdd ds ss (.add a b)
  else if (← peek) == some '-' then do
    bump
    let b ← parseAffMul ds ss
    parseAffAdd ds ss (.sub a b)
  else pure a

partial def parseAffMul (ds ss : List String) : P AffExp := do
  let a ← parseAffAtom ds ss
  parseAffMulTail ds ss a

partial def parseAffMulTail (ds ss : List String) (a : AffExp) : P AffExp := do
  skipWs
  if ← tryCh '*' then do let b ← parseAffAtom ds ss; parseAffMulTail ds ss (.mul a b)
  else if ← tryKw "floordiv" then do let b ← parseAffAtom ds ss; parseAffMulTail ds ss (.floorDiv a b)
  else if ← tryKw "ceildiv" then do let b ← parseAffAtom ds ss; parseAffMulTail ds ss (.ceilDiv a b)
  else if ← tryKw "mod" then do let b ← parseAffAtom ds ss; parseAffMulTail ds ss (.mod a b)
  else pure a

partial def parseAffAtom (ds ss : List String) : P AffExp := do
  skipWs
  if ← tryCh '(' then do
    let e ← parseAff ds ss
    let _ ← ch ')'
    pure e
  else if (← peek) == some '-' then do
    bump
    let e ← parseAffAtom ds ss
    pure (.sub (.const 0) e)
  else match ← peek with
    | some c =>
        if c.isDigit then do let n ← natLit; pure (.const (n : Int))
        else do
          let nm ← ident
          match ds.findIdx? (· == nm) with
          | some k => pure (.dim k)
          | none   =>
              match ss.findIdx? (· == nm) with
              | some k => pure (.sym k)
              | none   => err s!"unbound name '{nm}' in affine expression"
    | none => err "expected an affine expression"

end

/-- Comma-separated identifiers up to `close`, the opening bracket already consumed. -/
partial def parseNameList (close : Char) (acc : List String) : P (List String) := do
  skipWs
  if ← tryCh close then pure acc.reverse
  else do
    let nm ← ident
    skipWs
    if ← tryCh ',' then parseNameList close (nm :: acc)
    else do let _ ← ch close; pure (nm :: acc).reverse

/-- Affine expressions up to `)`. -/
partial def parseAffList (ds ss : List String) (acc : List AffExp) : P (List AffExp) := do
  skipWs
  if ← tryCh ')' then pure acc.reverse
  else do
    let e ← parseAff ds ss
    skipWs
    if ← tryCh ',' then parseAffList ds ss (e :: acc)
    else do let _ ← ch ')'; pure (e :: acc).reverse

/-- `affine_map<(d0, d1)[s0] -> (d0 * 32 + d1)>`. -/
def parseAffineMap : P AffMap := do
  let _ ← kw "affine_map"
  let _ ← ch '<'
  let _ ← ch '('
  let ds ← parseNameList ')' []
  let ss ← if ← tryCh '[' then parseNameList ']' [] else pure []
  let _ ← kw "->"
  let _ ← ch '('
  let rs ← parseAffList ds ss []
  let _ ← ch '>'
  pure ⟨ds, ss, rs⟩

/-! ## Attributes -/

/-- The `[…]` nesting of a `dense<…>` initialiser, flattened row-major — which is the order a
`Buf`'s `init` wants. -/
partial def parseDenseElems (acc : List Int) : P (List Int) := do
  skipWs
  if ← tryCh '[' then do
    let inner ← parseDenseElems []
    skipWs
    if ← tryCh ',' then parseDenseElems (inner.reverse ++ acc)
    else do let _ ← ch ']'; pure (inner.reverse ++ acc).reverse
  else if ← tryCh ']' then pure acc.reverse
  else do
    let n ← numLit
    let v := match n with | .inl k => k | .inr q => q.num / q.den
    skipWs
    if ← tryCh ',' then parseDenseElems (v :: acc)
    else do let _ ← ch ']'; pure (v :: acc).reverse

/-- Signed integers up to `close` — the elements of an `array<i32: …>`. -/
partial def parseIntsUntil (close : Char) (acc : List Int) : P (List Int) := do
  skipWs
  if ← tryCh close then pure acc.reverse
  else do
    let n ← numLit
    let v := match n with | .inl k => k | .inr q => q.num / q.den
    skipWs
    if ← tryCh ',' then parseIntsUntil close (v :: acc)
    else do let _ ← ch close; pure (v :: acc).reverse

mutual

partial def parseAttrValue : P MAttr := do
  skipWs
  if ← lookingAt "affine_map" then do let m ← parseAffineMap; pure (.affine m)
  else if ← lookingAt "affine_set" then err "integer sets (affine_set) are not supported"
  else if ← lookingAt "dense" then do
    let _ ← kw "dense"
    let _ ← ch '<'
    skipWs
    let a ←
      if (← peek) == some '[' then do
        let _ ← ch '['
        let es ← parseDenseElems []
        pure (MAttr.dense es false)
      else do
        let n ← numLit
        let v := match n with | .inl k => k | .inr q => q.num / q.den
        pure (MAttr.dense [v] true)
    let _ ← ch '>'
    match ← attempt (do let _ ← ch ':'; parseType) with
    | some t => pure (.ann a t)
    | none   => pure a
  else if ← lookingAt "array" then do
    let _ ← kw "array"
    let _ ← ch '<'
    let t ← ident
    skipWs
    if ← tryCh '>' then pure (.darr t [])
    else do
      let _ ← ch ':'
      let es ← parseIntsUntil '>' []
      pure (.darr t es)
  else if ← lookingAt "unit" then do let _ ← kw "unit"; pure .unit
  else if ← lookingAt "true" then do let _ ← kw "true"; pure (.int 1)
  else if ← lookingAt "false" then do let _ ← kw "false"; pure (.int 0)
  else match ← peek with
    | some '"' => do let s ← strLit; pure (.str s)
    | some '@' => do
        bump
        skipWs
        if (← peek) == some '"' then do let s ← strLit; pure (.sym s)
        else do let s ← ident; pure (.sym s)
    | some '[' => do
        let _ ← ch '['
        let xs ← parseAttrList ']' []
        pure (.arr xs)
    | some '{' => do
        let _ ← ch '{'
        let kvs ← parseAttrDictTail []
        pure (.dict kvs)
    | some c   =>
        if c.isDigit || c == '-' then do
          let n ← numLit
          let a := match n with | .inl k => MAttr.int k | .inr q => MAttr.flt q
          match ← attempt (do let _ ← ch ':'; parseType) with
          | some t => pure (.ann a t)
          | none   => pure a
        else do
          let t ← parseType
          pure (.ty t)
    | none     => err "expected an attribute value"

partial def parseAttrList (close : Char) (acc : List MAttr) : P (List MAttr) := do
  skipWs
  if ← tryCh close then pure acc.reverse
  else do
    let a ← parseAttrValue
    skipWs
    if ← tryCh ',' then parseAttrList close (a :: acc)
    else do let _ ← ch close; pure (a :: acc).reverse

/-- Entries up to the closing `}`, the opening brace already consumed. -/
partial def parseAttrDictTail (acc : List (String × MAttr)) : P (List (String × MAttr)) := do
  skipWs
  if ← tryCh '}' then pure acc.reverse
  else do
    skipWs
    let k ← if (← peek) == some '"' then strLit else ident
    let _ ← ch '='
    let v ← parseAttrValue
    skipWs
    if ← tryCh ',' then parseAttrDictTail ((k, v) :: acc)
    else do let _ ← ch '}'; pure ((k, v) :: acc).reverse

end

/-! ## Operations -/

/-- SSA names up to `)`, the opening paren already consumed. -/
partial def parseOperands (acc : List String) : P (List String) := do
  skipWs
  if ← tryCh ')' then pure acc.reverse
  else do
    let v ← valueId
    skipWs
    if ← tryCh ',' then parseOperands (v :: acc)
    else do let _ ← ch ')'; pure (v :: acc).reverse

/-- `%i: index` pairs up to `)` — a region's entry-block arguments. -/
partial def parseBlockArgs (acc : List (String × MTy)) : P (List (String × MTy)) := do
  skipWs
  if ← tryCh ')' then pure acc.reverse
  else do
    let v ← valueId
    let _ ← ch ':'
    let t ← parseType
    skipWs
    if ← tryCh ',' then parseBlockArgs ((v, t) :: acc)
    else do let _ ← ch ')'; pure ((v, t) :: acc).reverse

mutual

partial def parseOp : P Op := do
  skipWs
  let results ← if (← peek) == some '%' then do
        let rs ← parseResults []
        let _ ← ch '='
        pure rs
      else pure []
  let name ← strLit
  let _ ← ch '('
  let operands ← parseOperands []
  skipWs
  if (← peek) == some '[' then
    err "successor list: unstructured control flow is not representable in ParM"
  let regions ← if (← peek) == some '(' then do
        let _ ← ch '('
        parseRegionList []
      else pure []
  let attrs ← if (← tryCh '{') then parseAttrDictTail [] else pure []
  let _ ← ch ':'
  let (ins, outs) ← parseFunctionType
  pure ⟨name, results, operands, attrs, regions, ins, outs⟩

/-- Result names before the `=`. `%0:2` (the multi-result shorthand) is rejected here: the lowering
binds a result by name, so a name standing for several values has nowhere to go. -/
partial def parseResults (acc : List String) : P (List String) := do
  let v ← valueId
  skipWs
  if (← peek) == some ':' then err "multi-result shorthand '%x:n' is not supported"
  else if ← tryCh ',' then parseResults (v :: acc)
  else pure (v :: acc).reverse

partial def parseRegionList (acc : List Region) : P (List Region) := do
  skipWs
  let r ← parseRegion
  skipWs
  if ← tryCh ',' then parseRegionList (r :: acc)
  else do let _ ← ch ')'; pure (r :: acc).reverse

partial def parseRegion : P Region := do
  let _ ← ch '{'
  skipWs
  let args ← if (← peek) == some '^' then do
        bump
        let _ ← ident
        let as ← if ← tryCh '(' then parseBlockArgs [] else pure []
        let _ ← ch ':'
        pure as
      else pure []
  let ops ← parseOpsUntil '}' []
  pure ⟨args, ops⟩

/-- Operations up to `close`. A `^` here begins a second block, which is the unstructured case. -/
partial def parseOpsUntil (close : Char) (acc : List Op) : P (List Op) := do
  skipWs
  if ← tryCh close then pure acc.reverse
  else if (← peek) == some '^' then
    err "multi-block region: unstructured control flow is not representable in ParM"
  else if (← atEnd) then err s!"expected '{close}', found end of input"
  else do
    let o ← parseOp
    parseOpsUntil close (o :: acc)

end

/-- Operations up to the end of input — the whole file. -/
partial def parseTop (acc : List Op) : P (List Op) := do
  skipWs
  if ← atEnd then pure acc.reverse
  else do
    let o ← parseOp
    parseTop (o :: acc)

/-- **Read a file of MLIR generic form.** -/
def parse (src : String) : Except String (List Op) :=
  (parseTop [] ⟨src.toList.toArray, 0⟩).map Prod.fst

/-! ## Printing it back

The reader's inverse, so `render ∘ parse` can be gated for idempotence on every pilot. That gate is
what catches a rule that silently reads a construct as something else — a round trip that changes
the text is a reader bug whatever the lowering then does with it. -/

def renderTy : MTy → String
  | .index        => "index"
  | .int w        => "i" ++ toString w
  | .float w      => "f" ++ toString w
  | .memref ds e  => "memref<" ++ String.join (ds.map (fun d => toString d ++ "x"))
                      ++ renderTy e ++ ">"
  | .tensor ds e  => "tensor<" ++ String.join (ds.map (fun d => toString d ++ "x"))
                      ++ renderTy e ++ ">"
  | .tuple ts     => "(" ++ ", ".intercalate (ts.map renderTy) ++ ")"
  | .fn ins outs  => "(" ++ ", ".intercalate (ins.map renderTy) ++ ") -> ("
                      ++ ", ".intercalate (outs.map renderTy) ++ ")"
  | .other s      => s

def renderAff : AffExp → String
  | .dim n        => "d" ++ toString n
  | .sym n        => "s" ++ toString n
  | .const k      => toString k
  | .add a b      => "(" ++ renderAff a ++ " + " ++ renderAff b ++ ")"
  | .sub a b      => "(" ++ renderAff a ++ " - " ++ renderAff b ++ ")"
  | .mul a b      => "(" ++ renderAff a ++ " * " ++ renderAff b ++ ")"
  | .floorDiv a b => "(" ++ renderAff a ++ " floordiv " ++ renderAff b ++ ")"
  | .ceilDiv a b  => "(" ++ renderAff a ++ " ceildiv " ++ renderAff b ++ ")"
  | .mod a b      => "(" ++ renderAff a ++ " mod " ++ renderAff b ++ ")"

/-- Printed with canonical names `d0, d1, …`, which is what makes the round trip idempotent rather
than merely equal: whatever the source called its dimensions, the second pass prints the same. -/
def renderAffMap (m : AffMap) : String :=
  "affine_map<(" ++ ", ".intercalate ((List.range m.dims).map (fun i => "d" ++ toString i)) ++ ")"
    ++ (if m.syms == 0 then ""
        else "[" ++ ", ".intercalate ((List.range m.syms).map (fun i => "s" ++ toString i)) ++ "]")
    ++ " -> (" ++ ", ".intercalate (m.results.map renderAff) ++ ")>"

/-- Fractional digits a float literal is printed with. Fixed rather than shortest, which is what
makes `render ∘ parse` idempotent: the literal printed is exactly `trunc (q · 10¹⁸) / 10¹⁸`, so
reading it back and printing again gives the same digits. Every literal a source file is likely to
carry has fewer than eighteen decimals and so survives exactly. -/
def fltDigits : Nat := 18

/-- A rational as a decimal literal with `fltDigits` fractional digits. -/
def renderRat (q : Rat) : String :=
  let neg := q.num < 0
  let a : Rat := if neg then -q else q
  let scaled : Rat := a * pow10 fltDigits
  let n : Int := scaled.num / scaled.den
  let s0 := toString n
  let s := if s0.length ≤ fltDigits then
             String.ofList (List.replicate (fltDigits + 1 - s0.length) '0') ++ s0
           else s0
  let ip := s.take (s.length - fltDigits)
  let fp := s.drop (s.length - fltDigits)
  (if neg then "-" else "") ++ ip ++ "." ++ fp

mutual

def renderAttr : MAttr → String
  | .int n      => toString n
  | .flt q      => renderRat q
  | .str s      => "\"" ++ s ++ "\""
  | .sym s      => "@" ++ s
  | .ty t       => renderTy t
  | .affine m   => renderAffMap m
  | .dense es s => if s then "dense<" ++ String.join (es.map toString) ++ ">"
                   else "dense<[" ++ ", ".intercalate (es.map toString) ++ "]>"
  | .arr xs     => "[" ++ ", ".intercalate (renderAttrs xs) ++ "]"
  | .dict kvs   => "{" ++ ", ".intercalate (renderAttrDict kvs) ++ "}"
  | .unit       => "unit"
  | .darr t es  => if es.isEmpty then "array<" ++ t ++ ">"
                   else "array<" ++ t ++ ": " ++ ", ".intercalate (es.map toString) ++ ">"
  | .ann a t    => renderAttr a ++ " : " ++ renderTy t

def renderAttrs : List MAttr → List String
  | []      => []
  | x :: xs => renderAttr x :: renderAttrs xs

def renderAttrDict : List (String × MAttr) → List String
  | []            => []
  | (k, v) :: kvs => (k ++ " = " ++ renderAttr v) :: renderAttrDict kvs

end

private def indentOf (d : Nat) : String := String.ofList (List.replicate (2 * d) ' ')

mutual

def renderOp (d : Nat) : Op → String
  | ⟨nm, res, ops, attrs, rgs, ins, outs⟩ =>
      indentOf d
        ++ (if res.isEmpty then "" else ", ".intercalate (res.map (fun r => "%" ++ r)) ++ " = ")
        ++ "\"" ++ nm ++ "\"(" ++ ", ".intercalate (ops.map (fun o => "%" ++ o)) ++ ")"
        ++ (if rgs.isEmpty then ""
            else " (" ++ ", ".intercalate (renderRegions (d + 1) rgs) ++ ")")
        ++ (if attrs.isEmpty then ""
            else " {" ++ ", ".intercalate (renderAttrDict attrs) ++ "}")
        ++ " : (" ++ ", ".intercalate (ins.map renderTy) ++ ") -> ("
        ++ ", ".intercalate (outs.map renderTy) ++ ")"

def renderRegions (d : Nat) : List Region → List String
  | []                => []
  | ⟨args, ops⟩ :: rs =>
      ("{\n"
        ++ (if args.isEmpty then ""
            else indentOf d ++ "^bb0("
              ++ ", ".intercalate (args.map (fun a => "%" ++ a.1 ++ ": " ++ renderTy a.2))
              ++ "):\n")
        ++ "\n".intercalate (renderOps d ops)
        ++ "\n" ++ indentOf (d - 1) ++ "}") :: renderRegions d rs

def renderOps (d : Nat) : List Op → List String
  | []      => []
  | o :: os => renderOp d o :: renderOps d os

end

/-- **A file printed back in generic form.** -/
def render (ops : List Op) : String := "\n".intercalate (renderOps 0 ops)

/-- Parse, print, parse, print: equal strings mean the reader and the printer agree about the file.
`MLIR/Corpus.lean` gates this on every pilot. -/
def roundTrips (src : String) : Bool :=
  match parse src with
  | .error _  => false
  | .ok ops   =>
      let once := render ops
      match parse once with
      | .error _  => false
      | .ok ops'  => render ops' == once

end Paralever.MLIR
