/-! # SMT-LIB terms, as data

An S-expression and its printer, so a query is built as a tree and rendered once. Nothing here
knows what a verification condition is — see `Lang/Smt/Vc.lean` for that, and `docs/smt-vc.md` for
why the obligation is emitted at all. -/

namespace Paralever.Smt

/-- An SMT-LIB term. `app f []` prints as `f`, so a nullary application and an atom agree. -/
inductive Sx where
  | atom : String → Sx
  | app  : String → List Sx → Sx
  deriving Repr, Inhabited, BEq

namespace Sx

/-- An integer literal. SMT-LIB numerals are unsigned, so a negative one is a negation. -/
def int (n : Int) : Sx :=
  if n < 0 then .app "-" [.atom (toString (-n))] else .atom (toString n)

def nat (n : Nat) : Sx := .atom (toString n)

/-- Whether the term is a literal, counting the negation `int` emits for a negative one. -/
partial def isNumeral : Sx → Bool
  | .atom s      => !s.isEmpty && s.all Char.isDigit
  | .app "-" [a] => isNumeral a
  | _            => false

partial def render : Sx → String
  | .atom s   => s
  | .app f [] => f
  | .app f as => "(" ++ f ++ " " ++ String.intercalate " " (as.map render) ++ ")"

/-- `(or a b …)`, collapsing the degenerate arities so a query stays readable. -/
def orAll : List Sx → Sx
  | []  => .atom "false"
  | [a] => a
  | as  => .app "or" as

/-- Whether the term multiplies two non-numerals, which is what takes a query out of `QF_LIA`. -/
partial def nonlinear : Sx → Bool
  | .atom _     => false
  | .app "*" as => (as.filter (fun a => !a.isNumeral)).length > 1 || as.any nonlinear
  | .app _ as   => as.any nonlinear

end Sx

/-- One `(check-sat)` query: what to declare, what to assert, and the logic it needs. -/
structure Query where
  /-- How many `(declare-const uN Int)` lines the assertions refer to. -/
  unknowns : Nat
  /-- The condition whose unsatisfiability is the thing being proved. -/
  goal     : Sx
  /-- Lines of `;` comment placed above the query, to say what it is. -/
  notes    : List String := []
  /-- Hypotheses about the unknowns, asserted before the goal. A loaded value is unconstrained, so
  an obligation that holds only under an invariant of the heap is discharged only with it stated —
  and every one of these weakens the claim, so each is reported. -/
  assume   : List Sx := []
  deriving Repr, Inhabited

namespace Query

/-- `u0`, `u1`, … — the name a loaded value is declared under. -/
def unknownName (k : Nat) : String := s!"u{k}"

/-- The names a loaded value may be declared under, in order. -/
def unknownNames (q : Query) : List String := (List.range q.unknowns).map unknownName

/-- The query as SMT-LIB 2.6 text. `QF_NIA` is declared only when the goal needs it, and a note says
so, because that difference is the difference between decidable and not.

`model` appends `(get-value …)`. It is off by default because asking for a model after `unsat` is an
error, so the driver asks only once the answer is known (`Lang/Smt/Solve.lean`). -/
def render (q : Query) (model : Bool := false) : String :=
  let names := q.unknownNames
  let logic := if q.goal.nonlinear then "QF_NIA" else "QF_LIA"
  let blank := if names.isEmpty then [] else
    [ "", "; Assumptions. A loaded value is unconstrained, so an obligation that needs an invariant",
      "; of the heap — `idx` injective, an index in range — is stated by adding it here.",
      "; e.g. (assert (and (>= u0 0) (< u0 8)))" ]
      ++ q.assume.map (fun a => s!"(assert {a.render})") ++ [""]
  let lines :=
    q.notes.map (fun s => "; " ++ s)
      ++ [s!"(set-logic {logic})"]
      ++ names.map (fun u => s!"(declare-const {u} Int)")
      ++ blank
      ++ [s!"(assert {q.goal.render})", "(check-sat)"]
      ++ (if model && !names.isEmpty then [s!"(get-value ({String.intercalate " " names}))"] else [])
  String.intercalate "\n" lines ++ "\n"

end Query

end Paralever.Smt
