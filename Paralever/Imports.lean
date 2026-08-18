/-! # Mathlib import policy

**Never `import Mathlib`.** It rebuilds/pulls in the entire library and dominates build time; a
narrow import is orders of magnitude faster. `Core/` and `Theory/` need no Mathlib at all — keep
it that way as long as possible, so `lean <file>.lean` stays a fast standalone typecheck.

When a file genuinely needs a Mathlib lemma, import the **specific module** it lives in (e.g.
`import Mathlib.Data.List.Fold`), not a re-exporting umbrella file. Add the import where it's used,
not here — this file just tracks *which* modules the plan already anticipates needing, so the exact
path only has to be looked up once.

## Anticipated (from `PLAN.md`, not yet imported anywhere)

| lemma | module |
|---|---|
| `List.prod_flatten` / `List.sum_flatten` | `Batteries.Data.List.Lemmas` (not Mathlib) / `Mathlib.Algebra.BigOperators.Group.List.Defs` |
| `List.splitLengths`, `flatten_splitLengths` | `Mathlib.Data.List.SplitLengths` |
| `foldl_eq_foldr`, `foldl_eq_foldr_of_commute` | `Mathlib.Data.List.Fold` |
| `List.Perm.prod_eq`, `Perm.prod_eq'` | `Mathlib.Algebra.BigOperators.Group.List.Basic` / `...Lemmas` |
| `take_sum_flatten`, `drop_sum_flatten` | `Mathlib.Algebra.BigOperators.Group.List.Basic` |
-/
