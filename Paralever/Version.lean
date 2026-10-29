/-!
# The version, from one place

`lakefile.toml` is the single source: the string is read out of it while this module elaborates, so
nothing restates it. The minor number tracks Lean's own — `1.34.0` against
`leanprover/lean4:v4.34.0` — and the `#guard` below fails the build if the two drift apart.
-/

namespace Paralever

/-- `lakefile.toml`, baked in at elaboration. -/
private def lakefile : String := include_str "../lakefile.toml"

/-- The value of a top-level `key = "…"` in TOML, with no table or array support: enough for the
three fields this module reads, and nothing a reader could mistake for a parser. -/
private def tomlString (key : String) (toml : String) : Option String :=
  (toml.splitOn "\n").findSome? fun line =>
    match line.splitOn "\"" with
    | [k, v, _] => if k.replace " " "" == key ++ "=" then some v else none
    | _         => none

/-- The version, as `lakefile.toml` declares it. -/
def version : String := (tomlString "version" lakefile).getD "unknown"

/-- The package name, from the same place. -/
def packageName : String := (tomlString "name" lakefile).getD "paralever"

/-- The three components, or zeros if the string is not `N.N.N`. -/
def versionParts : Nat × Nat × Nat :=
  match (version.splitOn ".").map String.toNat? with
  | [some a, some b, some c] => (a, b, c)
  | _                        => (0, 0, 0)

def versionMajor : Nat := versionParts.1
def versionMinor : Nat := versionParts.2.1
def versionPatch : Nat := versionParts.2.2

-- **The versioning rule, machine-checked.** Our minor is Lean's minor, so `1.34.0` can only
-- accompany a `v4.34.x` toolchain and a bump of one forces a bump of the other.
#guard versionMinor == Lean.version.minor

/-- What `--version` prints: the package, its version, and the toolchain it was built with. -/
def versionLine : String :=
  packageName ++ " " ++ version ++ " (" ++ Lean.toolchain ++ ")"

end Paralever
