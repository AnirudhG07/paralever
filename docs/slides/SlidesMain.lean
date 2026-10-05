import VersoSlides
import Slides

open VersoSlides

def findBase : IO System.FilePath := do
  for d in [("docs/slides" : System.FilePath), "."] do
    if ← (d / "lean.css").pathExists then return d
  throw <| IO.userError "lean.css not found — run `lake exe slides` from the repo root (or from docs/ppt)"

/-- Load the CSS theme fresh at RUNTIME from `lean.css`, and bundle the deck's
images as theme assets (written verbatim to `<outputDir>/assets/…`).

We read the CSS here instead of `include_str`: `include_str` bakes it in at
*compile* time and Lake won't re-read it when only `lean.css` changes, so edits
would silently ship stale. Reading it in `main` means editing `lean.css` (or an
image) needs only a re-run of `lake exe slides` — no rebuild. -/
def loadTheme : IO CustomTheme := do
  let base ← findBase
  let css ← IO.FS.readFile (base / "lean.css")
  let asset (name : String) : IO ThemeAsset := do
    return { filename := "assets/" ++ name, contents := ← IO.FS.readBinFile (base / "assets" / name) }
  let assets ← #[].mapM asset
  -- stagger.js (per-item reveal fragments for `:::class "steps"` lists) is deliberately
  -- NOT loaded: every slide appears in full, with no staged reveals. To restore the
  -- staggered behaviour, ship it as an asset here and add it back to `extraJs` below.
  return {
    stylesheet     := { filename := "lean.css", contents := ⟨css⟩ },
    assets         := assets,
    -- light theme → light highlight.js theme (not the dark default)
    highlightTheme := HighlightTheme.forRevealTheme "white"
  }

/-- Shared config; every deck writes to its own subfolder under `_slides/`.
`build-site.sh` then deploys each `_slides/<name>/` to `/<name>/`. -/
def cfg (theme : CustomTheme) (out : System.FilePath) : Config where
  theme       := .custom theme
  outputDir   := out
  slideNumber := true
  transition  := "slide"
  width       := 1280
  height      := 720
  margin      := 0.0
  center      := false

/-- Build every deck. **Add one line per new deck**: give it a URL sub-folder and
point it at that deck's `#doc` with `%doc <ModuleName>` (the bare Lean module
name — e.g. `Slides`, not `Slides.lean`). -/
def main : IO UInt32 := do
  let base ← findBase
  let theme ← loadTheme
  -- per-deck overrides, layered on top of lean.css (read at runtime too)
  let deckCss ← IO.FS.readFile (base / "paralever.css")
  let config : Config := { cfg theme "_slides/paralever" with
    extraCss := #[{ filename := "paralever.css", contents := ⟨deckCss⟩ }],
    extraJs  := #[] }
  discard <| slidesMain config (doc := %doc Slides)
  return 0
