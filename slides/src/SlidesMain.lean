import VersoSlides
import Slides
import IspSlides

open VersoSlides

/-- Where the deck's sources live. `slides/src/` holds them; `slides/` beside it is where this
program writes, so the two never share a path. -/
def findBase : IO System.FilePath := do
  for d in [("slides/src" : System.FilePath), "."] do
    if ← (d / "lean.css").pathExists then return d
  throw <| IO.userError "lean.css not found — run `lake exe slides` from the repo root"

/-- Load the CSS theme fresh at RUNTIME from `lean.css`, and bundle the deck's
images as theme assets (written verbatim to `<outputDir>/assets/…`).

We read the CSS here instead of `include_str`: `include_str` bakes it in at
*compile* time and Lake won't re-read it when only `lean.css` changes, so edits
would silently ship stale. Reading it in `main` means editing `lean.css` (or an
image) needs only a re-run of `lake exe slides` — no rebuild. -/
def loadTheme : IO CustomTheme := do
  let base ← findBase
  let css ← IO.FS.readFile (base / "lean.css")
  -- every file in `assets/` ships verbatim to `<outputDir>/assets/`, so dropping a
  -- screenshot in there needs only a re-run.  A missing directory is not an error:
  -- a slide referencing an absent image shows its placeholder instead.
  let assetDir := base / "assets"
  let assets ← if ← assetDir.pathExists then do
      let entries ← assetDir.readDir
      entries.mapM fun e => do
        return { filename := "assets/" ++ e.fileName, contents := ← IO.FS.readBinFile e.path }
    else pure #[]
  -- stagger.js (per-item reveal fragments for `:::class "steps"` lists) is deliberately
  -- NOT loaded: every slide appears in full, with no staged reveals. To restore the
  -- staggered behaviour, ship it as an asset here and add it back to `extraJs` below.
  -- autofit.js is loaded: it reshapes reveal's slide box to the window and shrinks a
  -- slide whose content still overruns it. `extraJs` carries URLs rather than contents,
  -- so the file ships here and `main` names that URL.
  -- ref: docs/website.md § The deck's sizes
  let autofit ← IO.FS.readBinFile (base / "autofit.js")
  return {
    stylesheet     := { filename := "lean.css", contents := ⟨css⟩ },
    assets         := assets.push { filename := "assets/autofit.js", contents := autofit },
    -- light theme → light highlight.js theme (not the dark default)
    highlightTheme := HighlightTheme.forRevealTheme "white"
  }

/-- Shared config. The output directory is the published path: the deck is served
from `<repo>/slides/`, beside `index.html` and `web/`, so the URL carries no
underscore-prefixed segment (which GitHub Pages' Jekyll step would skip). -/
def cfg (theme : CustomTheme) (out : System.FilePath) : Config where
  theme       := .custom theme
  outputDir   := out
  slideNumber := true
  transition  := "slide"
  width       := 1280
  height      := 720
  margin      := 0.0
  center      := false

/-- The files every deck shares, hoisted one level up and referenced from there. -/
def sharedFiles : Array String := #["lib", "assets", "lean.css", "paralever.css"]

/-- Move a deck's shared files into its parent folder and point the deck at them there.

`slidesMain` writes every deck a full copy of the vendored reveal.js (`lib/`, 2.9 MB), the theme
stylesheet, the `extraCss` files and the theme assets, and references them from `index.html` by a
bare relative name. There is no base-path option, so the sharing is done after the write: each
named reference in `index.html` gains a `../`, and the file itself is moved up beside its
siblings. Every deck writes the same bytes, so whichever deck runs last is the one whose copy is
kept.

What stays in the deck's own folder is `index.html` and `-verso-docs.json` — the snippet data each
page fetches relative to its own URL, which is per-deck and must not be shared. -/
def shareWithParent (deck : System.FilePath) (names : Array String := sharedFiles) : IO Unit := do
  let parent := deck.parent.getD "."
  let page := deck / "index.html"
  let mut html ← IO.FS.readFile page
  for name in names do
    html := (html.replace s!"\"{name}\"" s!"\"../{name}\"").replace s!"\"{name}/" s!"\"../{name}/"
    let src := deck / name
    let dst := parent / name
    if ← src.pathExists then
      if ← dst.isDir then IO.FS.removeDirAll dst
      else if ← dst.pathExists then IO.FS.removeFile dst
      IO.FS.rename src dst
  IO.FS.writeFile page html

/-- Build every deck. **Add one line per new deck**: give it a sub-folder of `slides/`, point it at
that deck's `#doc` with `%doc <ModuleName>` (the bare Lean module name — e.g. `Slides`, not
`Slides.lean`), and hoist its shared files. `slides/index.html`, which lists the decks, is written
by hand and is not generated here. -/
def main : IO UInt32 := do
  let base ← findBase
  let theme ← loadTheme
  -- per-deck overrides, layered on top of lean.css (read at runtime too)
  let deckCss ← IO.FS.readFile (base / "paralever.css")
  let deck (out : System.FilePath) : Config := { cfg theme out with
    extraCss := #[{ filename := "paralever.css", contents := ⟨deckCss⟩ }],
    extraJs  := #["assets/autofit.js"] }
  discard <| slidesMain (deck "slides/main") (doc := %doc Slides)
  shareWithParent "slides/main"
  discard <| slidesMain (deck "slides/isp") (doc := %doc IspSlides)
  shareWithParent "slides/isp"
  return 0
