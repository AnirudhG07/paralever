# The website

`index.html`, `web/` and `slides/` are the published site, served from the repository root at
<https://anirudhg07.github.io/paralever/>. There is no generator and no build step for the prose:
the pages are hand-written HTML. Two things *are* built — the deck, by `lake exe slides`, and the
Lean snippets, by `web/build-snippets.sh`.

```text
index.html              the cover
web/*.html              seven pages: concept, language, autopar, races, mlir, cli, lean
web/css/site.css        every rule the pages use that the main site does not already give
web/js/site.js          the top bar, the sidebar, the footer, the embeds, the .prl/.mlir grammars
web/snippets/*.html     22 verso-snippets files — one per Lean block on the site
web/build-snippets.sh   what writes them
slides/                 the deck (`lake exe slides`)
.nojekyll               required: GitHub Pages' Jekyll step skips `_`-prefixed paths
```

GitHub Pages must be set to *Deploy from a branch* → `main` → `/ (root)`.

## The theme is linked, not copied

Both repositories serve from `anirudhg07.github.io`, so `/src/…` resolves from `/paralever/…`.
Every page links the main site's own stylesheet and header script:

```html
<link rel="stylesheet" href="/src/css/theme.css" />
<script src="/src/js/blog-post-header.js" defer></script>
```

Nothing is duplicated, so a restyle of the main site reaches these pages without a commit here.
`blog-post-header.js` is the minimal header the Blogs pages use — the name on the left, a short
uppercase link group on the right. It writes its links for a page under `/src/`, and its link group
is the Blogs one, so `site.js` re-roots the name and replaces the group with `paralever · GitHub ·
Home`. If the script never arrives, `site.js` renders the same bar from the same classes, so the
bar cannot go missing.

The section nav is a fixed left column below the bar, rendered from `site.js`'s `PAGES` table.
Adding a page is one HTML file plus one row in that table.

## Every Lean block is a verso-snippets embed

No Lean on the site is highlighted by a JavaScript grammar. Each block is an `<iframe>` holding one
self-contained file from `web/snippets/`, produced by [verso-snippets][vs] from the real module:
hover any name for its type, click a tactic for the goal state at that point, and switch between
Hover, Infoview and Literate in the snippet's own header. The code shown is the code in the
library, highlighted by the compiler that checked it.

[vs]: https://github.com/AnirudhG07/verso-snippets

```text
Paralever/Core/Access.lean          the source, with -- ANCHOR: site-runseq … ANCHOR_END
        │
        │  lake build Paralever.Core.Access:highlighted        (SubVerso)
        ▼
.lake/build/highlighted/Paralever/Core/Access.json             tokens, hovers, proof states
        │
        │  render-snippet … --anchor site-runseq               (Verso's HTML library)
        ▼
web/snippets/runseq.html                                       one self-contained file
        │
        │  <iframe class="lean-demo" src="snippets/runseq.html">
        ▼
web/concept.html
```

### The embeds are overridden, deliberately

A snippet is written to be *opened as a page*, and three of its defaults are wrong inside an
iframe. `web/snippet-overrides.css` is appended to every rendered file, after the snippet's own
styles, by `build-snippets.sh`:

| default | inside a frame | override |
|---|---|---|
| the infoview panel stacks below the code under **720px** | the prose column is 704px, so the panel never once sat beside the code | the stack point moves to 560px — a phone, which is what it was for |
| long lines scroll horizontally inside the box | a scrollbar inside a frame inside a page is unreachable | lines wrap, with a hanging indent so a continuation is visibly not a new line |
| the body centres itself in 880px and pads for a window | the frame already is the window | fill the width given |

The embed is also let out of the prose column: `.lean-embed` cancels the section's `px-6 md:px-12
lg:px-24` gutters, so code gets the full column width (896px at a desktop width) rather than the
704px the text gets. Together with the 560px stack point, the panel now seats beside the code from
a 640px viewport up, where before it did so at no width at all.

Editing a file under `web/snippets/` by hand is lost on the next build. Change
`web/snippet-overrides.css` and rebuild.

### Docstrings stay out

An anchor sits **below** a declaration's docstring, not above it, so the snippet shows the
declaration. The page's own prose is where the explaining belongs, and the docstring is still one
hover away. The one exception is `ParM`'s `par` constructor, whose docstring says the thing the
whole project rests on — that `par` is the only constructor Lean does not already give a meaning —
and which sits mid-region where no anchor can exclude it.

A region is selected by an anchor comment pair in the source:

```lean
-- ANCHOR: site-runseq
@[simp, grind .]
def runSeq {τ : Type} : ParM τ → State → τ × State
  | .pure a, σ => (a, σ)
  …
-- ANCHOR_END: site-runseq
```

Anchor comments are a SubVerso feature. They are ordinary Lean comments, they are stripped from the
rendered output, and an anchor placed above a declaration's docstring carries that docstring into
the snippet. Every anchor on the site is named `site-…` so `grep -rn "ANCHOR: site-"` finds the
whole set.

**The site cannot drift from the library.** A snippet is not a copy of a declaration, it is that
declaration rendered. Rename `runSeq` and the snippet shows the new name after one rebuild; delete
it and `build-snippets.sh` fails rather than publishing stale code.

### The three generated proofs

`web/cli.html` shows what `paralever prove` writes, which is not a source file. The script generates
it, places it as the scratch `Snippet` library (gitignored, declared in `lakefile.toml` only so the
`:highlighted` facet applies), builds it, renders it, and deletes it. Because the facet build drives
the compiler, a generated module that Lean does not accept cannot produce a snippet — the page can
only show proofs that check.

`prove` writes the absolute path it was handed; the script shortens it to the repository-relative
one, which still resolves because `prl_file` reads relative to the file naming it.

### Rebuilding

```bash
./web/build-snippets.sh                 # all 22, about 40s on a built tree
./web/build-snippets.sh race-sites-iff  # just the named ones
```

The renderer lives in the verso-snippets checkout and is built once:

```bash
(cd ~/lean/verso-snippets && lake build render-snippet)
```

Set `SNIPPETS_REPO` if it is elsewhere. It is **not** a dependency of this project. `render-snippet`
reads SubVerso JSON and is input-independent, so it builds against its own toolchain (Lean 4.31.0)
and renders JSON this project's SubVerso (4.34.0) produced. Requiring the package instead would
force one `verso` revision across both, which is why the renderer is invoked directly.

## Previewing locally

The pages reference `/src/…` on the main site, so a preview needs both trees under one root:

```bash
mkdir -p /tmp/site && cd /tmp/site
ln -s ~/Projects/anirudhg07.github.io/src src
ln -s ~/Projects/anirudhg07.github.io/assets assets
ln -s ~/lean/paralever paralever
python3 -m http.server 8000      # http://localhost:8000/paralever/
```

Same origin matters for more than the theme: `site.js` sizes each embed by reading its document's
`scrollHeight`, which a cross-origin frame would refuse.

## Everything else in a code block

Lean is the only language with a real elaborator behind it here. The rest is highlighted by
highlight.js with four grammars written in `site.js`, because no published grammar fits:

| class | what it covers |
|---|---|
| `language-prl` | the surface language — `paralever { … }` and `.prl` files |
| `language-mlir` | MLIR generic form: quoted op names, `%`-values, `!`-types |
| `language-console` | a terminal session, command *and* output: `paralever`/`lake` and their subcommands, flags, the label column of a report, buffer extents, and the verdict |
| `language-bnf`, `language-pseudo` | the `.prl` grammar, and the two rule definitions on the races page |

`language-console` replaced highlight.js's own `bash`, which coloured almost nothing: the commands
in these blocks are `paralever` and `lake`, not shell builtins, so one block came out with a single
highlighted token. No grammar uses lookbehind — Safari did not support it until 16.4, and one
unsupported regex throws and leaves the whole page unhighlighted.

## Figures

Every figure is HTML or inline SVG — `.dgm` in `site.css` — never a `<pre>` of box-drawing
characters. Pseudocode, grammars and transcripts stay code blocks. SVG `<marker>` ids are
per-page, since several figures can share one page.

Figures name things in plain language, because a figure is the one place a reader cannot look a
name up: the box both front ends converge on says *a Paralever program*, not `Layout × ParProg`.
Module names belong in the small captions beside a step, which is where "where this lives in the
code" goes.

## The deck's sizes

`reveal.js` lays every slide out on one box of a fixed size — 1280 × 720 here, set in
`SlidesMain.lean`'s `cfg` — and then scales that whole box to the window with a CSS transform.
Lengths in the deck's stylesheets are therefore in **box pixels**, and a length in `vh` or `vw` is
a bug: those measure the *window*, so the transform multiplies them a second time and the layout
changes shape with the window.

The arithmetic: reveal's scale is `min(W/1280, H/720)`. With a window wider than 16∶9 the scale is
`H/720`, and `3.4vh` works out to `3.4 × H/100 ÷ (H/720) = 24.5` box pixels whatever `H` is — the
case the deck was written in, where nothing looks wrong. With a window *narrower* than 16∶9 — a
16∶10 laptop screen, which is every MacBook — the scale is `W/1280` instead and the same `3.4vh`
becomes `43.5 × H/W`, so 27.2 box pixels: eleven percent larger text on the same 720-pixel-tall
box. That is enough to push the last line of a full slide past the bottom edge, where reveal hides
it without a scrollbar. The deck fitted on one machine and not another for no reason visible in the
source. `lean.css` § *base* now gives the conversion (`1vh` = 7.2px, `1vw` = 12.8px) and the files
hold no viewport units.

`docs/slides/autofit.js` does the two things that should still respond to the window:

- **The box follows the window's shape.** On a window that is not 16∶9 it enlarges the box's short
  side — 1280 × 800 for a 16∶10 window — rather than leaving reveal to letterbox it. The box only
  ever grows, so the scale factor and the on-screen text size are unchanged and the extra room is
  room a slide can use. Outside aspect ratios 1.15 to 2.2 it stops and lets reveal letterbox,
  because no slide was written for a window that shape.
- **An overfull slide shrinks instead of clipping.** It measures the union of the slide's children
  against the box and applies `zoom` to them, which re-runs layout, so the measurement after it is
  honest and margins shrink with the text as a `font-size` change would not. The floor is 0.62; a
  slide still overrunning at that point gets `.autofit-scroll`, a scrollbar, which is a visible
  failure rather than a silent one. Measuring again after webfonts load is what catches a font
  falling back to wider metrics.

The script is shipped as a theme asset because `Config.extraJs` carries URLs, not file contents.
