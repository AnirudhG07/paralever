# paralever

Verifying that **parallel programs produce the same output as their sequential counterparts**, in
Lean 4. One metatheorem — independent branches ⇒ `par p q ≡ seqPair p q` under every schedule — and
after that every program reduces to discharging one decidable independence obligation.

**Documentation: <https://anirudhg07.github.io/paralever/>** · the
[talk](https://anirudhg07.github.io/paralever/slides/)

```bash
lake exe cache get                                 # Mathlib oleans, before a first build
lake build paralever                               # ./.lake/build/bin/paralever
paralever check Examples/Language/matmul.prl
```

| | |
|---|---|
| The theorem | [`Paralever/Theory/Sequentialize.lean`](Paralever/Theory/Sequentialize.lean) |
| Worked examples | [`Examples/`](Examples/) — start at [`Tour.lean`](Examples/Tour.lean) |
| Design rationale | [`docs/`](docs/) |
| Plan | [`PLAN.md`](PLAN.md) · reading list [`docs/papers.md`](docs/papers.md) |

## The website

`index.html` and `web/` are the published site; `slides/` is the deck, written by `lake exe slides`.
There is no generator. The theme — the palette, the fonts and the top bar — is *not* copied: every
page links `/src/css/theme.css` and `/src/js/blog-post-header.js` from
[anirudhg07.github.io](https://anirudhg07.github.io) directly, so the site tracks the main one.

Every Lean block on the site is a [verso-snippets](https://github.com/AnirudhG07/verso-snippets)
embed, not highlighted text: hover a name for its type, click a tactic for its goal state. Each one
renders a real anchored region of a real module, so the code on the site is the code in the library.

```
index.html           the cover
web/concept.html     the theorem
web/language.html    the .prl language
web/autopar.html     the parallelizing pass
web/races.html       race detection
web/mlir.html        the MLIR front end
web/cli.html         the command line
web/lean.html        the Lean library
web/snippets/        the 22 Lean snippets (regenerate with `./web/build-snippets.sh`)
slides/              the deck (regenerate with `lake exe slides`)
```

Served from the repository root, so GitHub Pages wants *Deploy from a branch* → `main` → `/ (root)`.
`.nojekyll` is required and present. How it all fits together, and how to preview it locally:
[`docs/website.md`](docs/website.md).
