#!/usr/bin/env bash
# Build every Lean snippet the website shows, with verso-snippets.
#
# Each snippet is a real region of a real module — marked `-- ANCHOR: site-…` in the
# source — highlighted by SubVerso against this project's own imports and rendered by
# verso-snippets' `render-snippet` into one self-contained HTML file under
# `web/snippets/`. The pages embed those files in `<iframe>`s, so the code on the site
# is the code in the library, with its real types on hover and its real proof states.
#
# The three `prove` outputs are generated first, since they are what the tool writes
# rather than source: `paralever prove` emits a module, it is placed as the scratch
# `Snippet` lib (gitignored), highlighted, rendered, and removed.
#
# Needs the verso-snippets checkout for the renderer only. That binary reads SubVerso
# JSON and is input-independent, so it is built once in its own repo, against its own
# toolchain, and this project's build is untouched.
#
#   ./web/build-snippets.sh                 # all of them
#   ./web/build-snippets.sh race-sites-iff  # just the named ones
#
# See docs/website.md.
set -euo pipefail
cd "$(dirname "$0")/.."

SNIPPETS_REPO="${SNIPPETS_REPO:-$HOME/lean/verso-snippets}"
RENDER="$SNIPPETS_REPO/.lake/build/bin/render-snippet"
OUT="web/snippets"
HL=".lake/build/highlighted"

[[ -x "$RENDER" ]] || {
  echo "no renderer at $RENDER" >&2
  echo "build it once:  (cd $SNIPPETS_REPO && lake build render-snippet)" >&2
  exit 1
}
mkdir -p "$OUT"

# id │ module │ anchor │ label
MANIFEST=$(cat <<'EOF'
parseqeq|Paralever.Theory.Sequentialize|site-parseqeq|ParSeqEq — what "the same outcomes" means
parm|Paralever.Core.ParM|site-parm|ParM — a program as data
runseq|Paralever.Core.Access|site-runseq|runSeq — the sequential reading
step|Paralever.Core.Semantics|site-step|step — every schedule at once
footprint|Paralever.Core.Access|site-footprint|Footprint — what a computation touches
accesses-childs|Paralever.Core.Access|site-accesses-childs|accessesChilds — staggered measurement
par-seq-eq|Paralever.Theory.Sequentialize|site-par-seq-eq|par_seq_eq — the metatheorem
wfb-par-seq-eq|Prl.Lang.Core|site-wfb-par-seq-eq|par_seq_eq — one Bool, then the theorem
rewrite-sound|Paralever.AutoPar.Rewrite|site-rewrite-sound|rewrite_sound — no hypothesis
dag-edges|Paralever.AutoPar.Dag|site-dag-edges|the four dependence cases, as #guards
follow-sound|Paralever.Search.RaceSearch|site-follow-sound|follow_sound — a schedule is a run
race-sites-iff|Paralever.Search.RaceSearch|site-race-sites-iff|raceSites_nil_iff — the scan is complete
race-site-cases|Paralever.Search.RaceSearch|site-race-site-cases|what the scan finds, as #guards
writing|Examples.Language.Writing|site-writing|a program in the surface language
writing-theorem|Examples.Language.Writing|site-writing-theorem|its footprint, and its verdict
prl-file|Examples.Language.Files|site-prl-file|prl_file — the nine files, read while Lean elaborates
file-theorem|Examples.Language.Files|site-file-theorem|one theorem per accepted file
mlir-doall|Examples.Mlir.Files|site-mlir-doall|an MLIR file, lowered at elaboration time
mlir-theorem|Examples.Mlir.Files|site-mlir-theorem|and the theorem that follows
EOF
)

# id │ prove arguments │ label  — the module `paralever prove` writes
GENERATED=$(cat <<'EOF'
proof-sum|Examples/Language/sum.prl|prove sum.prl — the wfB route
proof-scatter|Examples/Language/scatter.prl|prove scatter.prl — the per-heap route
proof-chain|--autopar Examples/Language/chain.prl|prove --autopar chain.prl
EOF
)

# With no arguments every snippet is wanted; otherwise only the ids named.
want() {
  local id="$1"; shift
  [[ $# -eq 0 ]] && return 0
  for w in "$@"; do [[ "$id" == "$w" ]] && return 0; done
  return 1
}
WANTED=("$@")

# A snippet is written to be opened as a page. Appending web/snippet-overrides.css
# after its own <style> is what makes it work inside an iframe: the infoview beside
# the code rather than under it, long lines wrapped, and the full frame width used.
inject() {  # <html> <css>
  awk -v css="$2" '
    /<\/head>/ && !hit { print "<style>"; while ((getline l < css) > 0) print l; print "</style>"; hit = 1 }
    { print }
  ' "$1" > "$1.new" && mv "$1.new" "$1"
}

render() {  # <json> <id> <label> [extra flags…]
  local json="$1" id="$2" label="$3"; shift 3
  "$RENDER" "$json" "$OUT/$id.html" --label "$label" "$@" >/dev/null
  inject "$OUT/$id.html" web/snippet-overrides.css
  printf '  %-18s %6s KB\n' "$id" "$(( $(stat -c%s "$OUT/$id.html") / 1024 ))"
}

echo "== library snippets"
while IFS='|' read -r id mod anchor label; do
  [[ -z "$id" ]] && continue
  want "$id" ${WANTED+"${WANTED[@]}"} || continue
  lake build "$mod:highlighted" >/dev/null
  render "$HL/${mod//.//}.json" "$id" "$label" --anchor "$anchor"
done <<< "$MANIFEST"

echo "== generated proofs"
while IFS='|' read -r id args label; do
  [[ -z "$id" ]] && continue
  want "$id" ${WANTED+"${WANTED[@]}"} || continue
  # shellcheck disable=SC2086
  .lake/build/bin/paralever prove $args -o Snippet.lean >/dev/null
  # `prove` writes the path it was handed, absolutised. Shorten it to the repo-relative
  # one so the snippet shows a path a reader can use, and so `prl_file` still resolves:
  # it reads relative to the file that names it, which is now the repository root.
  sed -i "s|$PWD/||g" Snippet.lean
  lake build Snippet:highlighted >/dev/null
  render "$HL/Snippet.json" "$id" "$label"
  rm -f Snippet.lean
done <<< "$GENERATED"

echo "done — $(ls "$OUT" | wc -l) files, $(du -sh "$OUT" | cut -f1)"
