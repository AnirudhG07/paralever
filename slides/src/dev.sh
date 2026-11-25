#!/usr/bin/env bash
# ---------------------------------------------------------------------------
# Live-edit the paralever slides.
#
#   bash slides/src/dev.sh
#
# Watches slides/src/*.lean and *.css; on every save it re-runs `lake -q exe slides`,
# and a browser-sync server auto-reloads the page in your browser.
#
# Notes
#   * CSS edits (lean.css / paralever.css) are cheap — the theme is read at
#     runtime, so no Lean is recompiled; the rebuild is ~1-2s.
#   * Content edits (main/Slides.lean, isp/IspSlides.lean) recompile that deck's
#     module (a few seconds) — inherent to a compiled-Lean deck, not something a
#     watcher removes.
#   * The sources are `slides/src/`; the generated decks are `slides/` beside it,
#     which is the server's root, so `/` is the hand-written deck list and each
#     deck is one folder below it. The watcher never sees the output, so a
#     rebuild cannot retrigger itself.
#   * A failed build leaves the last good page up; fix the error and save again.
#   * Ctrl-C stops both the watcher and the server.
# ---------------------------------------------------------------------------
set -uo pipefail

# repo root = two levels up from this script (slides/src/dev.sh)
cd "$(dirname "$(readlink -f "$0")")/../.."

OUT="slides"
SRC="slides/src"
PORT="${PORT:-3000}"

DECK="${1:-}"
case "$DECK" in
  ""|main|isp) ;;
  *) echo "usage: bash dev.sh [main|isp]"; exit 2 ;;
esac

# Lake 4.36 prints "`Task.get` called from a `(sync := true)` task" plus a 20-line C
# backtrace for every job it runs — 360,000 lines on a full build of this repo. It comes
# from Lake's own `Lake.Module.computeExportInfo`, not from anything here, and it is
# harmless. `-q` hides it on a successful build; on a failed one Lake replays the job
# logs, so the filter drops what is left. `set -o pipefail` is on above, so the pipe
# still reports the build's exit status and errors and warnings pass through untouched.
build_slides() {
  lake -q exe slides 2>&1 | grep -v \
    -e '^`Task.get` called from' \
    -e '^backtrace:$' \
    -e '^info: stdout/stderr:$' \
    -e '^/home/.*/lib/lean/lib.*\.so' \
    -e '^/lib/[a-z0-9_]*-linux-gnu/lib'
}

command -v inotifywait >/dev/null || { echo "need inotifywait (apt install inotify-tools)"; exit 1; }
command -v npx         >/dev/null || { echo "need node/npx for the live-reload server"; exit 1; }

echo "▶ initial build…"
build_slides || echo "  ✗ initial build failed — fix and save to retry"

# live-reload static server: serves $OUT.  It watches nothing — the rebuild
# loop below tells it when to reload, so the only inotify watch this script
# takes is inotifywait's on $SRC.
# LAN IP others on your Wi-Fi can reach (e.g. 10.x / 192.168.x)
IP=$(ip route get 8.8.8.8 2>/dev/null | grep -oP 'src \K[0-9.]+')
[ -z "$IP" ] && IP=$(hostname -I 2>/dev/null | awk '{print $1}')
[ -z "$IP" ] && IP=127.0.0.1
echo "▶ serving (first run downloads browser-sync)…"
echo "    Local:    http://localhost:$PORT"
echo "    Network:  http://$IP:$PORT   ← open on your phone / share on Wi-Fi"
echo "    Decks:    /main/index.html  (the project talk)   /isp/index.html  (ISP)"
npx --yes browser-sync start \
    --server "$OUT" --startPath /index.html \
    --no-notify --port "$PORT" &
SERVER_PID=$!

cleanup() { echo; echo "▶ stopping…"; kill "$SERVER_PID" 2>/dev/null; exit 0; }
trap cleanup INT TERM

echo "▶ watching $SRC — edit a .lean or .css file and save (Ctrl-C to stop)"
while true; do
  if ! changed=$(inotifywait -r -q -e close_write,create,moved_to --format '%w%f' "$SRC"); then
    echo "  ✗ inotifywait failed — most likely out of file watchers."
    echo "    sudo sysctl -w fs.inotify.max_user_watches=524288"
    cleanup
  fi
  case "$changed" in
    *.lean|*.css) ;;
    *) continue ;;
  esac
  echo "  ↻ $changed → rebuilding…"
  if build_slides; then
    echo "  ✓ rebuilt"
    # a .css change is injected without losing the current slide; anything else
    # changed the generated HTML, so the page is reloaded.
    case "$changed" in
      *.css) npx --yes browser-sync reload --port "$PORT" --files "$(basename "$changed")" ;;
      *)     npx --yes browser-sync reload --port "$PORT" ;;
    esac >/dev/null 2>&1
  else
    echo "  ✗ build failed — page unchanged; fix and save again"
  fi
done
