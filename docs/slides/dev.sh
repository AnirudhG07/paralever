#!/usr/bin/env bash
# ---------------------------------------------------------------------------
# Live-edit the paralever slides.
#
#   bash docs/slides/dev.sh
#
# Watches docs/slides/*.lean and *.css; on every save it re-runs `lake exe slides`,
# and a browser-sync server auto-reloads the page in your browser.
#
# Notes
#   * CSS edits (lean.css / paralever.css) are cheap — the theme is read at
#     runtime, so no Lean is recompiled; the rebuild is ~1-2s.
#   * Content edits (Slides.lean) recompile the deck module (a few seconds) —
#     that's inherent to a compiled-Lean deck, not something a watcher removes.
#   * A failed build leaves the last good page up; fix the error and save again.
#   * Ctrl-C stops both the watcher and the server.
# ---------------------------------------------------------------------------
set -uo pipefail

# repo root = two levels up from this script (docs/slides/dev.sh)
cd "$(dirname "$(readlink -f "$0")")/../.."

OUT="_slides/paralever"
SRC="docs/slides"
PORT="${PORT:-3000}"

command -v inotifywait >/dev/null || { echo "need inotifywait (apt install inotify-tools)"; exit 1; }
command -v npx         >/dev/null || { echo "need node/npx for the live-reload server"; exit 1; }

echo "▶ initial build…"
lake exe slides || echo "  ✗ initial build failed — fix and save to retry"

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
  if lake exe slides; then
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
