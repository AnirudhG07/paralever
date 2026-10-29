/* paralever deck — fit the slide to the window, and the content to the slide.
 *
 * reveal.js lays every slide out on one fixed box (1280×720 here) and scales
 * that box to the window, so a window of another shape gets letterbox bars and a
 * slide that is one line too tall loses that line with no scrollbar. Two things
 * happen here, in this order:
 *
 *   1. `grow` reshapes reveal's box to the window's aspect ratio, enlarging the
 *      short side only. The box therefore never gets smaller than the design box
 *      and the scale factor never changes, so text keeps its size on screen and
 *      the extra room is real room: a 16:10 window gets 1280×800 instead of
 *      1280×720 with bars above and below.
 *   2. `fit` measures what a slide's content actually occupies in that box and
 *      zooms the slide down if it still overruns — the net under a slide that is
 *      too full at every window shape, or whose font fell back to wider metrics.
 *
 * Sizing the deck in box pixels rather than `vh`/`vw` is what makes step 2 rare
 * instead of load-bearing; see lean.css § base.
 * -- ref: docs/website.md § The deck's sizes
 */
(function () {
  var DESIGN_W = 1280, DESIGN_H = 720;
  // beyond these the window is a shape no slide was written for, so letterbox it
  var MIN_ASPECT = 1.15, MAX_ASPECT = 2.2;
  // below this a slide is unreadable, so it scrolls rather than shrink further
  var MIN_ZOOM = 0.62;
  var sizing = false;

  /* ---- 1 · the box ---- */

  function wanted() {
    var el = document.querySelector(".reveal");
    if (!el || !el.clientWidth || !el.clientHeight) return null;
    var a = el.clientWidth / el.clientHeight;
    a = Math.max(MIN_ASPECT, Math.min(MAX_ASPECT, a));
    return a < DESIGN_W / DESIGN_H
      ? { width: DESIGN_W, height: Math.round(DESIGN_W / a) }
      : { width: Math.round(DESIGN_H * a), height: DESIGN_H };
  }

  function grow() {
    var want = wanted();
    if (!want || sizing) return false;
    var now = Reveal.getConfig();
    if (Math.abs(now.width - want.width) < 2 && Math.abs(now.height - want.height) < 2)
      return false;
    sizing = true;
    try { Reveal.configure(want); } finally { sizing = false; }
    return true;
  }

  /* ---- 2 · the content ---- */

  function children(section) {
    return Array.prototype.filter.call(section.children, function (el) {
      return el.getClientRects().length > 0;
    });
  }

  /* How much of the slide the content fills, as a fraction: ≥ 1 is room to
     spare. `getBoundingClientRect` is after reveal's transform, hence the
     divide; `clientWidth`/`clientHeight` are layout values, already in box
     units. A centred flex section overflows both ways, so this measures the
     children's union rect rather than `scrollHeight`, which only ever sees the
     overflow below. */
  function headroom(section) {
    var kids = children(section);
    if (!kids.length) return 1;
    var scale = (Reveal.getScale && Reveal.getScale()) || 1;
    var top = Infinity, bottom = -Infinity, left = Infinity, right = -Infinity;
    kids.forEach(function (el) {
      var r = el.getBoundingClientRect();
      if (r.top < top) top = r.top;
      if (r.bottom > bottom) bottom = r.bottom;
      if (r.left < left) left = r.left;
      if (r.right > right) right = r.right;
    });
    var cs = getComputedStyle(section);
    var availH = section.clientHeight
      - parseFloat(cs.paddingTop) - parseFloat(cs.paddingBottom);
    var availW = section.clientWidth
      - parseFloat(cs.paddingLeft) - parseFloat(cs.paddingRight);
    var h = (bottom - top) / scale, w = (right - left) / scale;
    if (h <= 0 || w <= 0 || availH <= 0 || availW <= 0) return 1;
    return Math.min(availH / h, availW / w);
  }

  function zoom(section, z) {
    children(section).forEach(function (el) {
      if (z === null) el.style.removeProperty("zoom"); else el.style.zoom = z;
    });
  }

  function fit(section) {
    if (!section || section.classList.contains("stack")) return;
    section.classList.remove("autofit-scroll");
    zoom(section, null);
    var k = headroom(section);
    if (k >= 0.995) return;
    // `zoom` re-runs layout, so wrapping can change the height: measure again
    var z = Math.max(MIN_ZOOM, k);
    zoom(section, z);
    if (headroom(section) < 0.995) {
      z = Math.max(MIN_ZOOM, z * headroom(section));
      zoom(section, z);
      if (headroom(section) < 0.995) section.classList.add("autofit-scroll");
    }
  }

  function fitAll() {
    document.querySelectorAll(".reveal .slides section").forEach(fit);
  }

  function relayout() {
    // the box decides the room, so it is reshaped before anything is measured
    if (grow()) requestAnimationFrame(fitAll); else fitAll();
  }

  function start() {
    Reveal.on("slidechanged", function (e) { fit(e.currentSlide); });
    // reveal's own resize fires on every window resize, so one listener is enough
    Reveal.on("resize", relayout);
    relayout();
    // webfonts land after the first paint and change every metric on the page
    if (document.fonts && document.fonts.ready) document.fonts.ready.then(relayout);
  }

  // this file is loaded before `Reveal.initialize()` runs, so wait for the deck
  (function wait() {
    if (window.Reveal && Reveal.isReady && Reveal.isReady()) start();
    else setTimeout(wait, 50);
  })();
})();
