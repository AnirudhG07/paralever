/* paralever deck — "stagger" helper.
 *
 * Reveal.js has no built-in "reveal each list item in turn"; the mechanism is a
 * `class="fragment"` on every <li>. Writing that by hand (or one :::fragment per
 * bullet) is tedious, so instead: mark a list ONCE in the deck with
 *
 *     :::class "steps"
 *     * first point
 *     * second point
 *     :::
 *
 * and this script promotes each of that list's items into a fragment, so they
 * appear one click at a time.
 *
 * Timing: loaded via `extraJs`, so it runs AFTER reveal.js is loaded and the
 * whole slide DOM is parsed, but BEFORE `Reveal.initialize()` scans fragments —
 * so the items are already fragments when reveal sets up. No Reveal.sync() dance.
 */
(function () {
  document.querySelectorAll(".steps > li").forEach(function (li) {
    li.classList.add("fragment");
  });
})();
