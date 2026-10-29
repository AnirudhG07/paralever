/* paralever — the one script every page loads.
   Three things are rendered here: the top bar, the section sidebar and the footer.
   The top bar is not reimplemented: the page links the main site's own
   /src/js/blog-post-header.js (the minimal header, the one the Blogs pages use),
   which injects it into #post-header. That script's links are written for a page
   under /src/, and its link list is the Blogs one, so both are adjusted below.
   A fallback renders the same bar locally if the fetch never lands. */

(function () {
  "use strict";

  var SITE = "https://anirudhg07.github.io";

  /* ── the top bar ────────────────────────────────────────────────────────── */

  // Anirudh Gupta on the left; the uppercase group on the right.
  var BAR_LINKS = [
    ["paralever", "@base@index.html"],
    ["GitHub", "https://github.com/AnirudhG07/paralever"],
    ["Home", SITE]
  ];

  function barLinkHTML(base) {
    return BAR_LINKS.map(function (l) {
      return '<li><a href="' + l[1].replace("@base@", base) +
        '" class="text-stone-600 hover:text-stone-900 transition-colors no-underline">' +
        l[0] + "</a></li>";
    }).join("");
  }

  // The injected bar is the Blogs one: re-root its hrefs and swap its link list.
  function adoptBar(base) {
    var host = document.getElementById("post-header");
    if (!host) return true;
    var nav = host.querySelector("nav");
    if (!nav) return false;
    var brand = nav.querySelector("a");
    if (brand) brand.setAttribute("href", SITE);
    var list = nav.querySelector("ul");
    if (list) list.innerHTML = barLinkHTML(base);
    return true;
  }

  function renderBarFallback(base) {
    var host = document.getElementById("post-header");
    if (!host || host.querySelector("nav")) return;
    host.innerHTML =
      '<nav class="bg-[#f9f8f6]/90 backdrop-blur-md fixed w-full z-50 top-0 start-0' +
      ' border-b border-stone-100 shadow-sm">' +
      '<div class="max-w-screen-xl flex flex-wrap items-center justify-between mx-auto p-4">' +
      '<a href="' + SITE + '" class="flex items-center space-x-3 group no-underline">' +
      '<span class="self-center text-xl font-bold whitespace-nowrap text-stone-900' +
      ' tracking-tight serif italic group-hover:text-stone-500 transition-colors">' +
      "Anirudh Gupta</span></a>" +
      '<div class="md:flex md:w-auto md:order-1">' +
      '<ul class="flex space-x-8 font-bold text-[10px] tracking-[0.2em] uppercase">' +
      barLinkHTML(base) + "</ul></div></div></nav>";
  }

  /* ── the section sidebar ────────────────────────────────────────────────── */

  // One row per page, in reading order. Adding a page is one line.
  var PAGES = [
    ["", "Overview", "where the theorem is stated"],
    ["concept.html", "The theorem", "ParM, Bernstein, par ≡ seq"],
    ["language.html", "The language", "the .prl grammar in full"],
    ["autopar.html", "Autoparallelization", "a chain becomes a tree of forks"],
    ["races.html", "Finding races", "the scan, and the interleaving"],
    ["mlir.html", "From MLIR", "the other front end"],
    ["cli.html", "The command line", "check, run, prove"],
    ["lean.html", "The Lean library", "module by module"]
  ];

  var EXTRAS = [
    ["The talk", "@base@slides/", "the deck, built from the library"],
    ["Source", "https://github.com/AnirudhG07/paralever", "the repository"]
  ];

  function renderSide() {
    var host = document.getElementById("prl-side");
    if (!host) return;
    var base = host.getAttribute("data-base") || "";
    var here = host.getAttribute("data-page") || "";

    var html = '<nav class="side-nav" aria-label="Documentation sections">' +
      '<a class="side-brand" href="' + base + 'index.html">paralever</a>' +
      '<p class="side-tag">parallel ≡ sequential, in Lean 4</p>' +
      '<p class="side-head">Documentation</p><ul class="side-list">';

    PAGES.forEach(function (p) {
      var href = p[0] === "" ? base + "index.html" : base + "web/" + p[0];
      var cur = p[0] === here ? ' aria-current="page"' : "";
      html += "<li><a" + cur + ' href="' + href + '"><span class="side-name">' +
        p[1] + '</span><span class="side-note">' + p[2] + "</span></a></li>";
    });

    html += '</ul><p class="side-head">Elsewhere</p><ul class="side-list">';
    EXTRAS.forEach(function (e) {
      var href = e[1].replace("@base@", base);
      var ext = /^https?:/.test(href) ? ' target="_blank" rel="noopener noreferrer"' : "";
      html += "<li><a" + ext + ' href="' + href + '"><span class="side-name">' +
        e[0] + '</span><span class="side-note">' + e[2] + "</span></a></li>";
    });
    html += "</ul></nav>";
    host.innerHTML = html;
  }

  /* ── the footer ─────────────────────────────────────────────────────────── */

  function renderFooter() {
    var host = document.getElementById("prl-footer");
    if (!host) return;
    var base = host.getAttribute("data-base") || "";
    host.innerHTML =
      '<div class="foot-inner">' +
      '<p class="foot-claim"><strong>paralever</strong> — one metatheorem, proved once: ' +
      "independent branches mean a fork and its sequential reading reach the same " +
      "outcomes under every schedule. After that, each program owes a single " +
      "decidable check.</p>" +
      '<ul class="foot-links">' +
      '<li><a href="https://github.com/AnirudhG07/paralever" target="_blank" rel="noopener noreferrer">Source</a></li>' +
      '<li><a href="' + base + 'slides/">The talk</a></li>' +
      '<li><a href="' + base + 'index.html">Documentation</a></li>' +
      '<li><a href="/src/projects.html">Other projects</a></li>' +
      "</ul>" +
      '<p class="foot-fine">Built by <a href="' + SITE + '">Anirudh Gupta</a>. ' +
      "Lean 4, toolchain <code>leanprover/lean4:v4.34.0</code>. Every verdict, " +
      "transcript and measurement on these pages is the output of a run in the " +
      "repository — none of it is illustrative.</p>" +
      "</div>";
  }

  /* ── highlighting ───────────────────────────────────────────────────────── */

  // `.prl` is this project's own surface syntax, so highlight.js has no grammar
  // for it. These are the token classes `Lang.highlight` recognizes.
  function registerPrl(hl) {
    hl.registerLanguage("prl", function (h) {
      return {
        name: "prl",
        keywords: {
          keyword: "paralever def assertParSeq assert on buf let const reg slice copy from free synchronize " +
                   "parallel parfor for if else while in at input print",
          built_in: "zeros ones eye arange full str min max"
        },
        contains: [
          h.COMMENT("--", "$"),
          { className: "string", begin: '"', end: '"' },
          { className: "variable", begin: /%[A-Za-z_][A-Za-z0-9_]*|%[0-9]+/ },
          { className: "number", begin: /\b[0-9]+\b/ },
          { className: "operator", begin: /:=|\|/ }
        ]
      };
    });
  }

  // MLIR generic form: quoted op names, attribute dictionaries, `!`-types.
  function registerMlir(hl) {
    hl.registerLanguage("mlir", function (h) {
      return {
        name: "mlir",
        contains: [
          h.COMMENT("//", "$"),
          { className: "title", begin: /"[a-z_]+\.[a-z_.]+"/ },
          // custom form prints the same op name unquoted
          { className: "title", begin: /\b(?:affine|memref|arith|func|async|scf|index|tensor)\.[a-z_.]+/ },
          { className: "symbol", begin: /@[A-Za-z0-9_]+/ },
          { className: "string", begin: '"', end: '"' },
          { className: "variable", begin: /%[A-Za-z0-9_]+/ },
          { className: "type", begin: /![A-Za-z0-9_.<>x]+|\bmemref<[^>]*>/ },
          { className: "number", begin: /\b[0-9]+\b/ },
          { className: "operator", begin: /->|=/ }
        ]
      };
    });
  }

  /* ── the Lean embeds ────────────────────────────────────────────────────── */

  // Each snippet is its own document, so the iframe has to be told how tall it
  // is. Same origin, so its body is readable; a snippet that switches View
  // changes height, which the ResizeObserver inside it cannot report across the
  // frame, so re-measure on a timer for a few seconds after load as well.
  function sizeEmbeds() {
    document.querySelectorAll("iframe.lean-demo").forEach(function (frame) {
      if (frame.style.height) return;
      var apply = function () {
        try {
          var h = frame.contentWindow.document.body.scrollHeight;
          if (h > 0) frame.style.height = h + 32 + "px";
        } catch (e) {
          /* not loaded yet, or not same-origin */
        }
      };
      frame.addEventListener("load", function () {
        setTimeout(apply, 120);
        var n = 0;
        var t = setInterval(function () {
          apply();
          if (++n > 12) clearInterval(t);
        }, 400);
      });
      try {
        if (frame.contentDocument && frame.contentDocument.readyState === "complete") {
          setTimeout(apply, 120);
        }
      } catch (e) {
        /* cross-origin, which cannot happen for our own snippets */
      }
    });
  }

  // A terminal block: the commands, and what the tool printed. One grammar covers
  // both, because every such block on the site is a session — highlight.js's own
  // `bash` finds almost nothing here, since the commands are `paralever` and
  // `lake` rather than shell builtins.
  function registerConsole(hl) {
    hl.registerLanguage("console", function () {
      return {
        name: "console",
        aliases: ["terminal"],
        // Lookbehind is avoided deliberately: Safari did not support it until
        // 16.4, and one unsupported regex throws and leaves the whole page
        // unhighlighted. Subcommands are keywords instead.
        keywords: {
          keyword: "for in do done if then else fi while",
          built_in: "check run prove autopar convert to-prl to-mlir build exe clone update env cache"
        },
        contains: [
          { className: "comment", begin: /#.*$/ },
          { className: "meta", begin: /^\s*\$ / },
          // what is being run, and how
          { className: "keyword", begin: /\b(paralever|lake|lean|git|python3|ln|mkdir|cd|elan)\b/ },
          { className: "literal", begin: /\s--?[A-Za-z][\w-]*/ },
          { className: "string", begin: '"', end: '"' },
          { className: "variable", begin: /\$\{?\w+\}?/ },
          // the verdict is the point of most of these blocks
          { className: "type",
            begin: /\b(race-free|accepted|refused|unsupported|expressible|optimal|wrong|true|false|some|none)\b/ },
          // the label column down the left of a report
          { className: "attr", begin: /^\s{0,4}[a-z][a-z-]{2,}(?=\s{2,})/ },
          // a buffer and its extent, and where it sits
          { className: "title", begin: /\b[A-Za-z_][A-Za-z0-9_]*(?=\s?\[)/ },
          { className: "symbol", begin: /@\d+|↦|←|→|⟨|⟩|&&|\|\|/ },
          { className: "number", begin: /\b\d+(\.\d+)?\b/ }
        ]
      };
    });
  }

  // The two rule definitions on the races page: not a language, so only the parts
  // a reader scans for — the name being defined, the comment, the operators.
  function registerPseudo(hl) {
    hl.registerLanguage("pseudo", function () {
      return {
        name: "pseudo",
        keywords: { keyword: "for in if else and or not", literal: "true false" },
        contains: [
          { className: "comment", begin: /#.*$/ },
          { className: "title", begin: /^[a-zA-Z_][\w]*(?=\()/ },
          { className: "built_in", begin: /\b(loc|isWrite|dedup|concat|any|all|map)\b/ },
          { className: "symbol", begin: /∈|∉|∩|∅|↦|=>|==|&&|\|\|/ },
          { className: "number", begin: /\b\d+\b/ }
        ]
      };
    });
  }

  // The `.prl` grammar, as a grammar: what is being defined, and the literal tokens.
  function registerBnf(hl) {
    hl.registerLanguage("bnf", function () {
      return {
        name: "bnf",
        contains: [
          { className: "comment", begin: /#.*$/ },
          { className: "title", begin: /^[a-z][\w]*(?=\s*::=)/ },
          { className: "symbol", begin: /::=|\||[*?]/ },
          { className: "string", begin: '"', end: '"' },
          { className: "type", begin: /\b[a-z][\w]*(?=\s|\)|\||$)/ }
        ]
      };
    });
  }

  /* ── copy buttons ───────────────────────────────────────────────────────── */

  function wireCopy() {
    document.querySelectorAll(".code-wrap .copy-btn").forEach(function (btn) {
      btn.addEventListener("click", function () {
        var code = btn.closest(".code-wrap").querySelector("code");
        navigator.clipboard
          .writeText(code.innerText)
          .then(function () {
            btn.textContent = "Copied!";
            setTimeout(function () { btn.textContent = "Copy"; }, 2000);
          })
          .catch(function () { btn.textContent = "Error"; });
      });
    });
  }

  /* ── go ─────────────────────────────────────────────────────────────────── */

  document.addEventListener("DOMContentLoaded", function () {
    var side = document.getElementById("prl-side");
    var base = (side && side.getAttribute("data-base")) || "";

    renderSide();
    renderFooter();
    wireCopy();
    sizeEmbeds();

    if (window.hljs) {
      registerPrl(window.hljs);
      registerMlir(window.hljs);
      registerConsole(window.hljs);
      registerPseudo(window.hljs);
      registerBnf(window.hljs);
      window.hljs.highlightAll();
    }

    // blog-post-header.js is also a DOMContentLoaded listener; whichever order the
    // two run in, one of these attempts lands. After half a second, render our own.
    if (!adoptBar(base)) {
      var tries = 0;
      var t = setInterval(function () {
        if (adoptBar(base) || ++tries > 10) {
          clearInterval(t);
          renderBarFallback(base);
        }
      }, 50);
    }
  });
})();
