// Syntax highlighting for the code the decks write by hand.
//
// One painter, two vocabularies. `paralever.prl` is the browser-side twin of
// `Lang/Compile/Print.lean`'s `prlTokens` + `highlightHtml` — what `paralever to-prl --html`
// emits: same scan, same six token classes, same CSS names. It exists because the programs on
// these slides are written in the slide source rather than read from a .prl file, so nothing has
// run the Lean printer over them. Paste real `--html` output and it is already painted; `paint`
// skips anything already carrying a token class.
//
// To colour a new language, add one entry to `LANGS`: a selector, a comment opener, a keyword
// list, and whether the keywords are case sensitive. Nothing else changes.
window.paralever = window.paralever || {};
(function (ns) {
  var CLASSES = ["t-com", "t-str", "t-reg", "t-asg", "t-num", "t-kw"];

  // comment · string · register · sigil · number · identifier — first match wins
  function scanner(comment, caseSensitive) {
    return new RegExp(
      "(" + comment + "[^\\n]*)" +
      "|(\"[^\"\\n]*\")" +
      "|(%[A-Za-z_][A-Za-z0-9_']*)" +
      "|(:=|@[A-Za-z0-9_]+)" +
      "|(\\d+)" +
      "|([A-Za-z_][A-Za-z0-9_']*)", caseSensitive ? "g" : "gi");
  }

  // which of the six classes a match belongs to, or null for a plain identifier.
  function classOf(m, keywords, caseSensitive) {
    for (var i = 0; i < 5; i++) if (m[i + 1]) return CLASSES[i];
    if (!m[6]) return null;
    var w = caseSensitive ? m[6] : m[6].toLowerCase();
    return keywords.indexOf(w) >= 0 ? "t-kw" : null;
  }

  // `text` as a fragment with every token wrapped in its class.
  function fragment(text, lang) {
    var out = document.createDocumentFragment(), last = 0, m, re = lang.re;
    re.lastIndex = 0;
    while ((m = re.exec(text)) !== null) {
      var cls = classOf(m, lang.keywords, lang.caseSensitive);
      if (m.index > last) out.appendChild(document.createTextNode(text.slice(last, m.index)));
      if (cls) {
        var s = document.createElement("span");
        s.className = cls;
        s.textContent = m[0];
        out.appendChild(s);
      } else out.appendChild(document.createTextNode(m[0]));
      last = m.index + m[0].length;
    }
    if (last < text.length) out.appendChild(document.createTextNode(text.slice(last)));
    return out;
  }

  // Paint every element matching `lang.selector`, once. Text inside an `<em>` caption, or
  // inside a span that already carries a token class, is left alone.
  ns.paint = function (lang) {
    var blocks = document.querySelectorAll(lang.selector);
    for (var i = 0; i < blocks.length; i++) {
      var el = blocks[i];
      if (el.dataset.hlDone) continue;
      el.dataset.hlDone = "1";
      var walker = document.createTreeWalker(el, NodeFilter.SHOW_TEXT, {
        acceptNode: function (n) {
          return n.parentElement.closest("em, ." + CLASSES.join(", ."))
            ? NodeFilter.FILTER_REJECT : NodeFilter.FILTER_ACCEPT;
        }
      });
      var nodes = [], n;
      while ((n = walker.nextNode())) nodes.push(n);
      for (var j = 0; j < nodes.length; j++)
        nodes[j].parentNode.replaceChild(fragment(nodes[j].nodeValue, lang), nodes[j]);
    }
  };

  // keyword list from `Lang/Compile/Parse.lean`
  var PRL = ["paralever", "parallel", "parfor", "for", "while", "if", "else", "in", "at", "free",
    "synchronize", "print", "def", "assert", "assertParSeq", "on",
    "buf", "let", "const", "reg", "slice", "copy", "from", "min", "max", "zeros", "ones", "eye",
    "arange", "full", "str", "input"];
  // the dialects `MLIR/Parse.lean` reads, plus the ops `MLIR/Emit.lean` writes
  var MLIR = ["func", "module", "memref", "affine", "async", "arith", "scf", "global", "private",
    "dense", "for", "to", "step", "execute", "await", "return", "load", "store", "constant",
    "addi", "muli", "subi", "index", "i64", "i32"];

  ns.langs = [
    { selector: ".prl", comment: "--", keywords: PRL, caseSensitive: true },
    { selector: ".mlir", comment: "//", keywords: MLIR, caseSensitive: false }
  ];
  for (var k = 0; k < ns.langs.length; k++) {
    var l = ns.langs[k];
    l.re = scanner(l.comment, l.caseSensitive);
  }

  function run() { for (var k = 0; k < ns.langs.length; k++) ns.paint(ns.langs[k]); }
  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", run);
  else run();
})(window.paralever);
