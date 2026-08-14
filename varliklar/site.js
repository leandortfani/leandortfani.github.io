/* ==========================================================================
   Kanıt Defteri — istemci tarafı
   1) tema düğmesi   2) KaTeX   3) Lean 4 renklendirici   4) kopyala + TOC
   ========================================================================== */

(function () {
  "use strict";

  /* ------------------------------------------------------------ 1. tema */

  var kok = document.documentElement;

  function temaAyarla(t) {
    kok.setAttribute("data-tema", t);
    try { localStorage.setItem("tema", t); } catch (e) {}
  }

  document.addEventListener("click", function (e) {
    var d = e.target.closest && e.target.closest("#tema-dugme");
    if (!d) return;
    temaAyarla(kok.getAttribute("data-tema") === "koyu" ? "acik" : "koyu");
  });

  /* ----------------------------------------------------------- 2. KaTeX */

  function matematigiIsle() {
    if (typeof window.renderMathInElement !== "function") return;
    window.renderMathInElement(document.body, {
      delimiters: [
        { left: "\\[", right: "\\]", display: true },
        { left: "\\(", right: "\\)", display: false }
      ],
      ignoredTags: ["script", "noscript", "style", "textarea", "pre", "code", "option"],
      throwOnError: false,
      errorColor: "#bf2f2f",
      strict: false,
      trust: false,
      macros: {
        "\\R": "\\mathbb{R}",
        "\\N": "\\mathbb{N}",
        "\\Z": "\\mathbb{Z}",
        "\\Q": "\\mathbb{Q}",
        "\\C": "\\mathbb{C}",
        "\\eps": "\\varepsilon",
        "\\dd": "\\,\\mathrm{d}",
        "\\abs": "\\left|#1\\right|",
        "\\der": "\\operatorname{der}",
        "\\Kanit": "\\square"
      }
    });
  }

  /* --------------------------------------------------- 3. Lean 4 boyama */

  var ANAHTAR = ("theorem lemma def abbrev example instance structure inductive class " +
    "deriving where with fun let have show from by do match if then else at using " +
    "namespace section end open import variable variables universe noncomputable " +
    "partial mutual private protected local scoped macro notation infixl infixr " +
    "prefix postfix syntax elab set_option attribute calc this return unless " +
    "forall exists obtain axiom abbrev mathlib").split(" ");

  var TAKTIK = ("intro intros exact apply refine rfl rw rwa simp simp_all simpa dsimp " +
    "ring ring_nf field_simp linarith nlinarith positivity omega decide norm_num " +
    "push_cast push_neg induction cases rcases obtain constructor use exists " +
    "left right unfold subst contradiction exfalso trivial assumption specialize " +
    "gcongr polyrith aesop tauto nlinarith interval_cases " +
    "first repeat all_goals any_goals try focus conv congr ext funext " +
    "existsi refine' change convert filter_upwards continuity measurability " +
    "fun_prop apply_fun norm_cast").split(" ");

  var KWS = {}, TKS = {};
  ANAHTAR.forEach(function (k) { KWS[k] = 1; });
  TAKTIK.forEach(function (k) { TKS[k] = 1; });

  var TIPLER = { "Nat": 1, "Int": 1, "Real": 1, "Prop": 1, "Type": 1, "Sort": 1,
    "Bool": 1, "List": 1, "Set": 1, "Finset": 1, "Polynomial": 1, "Complex": 1,
    "Rat": 1, "Filter": 1, "Function": 1, "Option": 1, "Sigma": 1, "Subtype": 1 };

  var KACIS = { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" };
  function kac(s) { return s.replace(/[&<>"]/g, function (c) { return KACIS[c]; }); }

  var DESEN = new RegExp([
    "(\\/-[\\s\\S]*?-\\/)",                       // 1 blok yorum
    "(--[^\\n]*)",                                // 2 satır yorum
    "(\"(?:[^\"\\\\]|\\\\.)*\")",                 // 3 metin
    "(@\\[[^\\]]*\\])",                           // 4 öznitelik
    "(:=|=>|<->|->|<-|\\u2192|\\u2190|\\u21a6|\\u27f6|\\u22a2)",  // 5 ok/atama
    "([A-Za-z_\\u0391-\\u03c9\\u1d62\\u2080-\\u2089][A-Za-z0-9_'!?\\u0391-\\u03c9\\u1d62\\u2080-\\u2089]*" +
      "(?:\\.[A-Za-z0-9_'!?]+)*)",                // 6 tanımlayıcı (noktalı)
    "(\\d+(?:\\.\\d+)?)",                         // 7 sayı
    "([\\u2115\\u2124\\u211a\\u211d\\u2102])",    // 8 sayı kümeleri
    "([\\u2200\\u2203\\u2194\\u2227\\u2228\\u00ac\\u2264\\u2265\\u2260\\u2248\\u2208" +
      "\\u2209\\u2286\\u2282\\u222a\\u2229\\u2211\\u220f\\u222b\\u221a\\u00b1\\u2218" +
      "\\u2261\\u27e8\\u27e9\\u230a\\u230b\\u2016\\u00b7\\u00d7\\u2205\\u25b8\\u220e" +
      "\\u25a1\\u2223\\u207b\\u00b9])"            // 9 semboller
  ].join("|"), "g");

  function leanBoya(kod) {
    var cikti = "", son = 0, m;
    DESEN.lastIndex = 0;
    while ((m = DESEN.exec(kod)) !== null) {
      if (m.index > son) cikti += kac(kod.slice(son, m.index));
      var t = m[0], sinif = null;

      if (m[1] || m[2]) sinif = "l-yrm";
      else if (m[3]) sinif = "l-str";
      else if (m[4]) sinif = "l-att";
      else if (m[5]) sinif = "l-sym";
      else if (m[6]) {
        var bas = t.split(".")[0];
        if (t === "sorry") sinif = "l-srr";
        else if (KWS[t]) sinif = "l-kw";
        else if (TKS[t] || TKS[bas]) sinif = "l-tk";
        else if (TIPLER[bas] || /^[A-Z]/.test(bas)) sinif = "l-tip";
      }
      else if (m[7]) sinif = "l-say";
      else if (m[8]) sinif = "l-tip";
      else if (m[9]) sinif = "l-sym";

      cikti += sinif ? '<span class="' + sinif + '">' + kac(t) + "</span>" : kac(t);
      son = m.index + t.length;
    }
    cikti += kac(kod.slice(son));
    return cikti;
  }

  function koduBoya() {
    document.querySelectorAll('pre.kod[data-dil="lean"] > code').forEach(function (el) {
      el.innerHTML = leanBoya(el.textContent);
    });
  }

  /* ------------------------------------------------ 4. kopyala + TOC */

  function kopyalaDugmeleri() {
    document.querySelectorAll("pre.kod").forEach(function (pre) {
      var d = document.createElement("button");
      d.type = "button";
      d.className = "kopyala";
      d.textContent = "kopyala";
      d.addEventListener("click", function () {
        var kod = pre.querySelector("code");
        var yaz = navigator.clipboard && navigator.clipboard.writeText
          ? navigator.clipboard.writeText(kod.textContent)
          : Promise.reject();
        yaz.then(function () {
          d.textContent = "kopyalandı";
          setTimeout(function () { d.textContent = "kopyala"; }, 1400);
        }, function () {
          d.textContent = "olmadı";
          setTimeout(function () { d.textContent = "kopyala"; }, 1400);
        });
      });
      pre.appendChild(d);
    });
  }

  function tocIzle() {
    var baglar = document.querySelectorAll(".toc a");
    if (!baglar.length || !("IntersectionObserver" in window)) return;
    var harita = {};
    baglar.forEach(function (a) { harita[a.getAttribute("href").slice(1)] = a; });

    var basliklar = [];
    Object.keys(harita).forEach(function (k) {
      var h = document.getElementById(k);
      if (h) basliklar.push(h);
    });

    var gozlemci = new IntersectionObserver(function (girisler) {
      girisler.forEach(function (g) {
        if (!g.isIntersecting) return;
        baglar.forEach(function (a) { a.classList.remove("etkin"); });
        var a = harita[g.target.id];
        if (a) a.classList.add("etkin");
      });
    }, { rootMargin: "0px 0px -75% 0px", threshold: 0 });

    basliklar.forEach(function (h) { gozlemci.observe(h); });
  }

  /* ---------------------------------------------------------- başlangıç */

  function basla() {
    koduBoya();
    kopyalaDugmeleri();
    matematigiIsle();
    tocIzle();
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", basla);
  } else {
    basla();
  }
})();
