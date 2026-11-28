/* Hlídač — frontend analytika trhu (board/app.js).
 * Statická appka bez build kroku: čte data.json (+ detail/NN.json při otevření detailu).
 * KONTRAKT KLÍČŮ = hlavička scripts/build_board_data.py (měnit jen spolu).
 * Pravidla:
 *  - kontaktní HODNOTY (telefon, e-mail, jméno, ulice) tu nejsou a nebudou, jen příznaky tel/em/adr/sl;
 *  - vše z cizích webů (titulek, popis, lokalita) se escapuje, odkazy jen http(s);
 *  - <img> nikdy loading="lazy" (na GitHub Pages se nikdy nenačetly);
 *  - funkce volané z handlerů jsou top-level, události se delegují (žádné inline onclick).
 * Soubor má dvě části: A) čisté jádro bez DOMu (testovatelné v Node přes globalThis.HLIDAC_CORE),
 * B) UI, které se spustí jen v prohlížeči.
 */
"use strict";

/* ================================================================================================
   A) JÁDRO — konstanty, příprava dat, filtrování, řazení, souhrny, hash, CSV, matice trhu
   ================================================================================================ */

var SHARDS = 32;                // musí sedět s build_board_data.py
var PAGE = 100;                 // max řádků vykreslených naráz
var TYP = { dum: "dům", byt: "byt", pozemek: "pozemek", komercni: "komerční" };
var TYP_ORDER = ["byt", "dum", "pozemek", "komercni"];
var FLAG = { podil: "PODÍL", cena_za_m2: "CENA/M²", mobilheim: "MOBILHEIM", drazba: "DRAŽBA", vykup: "VÝKUP", pronajem: "PRONÁJEM", timeshare: "TIMESHARE" };
var TAGS = { dufek: "Dufek", eva: "Eva", stanek: "Staněk", glamping: "Glamping" };
var SRC = { annonce: "annonce.cz", bazos: "bazoš", bezrealitky: "Bezrealitky" };
var AKCE = {
  koupe: ["KOUPĚ", "buy"], nabor_hned: ["NÁBOR HNED", "hot"], nabor: ["NÁBOR", "warm"], glamping: ["GLAMPING", "glamp"],
  prezentace: ["PREZENTACE", "pres"], sledovat: ["SLEDOVAT", "watch"], preskocit: ["PŘESKOČIT", "skip"], nekontakt: ["NEKONTAKT.", "skip"]
};
var AKCE_ORDER = ["koupe", "nabor_hned", "nabor", "glamping", "prezentace", "sledovat", "preskocit", "nekontakt"];
var ADR = { presna: "přesná", ulice: "aspoň ulice", obec: "jen obec", "-": "žádná" };
var ADR_LIST = ["presna", "ulice", "obec", "-"];          // pořadí v UI
var ADR_CODE = { presna: 3, ulice: 2, obec: 1, "-": 0 };  // kód v P.adr
var SL_LIST = ["s", "m", "?"];
var SL_CODE = { s: 1, m: 2, "?": 0 };
var SL_LABEL = { s: "pravděpodobně soukromník", m: "detail říká makléř", "?": "neověřeno" };
var LIQ_LABEL = { R: "rychlý trh", P: "průměrný trh", S: "pomalý trh" };
var CG_LABEL = { obec: "stejný okres / město", kraj: "stejný kraj" };
// hranice histogramu a posuvníku stáří (dny); poslední koš = „a víc"
var AGE_STOPS = [0, 7, 14, 30, 60, 90, 120, 180, 270, 365, 540, 730, 1100];

// bity podmínek filtru: položka, která neprojde, má ve svém „selhání" příslušný bit
var B = { q: 1, kraj: 2, typ: 4, src: 8, akce: 16, tag: 32, price: 64, m2: 128, area: 256, dv: 512, drop: 1024, nove: 2048,
  clean: 4096, rk: 8192, pc: 16384, pz: 32768, mot: 65536, prez: 131072, age: 262144, tel: 524288, em: 1048576, adr: 2097152,
  sl: 4194304, hid: 8388608 };

/* ---------- drobné pomůcky ---------- */
var NF = new Intl.NumberFormat("cs-CZ", { maximumFractionDigits: 0 });
var NF1 = new Intl.NumberFormat("cs-CZ", { maximumFractionDigits: 1 });
function fmt(n) { return (typeof n !== "number" || n !== n) ? "—" : NF.format(Math.round(n)); }
function fmt1(n) { return (typeof n !== "number" || n !== n) ? "—" : NF1.format(n); }
// krátká cena: 2,4 M / 850 tis.
function fmtM(n) {
  if (typeof n !== "number" || n !== n) return "—";
  if (n >= 1e6) return NF1.format(Math.round(n / 1e5) / 10) + " M";
  if (n >= 1e3) return NF.format(Math.round(n / 1e3)) + " tis.";
  return NF.format(Math.round(n));
}
var ESC = { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" };
function esc(s) { return String(s == null ? "" : s).replace(/[&<>"']/g, function (c) { return ESC[c]; }); }
function safeUrl(u) { return /^https?:\/\//i.test(u || "") ? u : ""; }
function fold(s) { return String(s == null ? "" : s).normalize("NFD").replace(/[̀-ͯ]/g, "").toLowerCase(); }
// Obranná vrstva: do popisů a titulků z cizích webů se občas dostane telefon / e-mail. Hodnoty kontaktů se nesmí zobrazit
// ani exportovat → před zobrazením je zakryjeme. (GPS souřadnice „50.830363565" se nezakrývají: před číslem je tečka.)
var RE_MAIL = /[\w.+-]+@[\w-]+(?:\.[\w-]+)+/g;
var RE_TEL9 = /(^|[^\d.])((?:\+|00)?(?:420|421)?[\s.-]?[1-9]\d{2}[\s.-]?\d{3}[\s.-]?\d{3})(?!\d)/g;
var RE_TEL8 = /(^|[^\d.])([1-9]\d{2}[\s.-]\d{2}[\s.-]\d{2}[\s.-]\d{2})(?!\d)/g;
function redact(s) {
  if (!s) return "";
  return String(s).replace(RE_MAIL, "[e-mail skryt]").replace(RE_TEL9, "$1[tel. skryt]").replace(RE_TEL8, "$1[tel. skryt]");
}
function dayNum(s) {
  var m = /^(\d{4})-(\d\d)-(\d\d)/.exec(s || "");
  return m ? Date.UTC(+m[1], +m[2] - 1, +m[3]) / 864e5 : NaN;
}
function fmtDate(s) {
  var m = /^(\d{4})-(\d\d)-(\d\d)/.exec(s || "");
  return m ? (+m[3]) + ". " + (+m[2]) + ". " + m[1] : (s ? String(s) : "—");
}
function fmtDateShort(s) {
  var m = /^(\d{4})-(\d\d)-(\d\d)/.exec(s || "");
  return m ? (+m[3]) + ". " + (+m[2]) + "." : "";
}
// „2,5m" → 2 500 000, „800k" → 800 000, „1 200 000" → 1200000; jinak null
function parseNum(s) {
  if (s == null) return null;
  s = String(s).trim().toLowerCase().replace(/[\s ]/g, "").replace(/,/g, ".");
  if (!s) return null;
  if (/^\d{1,3}(\.\d{3})+$/.test(s)) s = s.replace(/\./g, "");
  var m = /^(\d+(?:\.\d+)?)(k|tis|m|mil|mio)?$/.exec(s);
  if (!m) return null;
  var v = parseFloat(m[1]);
  if (m[2] === "k" || m[2] === "tis") v *= 1e3; else if (m[2]) v *= 1e6;
  return v;
}
function median(a) {
  var b = [];
  for (var i = 0; i < a.length; i++) if (a[i] === a[i] && a[i] != null) b.push(a[i]);
  if (!b.length) return NaN;
  var t = Float64Array.from(b).sort(), m = t.length >> 1;
  return (t.length & 1) ? t[m] : (t[m - 1] + t[m]) / 2;
}
// Stejný výpočet jako shard_of() v scripts/build_board_data.py (kódy znaků = code pointy, ne UTF-16 jednotky)
function shardOf(id) {
  var s = 0;
  for (var ch of String(id)) s += ch.codePointAt(0);
  return s % SHARDS;
}
function shardFile(id) { var s = shardOf(id); return "detail/" + (s < 10 ? "0" : "") + s + ".json"; }

/* ---------- stav filtrů ---------- */
function defState() {
  return {
    tab: "leady", q: "", kraj: new Set(), typ: new Set(), src: new Set(), akce: new Set(), tag: new Set(),
    adr: new Set(), sl: new Set(), tel: "", em: "",
    pMin: null, pMax: null, m2Min: null, m2Max: null, aMin: null, aMax: null,
    dv: null, drop: false, nove: null, clean: true, rk: false, pc: "", pz: false, mot: null, prMax: null,
    ageMode: "ag", gMin: null, gMax: null,
    hid: 0, sort: "sc", dir: -1, img: true, mt: "m2", d: null
  };
}

/* ---------- příprava dat: typované pole pro rychlé filtrování ---------- */
function prep(Dt) {
  var L = Dt.L || [], n = L.length, meta = Dt.meta || {};
  var P = { L: L, n: n, meta: meta, trh: Dt.trh || {}, gen: meta.gen || "", genDay: dayNum(meta.gen), hasX: false };
  function nan() { var a = new Float64Array(n); a.fill(NaN); return a; }
  P.price = nan(); P.m2 = nan(); P.area = nan(); P.dv = nan(); P.dd = nan(); P.sc = nan(); P.pct = nan(); P.mot = nan();
  P.prez = nan(); P.fd = nan(); P.ao = nan(); P.agm = nan(); P.agr = nan();
  P.pctSrc = new Uint8Array(n);
  ["kraj", "typ", "ak", "src", "tag", "tel", "em", "adr", "sl", "flag", "rk", "pc", "pz", "dropf", "favf", "hidf"].forEach(function (k) { P[k] = new Uint8Array(n); });
  P.q = new Array(n); P.lkey = new Array(n);

  // seznamy hodnot facetů (pořadí podle četnosti, stabilní — počty se mění, pořadí ne)
  var kc = {}, typ = {}, ak = {}, src = {}, tag = {}, i, l;
  for (i = 0; i < n; i++) {
    l = L[i];
    var k = l.k || "?"; kc[k] = (kc[k] || 0) + 1;
    typ[l.c || "?"] = 1; ak[l.ak || "sledovat"] = 1;
    (l.s || []).forEach(function (s) { src[s] = (src[s] || 0) + 1; });
    (l.tg || []).forEach(function (t) { tag[t] = 1; });
  }
  P.krajList = Object.keys(kc).sort(function (a, b) { return (a === "?") - (b === "?") || kc[b] - kc[a]; });
  P.typList = TYP_ORDER.filter(function (t) { return typ[t]; }).concat(Object.keys(typ).filter(function (t) { return TYP_ORDER.indexOf(t) < 0; }));
  P.akList = AKCE_ORDER.filter(function (t) { return ak[t]; }).concat(Object.keys(ak).filter(function (t) { return AKCE_ORDER.indexOf(t) < 0; }));
  var zd = meta.zdroje || src;
  P.srcList = Object.keys(src).sort(function (a, b) { return (zd[b] || 0) - (zd[a] || 0); }).slice(0, 8);
  P.tagList = Object.keys(TAGS).filter(function (t) { return tag[t]; }).concat(Object.keys(tag).filter(function (t) { return !TAGS[t]; })).slice(0, 8);
  P.krajIdx = {}; P.krajList.forEach(function (v, j) { P.krajIdx[v] = j; });
  P.typIdx = {}; P.typList.forEach(function (v, j) { P.typIdx[v] = j; });
  P.akIdx = {}; P.akList.forEach(function (v, j) { P.akIdx[v] = j; });
  P.srcIdx = {}; P.srcList.forEach(function (v, j) { P.srcIdx[v] = j; });
  P.tagIdx = {}; P.tagList.forEach(function (v, j) { P.tagIdx[v] = j; });
  P.idMap = new Map(); P.urlMap = new Map();

  var pctMax = 0;
  for (i = 0; i < n; i++) {
    l = L[i];
    if (l.p != null) P.price[i] = l.p;
    if (l.m2 != null) P.m2[i] = l.m2;
    if (l.a != null) P.area[i] = l.a;
    if (l.dv != null) P.dv[i] = l.dv;
    if (l.dd != null) P.dd[i] = l.dd;
    if (l.sc != null) P.sc[i] = l.sc;
    if (l.pr != null) P.prez[i] = l.pr;
    if (l.ao != null) P.ao[i] = l.ao;
    if (l.ag != null) P.agr[i] = l.ag;
    P.agm[i] = l.ag != null ? l.ag : (l.ao != null ? l.ao : NaN);
    var fdn = dayNum(l.fs);
    if (fdn === fdn && P.genDay === P.genDay) P.fd[i] = Math.max(0, P.genDay - fdn);
    P.kraj[i] = P.krajIdx[l.k || "?"];
    P.typ[i] = P.typIdx[l.c || "?"];
    P.ak[i] = P.akIdx[l.ak || "sledovat"];
    var sb = 0; (l.s || []).forEach(function (s) { if (P.srcIdx[s] != null) sb |= 1 << P.srcIdx[s]; }); P.src[i] = sb;
    var tb = 0; (l.tg || []).forEach(function (t) { if (P.tagIdx[t] != null) tb |= 1 << P.tagIdx[t]; }); P.tag[i] = tb;
    P.tel[i] = l.tel === true ? 1 : (l.tel === "w" ? 2 : 0);
    P.em[i] = l.em ? 1 : 0;
    P.adr[i] = ADR_CODE[l.adr] || 0;
    P.sl[i] = SL_CODE[l.sl] || 0;
    P.flag[i] = (l.fl && l.fl.length) ? 1 : 0;
    P.rk[i] = l.rk ? 1 : 0; P.pc[i] = l.pc ? 1 : 0; P.pz[i] = l.pz ? 1 : 0;
    P.dropf[i] = l.dd > 0 ? 1 : 0;
    var x = l.x;
    if (x && typeof x === "object") {
      P.hasX = true;
      if (typeof x.pct === "number") { P.pct[i] = x.pct; if (x.pct > pctMax) pctMax = x.pct; P.pctSrc[i] = 1; }
      if (typeof x.mot === "number") P.mot[i] = x.mot;
    }
    P.q[i] = fold(redact(l.t || "") + " " + (l.l || "") + " " + (l.k || "") + " " + (TYP[l.c] || ""));
    P.lkey[i] = fold(l.l || "");
    P.idMap.set(l.i, i);
    P.urlMap.set(l.u, i);
    (l.us || []).forEach(function (u) { if (!P.urlMap.has(u)) P.urlMap.set(u, i); });
  }
  // percentil z analytika může být 0–1 nebo 0–100
  P.pctScale = (pctMax > 0 && pctMax <= 1) ? 100 : 1;
  if (P.pctScale !== 1) for (i = 0; i < n; i++) if (P.pctSrc[i] === 1) P.pct[i] *= P.pctScale;

  // záložní percentil Kč/m² v rámci kraj×typ (jen když analytik nedodal x.pct) — hrubý odhad z dat boardu
  var grp = {};
  for (i = 0; i < n; i++) {
    if (!(P.m2[i] === P.m2[i]) || P.flag[i]) continue;
    l = L[i];
    var g1 = (l.k || "?") + "|" + (l.c || "?"), g2 = "*|" + (l.c || "?");
    (grp[g1] || (grp[g1] = [])).push(P.m2[i]); (grp[g2] || (grp[g2] = [])).push(P.m2[i]);
  }
  Object.keys(grp).forEach(function (k) { grp[k] = Float64Array.from(grp[k]).sort(); });
  for (i = 0; i < n; i++) {
    if (P.pctSrc[i] || !(P.m2[i] === P.m2[i])) continue;
    l = L[i];
    var g = grp[(l.k || "?") + "|" + (l.c || "?")];
    if (!g || g.length < 20) g = grp["*|" + (l.c || "?")];
    if (!g || g.length < 20) continue;
    var lo = 0, hi = g.length, v = P.m2[i];
    while (lo < hi) { var mid = (lo + hi) >> 1; if (g[mid] <= v) lo = mid + 1; else hi = mid; }
    P.pct[i] = 100 * lo / g.length; P.pctSrc[i] = 2;
  }
  return P;
}

/* ---------- filtrování + počty facetů v jednom průchodu ----------
   Položka s maskou selhání 0 projde. Položka, která selhala PRÁVĚ v jedné podmínce, se započítá do počtů
   facetu té podmínky (= kolik by jich bylo, kdyby uživatel hodnotu zvolil) — klasické disjunktivní fasety. */
function newCounts(P) {
  return {
    kraj: new Int32Array(P.krajList.length), typ: new Int32Array(P.typList.length), src: new Int32Array(P.srcList.length),
    akce: new Int32Array(P.akList.length), tag: new Int32Array(P.tagList.length), tagNone: 0,
    tel: new Int32Array(3), em: new Int32Array(2), adr: new Int32Array(4), sl: new Int32Array(3),
    age: new Int32Array(AGE_STOPS.length), hid: 0, ageN: 0
  };
}
function ageBin(v) {
  if (!(v === v)) return -1;
  for (var k = AGE_STOPS.length - 1; k >= 0; k--) if (v >= AGE_STOPS[k]) return k;
  return 0;
}
function selFrom(set, idxMap, size) {
  var a = new Uint8Array(size);
  set.forEach(function (v) { var j = idxMap[v]; if (j != null) a[j] = 1; });
  return a;
}
function ageRange(S) {
  return [S.gMin == null ? -Infinity : S.gMin, S.gMax == null ? Infinity : S.gMax];
}
function ageArr(P, S) { return S.ageMode === "ao" ? P.ao : P.agm; }

function filterPass(P, S) {
  var n = P.n, M = new Uint32Array(n), C = newCounts(P), buf = new Int32Array(n), cnt = 0, i, j;
  var qt = S.q ? fold(S.q).split(/\s+/).filter(Boolean) : null;
  if (qt && !qt.length) qt = null;
  var kSel = S.kraj.size ? selFrom(S.kraj, P.krajIdx, P.krajList.length) : null;
  var tSel = S.typ.size ? selFrom(S.typ, P.typIdx, P.typList.length) : null;
  var aSel = S.akce.size ? selFrom(S.akce, P.akIdx, P.akList.length) : null;
  var srcMask = 0; S.src.forEach(function (v) { if (P.srcIdx[v] != null) srcMask |= 1 << P.srcIdx[v]; });
  var tagMask = 0; S.tag.forEach(function (v) { if (P.tagIdx[v] != null) tagMask |= 1 << P.tagIdx[v]; });
  var srcOn = S.src.size > 0, tagOn = S.tag.size > 0;
  var adrSel = null, slSel = null;
  if (S.adr.size) { adrSel = new Uint8Array(4); S.adr.forEach(function (v) { if (ADR_CODE[v] != null) adrSel[ADR_CODE[v]] = 1; }); }
  if (S.sl.size) { slSel = new Uint8Array(3); S.sl.forEach(function (v) { if (SL_CODE[v] != null) slSel[SL_CODE[v]] = 1; }); }
  var pOn = S.pMin != null || S.pMax != null, pLo = S.pMin == null ? -Infinity : S.pMin, pHi = S.pMax == null ? Infinity : S.pMax;
  var mOn = S.m2Min != null || S.m2Max != null, mLo = S.m2Min == null ? -Infinity : S.m2Min, mHi = S.m2Max == null ? Infinity : S.m2Max;
  var aOn = S.aMin != null || S.aMax != null, aLo = S.aMin == null ? -Infinity : S.aMin, aHi = S.aMax == null ? Infinity : S.aMax;
  var A = ageArr(P, S), gOn = S.gMin != null || S.gMax != null, ar = ageRange(S), gLo = ar[0], gHi = ar[1];
  var tel = S.tel, em = S.em;

  for (i = 0; i < n; i++) {
    var f = 0;
    if (qt) { var s = P.q[i]; for (j = 0; j < qt.length; j++) if (s.indexOf(qt[j]) < 0) { f |= B.q; break; } }
    if (kSel && !kSel[P.kraj[i]]) f |= B.kraj;
    if (tSel && !tSel[P.typ[i]]) f |= B.typ;
    if (srcOn && !(P.src[i] & srcMask)) f |= B.src;
    if (aSel && !aSel[P.ak[i]]) f |= B.akce;
    if (tagOn && !(P.tag[i] & tagMask)) f |= B.tag;
    if (pOn) { var p = P.price[i]; if (!(p >= pLo && p <= pHi)) f |= B.price; }
    if (mOn) { var m = P.m2[i]; if (!(m >= mLo && m <= mHi)) f |= B.m2; }
    if (aOn) { var ar2 = P.area[i]; if (!(ar2 >= aLo && ar2 <= aHi)) f |= B.area; }
    if (S.dv != null && !(P.dv[i] >= S.dv)) f |= B.dv;
    if (S.drop && !P.dropf[i]) f |= B.drop;
    if (S.nove != null && !(P.fd[i] <= S.nove)) f |= B.nove;
    if (S.clean && P.flag[i]) f |= B.clean;
    if (S.rk && P.rk[i]) f |= B.rk;
    if (S.pc === "hide" ? P.pc[i] : (S.pc === "only" && !P.pc[i])) f |= B.pc;
    if (S.pz && !P.pz[i]) f |= B.pz;
    if (S.mot != null && !(P.mot[i] >= S.mot)) f |= B.mot;
    if (S.prMax != null && !(P.prez[i] <= S.prMax)) f |= B.prez;
    if (gOn) { var a = A[i]; if (!(a >= gLo && a <= gHi)) f |= B.age; }
    if (tel) {
      var t = P.tel[i];
      if (tel === "any" ? t === 0 : (tel === "yes" ? t !== 1 : (tel === "web" ? t !== 2 : t !== 0))) f |= B.tel;
    }
    if (em && (em === "yes" ? !P.em[i] : P.em[i])) f |= B.em;
    if (adrSel && !adrSel[P.adr[i]]) f |= B.adr;
    if (slSel && !slSel[P.sl[i]]) f |= B.sl;
    if (S.hid ? !P.hidf[i] : P.hidf[i]) f |= B.hid;
    M[i] = f;

    var ok = f === 0;
    if (ok) buf[cnt++] = i;
    if (ok || f === B.kraj) C.kraj[P.kraj[i]]++;
    if (ok || f === B.typ) C.typ[P.typ[i]]++;
    if (ok || f === B.akce) C.akce[P.ak[i]]++;
    if (ok || f === B.src) { var sb = P.src[i]; for (j = 0; j < C.src.length; j++) if (sb & (1 << j)) C.src[j]++; }
    if (ok || f === B.tag) { var tb = P.tag[i]; if (!tb) C.tagNone++; for (j = 0; j < C.tag.length; j++) if (tb & (1 << j)) C.tag[j]++; }
    if (ok || f === B.tel) C.tel[P.tel[i]]++;
    if (ok || f === B.em) C.em[P.em[i]]++;
    if (ok || f === B.adr) C.adr[P.adr[i]]++;
    if (ok || f === B.sl) C.sl[P.sl[i]]++;
    if (ok || f === B.age) { var bi = ageBin(A[i]); if (bi >= 0) { C.age[bi]++; C.ageN++; } }
    if (f === B.hid) C.hid++;
  }
  return { M: M, idx: buf.slice(0, cnt), C: C };
}

/* ---------- řazení ---------- */
var SORTS = {
  sc: { l: "Skóre příležitosti", a: "sc", d: -1 },
  ag: { l: "Stáří", a: "age", d: -1 },
  p: { l: "Cena", a: "price", d: 1 },
  m2: { l: "Kč/m²", a: "m2", d: 1 },
  dv: { l: "Pod férovou cenou", a: "dv", d: -1 },
  dd: { l: "Velikost slevy", a: "dd", d: -1 },
  mot: { l: "Motivace prodávajícího", a: "mot", d: -1 },
  fs: { l: "Nejnovější", a: "fd", d: 1 },
  a: { l: "Plocha", a: "area", d: -1 },
  pct: { l: "Percentil Kč/m²", a: "pct", d: 1 },
  l: { l: "Lokalita (A–Z)", a: null, d: 1, s: true }
};
function sortIdx(P, S, idx) {
  var sk = SORTS[S.sort] || SORTS.sc, dir = S.dir || sk.d, out = Int32Array.from(idx), cmp;
  if (sk.s) {
    var ks = P.lkey;
    cmp = function (a, b) { var x = ks[a], y = ks[b]; return x < y ? -dir : (x > y ? dir : a - b); };
  } else {
    var arr = sk.a === "age" ? ageArr(P, S) : P[sk.a];
    // chybějící hodnoty vždy na konec, ať je směr jakýkoli
    cmp = function (a, b) {
      var x = arr[a], y = arr[b], nx = x !== x, ny = y !== y;
      if (nx || ny) return nx && ny ? a - b : (nx ? 1 : -1);
      return x === y ? a - b : (x < y ? -dir : dir);
    };
  }
  return out.sort(cmp);
}

/* ---------- souhrn výběru ---------- */
function summarize(P, S, idx) {
  var pr = [], m2 = [], ag = [], drop = 0, adr = 0, tel = 0, kup = 0, A = ageArr(P, S);
  for (var k = 0; k < idx.length; k++) {
    var i = idx[k];
    pr.push(P.price[i]); m2.push(P.m2[i]); ag.push(A[i]);
    if (P.dropf[i]) drop++;
    if (P.adr[i] >= 2) adr++;
    if (P.tel[i]) tel++;
    if (P.pz[i]) kup++;
  }
  var n = idx.length;
  return { n: n, medP: median(pr), medM2: median(m2), medAg: median(ag), dropPct: n ? 100 * drop / n : 0, drop: drop, adr: adr, tel: tel, kup: kup };
}

/* ---------- předvolby („pohledy analytika") ---------- */
function resetBut(S, keep) { var d = defState(); Object.keys(d).forEach(function (k) { if (keep.indexOf(k) < 0) S[k] = d[k]; }); return S; }
var PRESETS = [
  { id: "zasekla", label: "Zaseknuté 6m+ s adresou", tip: "Stáří ≥ 180 dní (odhad motoru) a známá adresa aspoň po ulici — kandidáti na papírový dopis majiteli",
    patch: function (S) { S.ageMode = "ag"; S.gMin = 180; S.adr = new Set(["presna", "ulice"]); S.sort = "ag"; S.dir = -1; } },
  { id: "zlevnuji", label: "Zlevňují a stárnou", tip: "Majitel už slevil a inzerát visí 90+ dní — tlak na prodej roste",
    patch: function (S) { S.drop = true; S.ageMode = "ag"; S.gMin = 90; S.sort = "dd"; S.dir = -1; } },
  { id: "kupy", label: "Reálné kupy", tip: "Výrazně pod férovou cenou a bez balastu (model pz)",
    patch: function (S) { S.pz = true; S.sort = "dv"; S.dir = -1; } },
  { id: "dnes", label: "Nové dnes", tip: "První zachycení v den generování dat",
    patch: function (S) { S.nove = 0; S.sort = "sc"; S.dir = -1; } },
  { id: "tyden", label: "Nové za 7 dní", tip: "První zachycení za posledních 7 dní",
    patch: function (S) { S.nove = 7; S.sort = "sc"; S.dir = -1; } },
  { id: "prezentace", label: "Prezentace na nic", tip: "Prezentační skóre ≤ 45 a cena od 800 tis. — drahý objekt s mizerným inzerátem = prodej focení / videa",
    patch: function (S) { S.prMax = 45; S.pMin = 800000; S.sort = "p"; S.dir = -1; } },
  { id: "klienti", label: "Pro klienty", tip: "Sedí do rajonu Dufek / Eva / Staněk / glamping",
    patch: function (S) { S.tag = new Set(Object.keys(TAGS)); S.sort = "sc"; S.dir = -1; } },
  { id: "motiv", label: "Motivovaní prodávající", tip: "Motivace ≥ 60 (analytik) — vyžaduje data analytiku",
    patch: function (S) { S.mot = 60; S.sort = "mot"; S.dir = -1; }, needsX: true }
];
function presetState(p, keepImg) {
  var S = defState(); if (keepImg === false) S.img = false;
  p.patch(S); return S;
}

/* ---------- serializace stavu do URL hash (sdílitelné odkazy) ---------- */
function toHash(S, opt) {
  opt = opt || {};
  var o = [], d = defState();
  function add(k, v) { if (v != null && v !== "") o.push(k + "=" + v); }
  function enc(v) { return encodeURIComponent(v); }
  function list(k, set) { if (set.size) add(k, Array.from(set).map(enc).join(",")); }
  function num(k, v) { if (v != null) add(k, String(v)); }
  if (!opt.noView) { if (S.tab !== "leady") add("t", S.tab); }
  if (S.q) add("q", enc(S.q));
  list("kr", S.kraj); list("ty", S.typ); list("zd", S.src); list("ak", S.akce); list("tg", S.tag); list("ad", S.adr); list("sl", S.sl);
  add("tel", S.tel); add("em", S.em);
  num("pmin", S.pMin); num("pmax", S.pMax); num("mmin", S.m2Min); num("mmax", S.m2Max); num("amin", S.aMin); num("amax", S.aMax);
  num("dv", S.dv); if (S.drop) add("dr", "1"); num("nv", S.nove); if (!S.clean) add("cl", "0"); if (S.rk) add("rk", "1");
  add("pc", S.pc); if (S.pz) add("pz", "1"); num("mot", S.mot); num("prmax", S.prMax);
  if (S.ageMode !== "ag") add("am", S.ageMode); num("s0", S.gMin); num("s1", S.gMax);
  if (S.hid) add("hid", "1");
  if (!opt.noView) {
    if (S.sort !== d.sort || S.dir !== d.dir) { add("so", S.sort); add("sd", S.dir > 0 ? "1" : "-1"); }
    if (!S.img) add("img", "0");
    if (S.tab === "trh" && S.mt !== "m2") add("mt", S.mt);
    if (S.d) add("d", enc(S.d));
  }
  return o.join("&");
}
function parseHash(h) {
  var o = {};
  String(h || "").replace(/^#/, "").split("&").forEach(function (kv) {
    if (!kv) return; var i = kv.indexOf("=");
    o[i < 0 ? kv : kv.slice(0, i)] = i < 0 ? "" : kv.slice(i + 1);
  });
  return o;
}
function dec(v) { try { return decodeURIComponent(v); } catch (e) { return v; } }
function decList(v) { return v ? v.split(",").map(dec).filter(Boolean) : []; }
function fromHash(h) {
  var o = parseHash(h), S = defState();
  function nm(k) { if (o[k] == null) return null; var v = parseFloat(o[k]); return v === v ? v : null; }
  if (o.t === "trh" || o.t === "fav") S.tab = o.t;
  if (o.q) S.q = dec(o.q);
  S.kraj = new Set(decList(o.kr)); S.typ = new Set(decList(o.ty)); S.src = new Set(decList(o.zd));
  S.akce = new Set(decList(o.ak)); S.tag = new Set(decList(o.tg));
  S.adr = new Set(decList(o.ad).filter(function (v) { return Object.prototype.hasOwnProperty.call(ADR_CODE, v); }));
  S.sl = new Set(decList(o.sl).filter(function (v) { return Object.prototype.hasOwnProperty.call(SL_CODE, v); }));
  if (["any", "yes", "web", "no"].indexOf(o.tel) >= 0) S.tel = o.tel;
  if (["yes", "no"].indexOf(o.em) >= 0) S.em = o.em;
  S.pMin = nm("pmin"); S.pMax = nm("pmax"); S.m2Min = nm("mmin"); S.m2Max = nm("mmax"); S.aMin = nm("amin"); S.aMax = nm("amax");
  S.dv = nm("dv"); S.drop = o.dr === "1"; S.nove = nm("nv"); S.clean = o.cl !== "0"; S.rk = o.rk === "1";
  if (o.pc === "hide" || o.pc === "only") S.pc = o.pc;
  S.pz = o.pz === "1"; S.mot = nm("mot"); S.prMax = nm("prmax");
  if (o.am === "ao") S.ageMode = "ao";
  S.gMin = nm("s0"); S.gMax = nm("s1");
  S.hid = o.hid === "1" ? 1 : 0;
  if (o.so && Object.prototype.hasOwnProperty.call(SORTS, o.so)) { S.sort = o.so; S.dir = o.sd === "1" ? 1 : -1; }
  if (o.img === "0") S.img = false;
  if (o.mt) S.mt = o.mt;
  if (o.d) S.d = dec(o.d);
  return S;
}

/* ---------- export CSV (jen příznaky kontaktů, žádné hodnoty — ty nemáme a nebudeme mít) ---------- */
function csvEsc(v) {
  if (v == null) return "";
  if (typeof v === "number") return String(Math.round(v * 100) / 100).replace(".", ",");
  var s = String(v);
  if (/^[=+\-@\t\r]/.test(s)) s = "'" + s;        // ochrana proti vzorcům v Excelu (titulky jsou z cizích webů)
  return /[";\n\r]/.test(s) ? '"' + s.replace(/"/g, '""') + '"' : s;
}
var CSV_HEAD = ["id", "zdroje", "kraj", "lokalita", "typ", "titulek", "cena_kc", "puvodni_cena_kc", "sleva_pct", "plocha_m2", "kc_m2",
  "ferova_cena_kc", "pod_ferovou_pct", "stari_dny", "stari_jistota", "vznik_odhad", "naposledy_obnoveno", "sledujeme_dni", "prvni_videno",
  "telefon", "email", "adresa", "prodejce", "akce", "tip", "tagy", "vlajky", "url", "dalsi_url"];
function toCSV(P, idx) {
  var rows = [CSV_HEAD.join(";")];
  for (var k = 0; k < idx.length; k++) {
    var l = P.L[idx[k]];
    rows.push([l.i, (l.s || []).join("+"), l.k, l.l, TYP[l.c] || l.c, redact(l.t), l.p, l.p0, l.dd, l.a, l.m2, l.f, l.dv, l.ag, l.aj, l.an, l.ab, l.ao, l.fs,
      l.tel === true ? "ano" : (l.tel === "w" ? "jen na webu" : ""), l.em ? "ano" : "", l.adr || "", l.sl || "", l.ak, l.tp,
      (l.tg || []).join("|"), (l.fl || []).join("|"), l.u, (l.us || []).join(" ")].map(csvEsc).join(";"));
  }
  return rows.join("\r\n");
}

/* ---------- matice trhu kraj × typ ---------- */
var TRH_ALIAS = {
  n: ["n", "count", "pocet"], m2: ["m2", "med_m2", "median_m2", "kc_m2"], ag: ["ag", "med_age", "median_age", "stari", "med_stari"],
  drop: ["drop", "zlevneno_pct", "pct_drop"], nove7: ["nove7", "new7"], pz: ["pz", "kupy", "deals"],
  odch30: ["odchod30"], zas: ["zasoba_mesice"], dmed: ["drop_med"]
};
function normTrh(e) {
  var o = {};
  Object.keys(TRH_ALIAS).forEach(function (k) {
    for (var j = 0; j < TRH_ALIAS[k].length; j++) { var v = e[TRH_ALIAS[k][j]]; if (typeof v === "number") { o[k] = v; break; } }
  });
  return o;
}
function trhMatrix(P) {
  var cells = {};
  function bk(k) { return cells[k] || (cells[k] = { n: 0, m2: [], ag: [], drop: 0, nove7: 0, pz: 0, adr: 0, st: 0 }); }
  for (var i = 0; i < P.n; i++) {
    if (P.flag[i]) continue;             // stejně jako builder: tržní přehled jen z čistých inzerátů
    var l = P.L[i], k = l.k || "?", c = l.c || "?";
    [k + "|" + c, k + "|*", "*|" + c, "*|*"].forEach(function (key) {
      var b = bk(key); b.n++;
      if (P.m2[i] === P.m2[i]) b.m2.push(P.m2[i]);
      b.ag.push(P.agm[i] === P.agm[i] ? P.agm[i] : 0);
      if (P.dropf[i]) b.drop++;
      if (P.fd[i] <= 7) b.nove7++;
      if (P.pz[i]) b.pz++;
      if (P.adr[i] >= 2) b.adr++;
      if (P.agm[i] >= 180) b.st++;
    });
  }
  var out = {};
  Object.keys(cells).forEach(function (key) {
    var b = cells[key]; if (b.n < 5) return;
    out[key] = { n: b.n, m2: b.m2.length >= 5 ? Math.round(median(b.m2)) : null, ag: Math.round(median(b.ag)),
      drop: Math.round(1000 * b.drop / b.n) / 10, nove7: b.nove7, pz: b.pz, adr: b.adr, st: b.st };
  });
  // oficiální čísla (analytik / builder) mají přednost před přepočtem v prohlížeči
  var off = P.trh || {};
  Object.keys(off).forEach(function (key) {
    if (!out[key] || !off[key] || typeof off[key] !== "object") return;
    var nrm = normTrh(off[key]); Object.keys(nrm).forEach(function (f) { out[key][f] = nrm[f]; });
  });
  return out;
}
var METRICS = [
  { k: "m2", l: "Medián Kč/m²", f: function (v) { return fmt(v); }, hue: "--accent", tip: "Medián ceny za m² (jen čisté inzeráty s plochou)" },
  { k: "ag", l: "Medián stáří", f: function (v) { return fmt(v) + " d"; }, hue: "--gold", tip: "Medián skutečného stáří inzerátu ve dnech" },
  { k: "drop", l: "% zlevněných", f: function (v) { return fmt1(v) + " %"; }, hue: "--drop", tip: "Podíl inzerátů, kde majitel už snížil cenu" },
  { k: "nove7", l: "Nové za 7 dní", f: function (v) { return fmt(v); }, hue: "--info", tip: "První zachycení za posledních 7 dní" },
  { k: "pz", l: "Reálné kupy", f: function (v) { return fmt(v); }, hue: "--accent", tip: "Inzeráty výrazně pod férovou cenou (model)" },
  { k: "st", l: "Zaseknuté 180+ d", f: function (v) { return fmt(v); }, hue: "--gold", tip: "Počet inzerátů staršího než 180 dní" },
  { k: "adr", l: "S adresou", f: function (v) { return fmt(v); }, hue: "--accent", tip: "Počet inzerátů se známou adresou aspoň po ulici (cíl papírového dopisu)" },
  { k: "n", l: "Počet inzerátů", f: function (v) { return fmt(v); }, hue: "--info", tip: "Počet čistých inzerátů" },
  { k: "dmed", l: "Medián slevy", f: function (v) { return fmt1(v) + " %"; }, hue: "--drop", tip: "Medián velikosti slevy u inzerátů, které zlevnily" },
  { k: "odch30", l: "Odešlo za 30 dní", f: function (v) { return fmt(v); }, hue: "--info", tip: "Kolik inzerátů zmizelo za 30 dní. Odchod není prodej — bazoš maže po ~60 dnech a majitel mohl i vzdát." },
  { k: "zas", l: "Zásoba (měsíce)", f: function (v) { return fmt1(v) + " m"; }, hue: "--gold", tip: "Živé inzeráty / odchody za 30 dní — orientačně, za kolik měsíců by se nabídka vyčerpala" }
];

var HLIDAC_CORE = {
  SHARDS: SHARDS, PAGE: PAGE, B: B, AGE_STOPS: AGE_STOPS, SORTS: SORTS, PRESETS: PRESETS, METRICS: METRICS,
  defState: defState, prep: prep, filterPass: filterPass, sortIdx: sortIdx, summarize: summarize, presetState: presetState,
  toHash: toHash, fromHash: fromHash, toCSV: toCSV, csvEsc: csvEsc, trhMatrix: trhMatrix, shardOf: shardOf, shardFile: shardFile,
  parseNum: parseNum, median: median, fold: fold, esc: esc, redact: redact, ageBin: ageBin, safeUrl: safeUrl, fmt: fmt, fmtM: fmtM
};
globalThis.HLIDAC_CORE = HLIDAC_CORE;

/* ================================================================================================
   B) UI — jen v prohlížeči
   ================================================================================================ */
var Dt = null, P = null, S = defState(), R = null, SORTED = new Int32Array(0);
var FAVS = new Set(), HIDS = new Set(), UIP = { open: {}, dense: false };
var page = 0, cur = -1, detailN = -1, lastFocus = null, presetCounts = {}, CHIPS = [], FE = null, TRH = null, SHARD = {};
var tmr = {}, hashLast = null, suppressHash = false;

function $(id) { return document.getElementById(id); }
function lsGet(k, def) { try { var v = localStorage.getItem(k); return v == null ? def : JSON.parse(v); } catch (e) { return def; } }
function lsSet(k, v) { try { localStorage.setItem(k, JSON.stringify(v)); } catch (e) { /* soukromý režim — bez uložení */ } }
function debounce(key, fn, ms) { clearTimeout(tmr[key]); tmr[key] = setTimeout(fn, ms); }

/* ---------- ikony ---------- */
var SVGA = 'viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"';
var ICON = {
  tel: '<svg ' + SVGA + '><path d="M5 4h4l2 5-2.5 1.5a11 11 0 0 0 5 5L15 13l5 2v4a2 2 0 0 1-2 2A16 16 0 0 1 3 6a2 2 0 0 1 2-2z"/></svg>',
  em: '<svg ' + SVGA + '><rect x="3" y="5" width="18" height="14" rx="2"/><path d="M3 7l9 6 9-6"/></svg>',
  adr: '<svg ' + SVGA + '><path d="M3 11l9-8 9 8"/><path d="M5 10v10h14V10"/><path d="M10 20v-6h4v6"/></svg>'
};
var JD = {
  v: '<svg class="jd" viewBox="0 0 12 12" aria-hidden="true"><circle cx="6" cy="6" r="5" fill="currentColor"/></svg>',
  s: '<svg class="jd" viewBox="0 0 12 12" aria-hidden="true"><circle cx="6" cy="6" r="4.5" fill="none" stroke="currentColor" stroke-width="1.5"/><path d="M6 1.5a4.5 4.5 0 0 0 0 9z" fill="currentColor"/></svg>',
  n: '<svg class="jd" viewBox="0 0 12 12" aria-hidden="true"><circle cx="6" cy="6" r="4.5" fill="none" stroke="currentColor" stroke-width="1.5"/></svg>'
};
var JTXT = { v: "vysoká", s: "střední", n: "nízká" };
function jdot(aj) { aj = JTXT[aj] ? aj : "n"; return '<span class="j' + aj + '" title="Jistota stáří: ' + JTXT[aj] + '">' + JD[aj] + '</span>'; }

/* ---------- drobné HTML pomůcky ---------- */
function akBadge(k) { var a = AKCE[k] || AKCE.sledovat; return '<span class="ak ak-' + a[1] + '">' + a[0] + '</span>'; }
function krajLabel(k) { return k === "?" ? "neurčeno" : k; }
function pill(cls, txt, title) { return '<span class="pill ' + cls + '"' + (title ? ' title="' + esc(title) + '"' : "") + '>' + esc(txt) + '</span>'; }
function badges(l) {
  var h = "";
  if (l.pz) h += pill("pl-kup", "REÁLNÝ KUP", "Výrazně pod férovou cenou, bez balastu");
  if (l.pc) h += pill("pl-sus", "LEVNÉ?", "Podezřele levné — skoro jistě háček, prověřit");
  (l.fl || []).forEach(function (f) { h += pill("pl-flag", FLAG[f] || f.toUpperCase()); });
  (l.tg || []).forEach(function (t) { h += pill("pl-tag", TAGS[t] || t, "Vhodné pro: " + (TAGS[t] || t)); });
  if (l.rk) h += pill("pl-rk", "RK NEVOLAT", "Majitel píše, že si nepřeje oslovení od realitek");
  if (l.sl === "m") h += pill("pl-mak", "MAKLÉŘ?", "Detail inzerátu říká, že prodává makléř / RK — ověř před oslovením");
  return h;
}
function ageTitle(l) {
  var t = [];
  if (l.ag != null) t.push("Skutečné stáří (odhad motoru): " + l.ag + " dní · jistota " + (JTXT[l.aj] || "nízká"));
  if (l.an) t.push("Vznikl (odhad): " + fmtDate(l.an));
  if (l.ab) t.push("Naposledy obnoveno (to vidí majitel na portálu): " + fmtDate(l.ab));
  if (l.ao != null) t.push("Sledujeme: " + l.ao + " dní" + (l.fs ? " (poprvé viděno " + fmtDate(l.fs) + ")" : ""));
  return t.join("\n");
}
function ctTitle(what, l, val) {
  return what + " — " + val + (l.kz === "text" ? " (odhad z textu inzerátu; z detailu zatím neověřeno)" : " (ověřeno z detailu)");
}
function ctIcons(l) {
  var tel = l.tel === true ? ["", "ano — číslo je v inzerátu"] : (l.tel === "w" ? ["web", "jen za tlačítkem na webu (neodkrýváme)"] : ["off", "nenalezen"]);
  var em = l.em ? ["", "ano"] : ["off", "nenalezen"];
  var ad = l.adr === "presna" ? ["pres", "přesná"] : (l.adr === "ulice" ? ["", "aspoň ulice"] : (l.adr === "obec" ? ["part", "jen obec"] : ["off", "nenalezena"]));
  function ic(cls, svg, what, val) {
    return '<span class="ci ' + cls + '" title="' + esc(what + ": " + val) + '">' + svg + '<span class="sr">' + esc(what + ": " + val) + '</span></span>';
  }
  return ic(tel[0], ICON.tel, "Telefon", tel[1]) + ic(em[0], ICON.em, "E-mail", em[1]) + ic(ad[0], ICON.adr, "Adresa", ad[1]);
}

/* ---------- oblíbené / skryté (kompatibilní klíče hlidac_fav a hlidac_hidden = URL inzerátu) ---------- */
function loadUserSets() {
  var f = lsGet("hlidac_fav", []), h = lsGet("hlidac_hidden", []);
  FAVS = new Set(Array.isArray(f) ? f.filter(function (u) { return typeof u === "string"; }) : []);
  HIDS = new Set(Array.isArray(h) ? h.filter(function (u) { return typeof u === "string"; }) : []);
  syncUserFlags();
}
function syncUserFlags() {
  P.favf.fill(0); P.hidf.fill(0);
  FAVS.forEach(function (u) { var n = P.urlMap.get(u); if (n != null) P.favf[n] = 1; });
  HIDS.forEach(function (u) { var n = P.urlMap.get(u); if (n != null) P.hidf[n] = 1; });
}
function saveUserSets() { lsSet("hlidac_fav", Array.from(FAVS)); lsSet("hlidac_hidden", Array.from(HIDS)); }
function allUrls(n) { var l = P.L[n]; return [l.u].concat(l.us || []); }
function toggleFav(n) {
  if (P.favf[n]) { allUrls(n).forEach(function (u) { FAVS.delete(u); }); P.favf[n] = 0; }
  else { FAVS.add(P.L[n].u); P.favf[n] = 1; }
  saveUserSets();
}
function toggleHide(n) {
  var was = P.hidf[n];
  if (was) { allUrls(n).forEach(function (u) { HIDS.delete(u); }); P.hidf[n] = 0; }
  else { HIDS.add(P.L[n].u); P.hidf[n] = 1; }
  saveUserSets();
  return !was;
}
function favCount() { var c = 0; for (var i = 0; i < P.n; i++) c += P.favf[i]; return c; }

/* ---------- výpočet výsledku ---------- */
function recompute() {
  if (S.tab === "fav") {
    var f = []; for (var i = 0; i < P.n; i++) if (P.favf[i]) f.push(i);
    R = null; SORTED = sortIdx(P, S, Int32Array.from(f));
  } else {
    R = filterPass(P, S);
    SORTED = sortIdx(P, S, R.idx);
  }
}
function computePresetCounts() {
  PRESETS.forEach(function (p) { presetCounts[p.id] = filterPass(P, presetState(p)).idx.length; });
}
function activePresetId() {
  var key = toHash(S, { noView: true });
  for (var j = 0; j < PRESETS.length; j++) if (toHash(presetState(PRESETS[j]), { noView: true }) === key) return PRESETS[j].id;
  return null;
}

/* ---------- hlavní vykreslení ---------- */
function refresh(what) {
  if (S.tab === "trh") { renderTrh(); updateTabs(); syncHash(); return; }
  if (what !== "list") { recompute(); }
  var pages = Math.max(1, Math.ceil(SORTED.length / PAGE)); if (page >= pages) page = pages - 1;
  renderPresets(); syncFacets(); renderChips(); renderSummary(); renderList(); renderPager(); updateTabs(); syncHash();
}
function onFilterChange() { page = 0; cur = -1; refresh(); }

function updateTabs() {
  var tabs = document.querySelectorAll(".tabs [role=tab]");
  for (var i = 0; i < tabs.length; i++) tabs[i].setAttribute("aria-selected", tabs[i].dataset.tab === S.tab ? "true" : "false");
  $("tcnt-leady").textContent = (S.tab === "leady" && R) ? fmt(R.idx.length) : "";
  var fc = favCount(); $("tcnt-fav").textContent = fc ? String(fc) : "";
  var hc = HIDS.size; $("btn-hid").textContent = "Skryté: " + hc; $("btn-hid").setAttribute("aria-pressed", S.hid ? "true" : "false");
  $("btn-img").setAttribute("aria-pressed", S.img ? "true" : "false");
}
function setTab(t) {
  S.tab = t; page = 0; cur = -1;
  $("pane-list").hidden = t === "trh"; $("pane-trh").hidden = t !== "trh";
  var fav = t === "fav";
  $("pane-list").classList.toggle("favmode", fav);
  $("side").hidden = fav; $("presets").hidden = fav; $("btn-filters").hidden = fav;
  closeSheet();
  refresh();
  window.scrollTo(0, 0);
}

/* ---------- postranní panel: fasety ---------- */
function sec(id, title, body) {
  var open = UIP.open[id] != null ? UIP.open[id] : (["q", "age", "kontakt", "typ", "kraj", "cena"].indexOf(id) >= 0);
  return '<details class="fsec" data-sec="' + id + '"' + (open ? " open" : "") + '><summary>' + title + '<span class="sbadge" data-sb="' + id + '"></span></summary><div class="fbody">' + body + '</div></details>';
}
function checkList(f, items, labelFn, cls) {
  return items.map(function (v) {
    return '<label class="fv ' + (cls || "") + '" data-fv="' + f + ':' + esc(v) + '"><input type="checkbox" data-f="' + f + '" data-v="' + esc(v) + '"><span class="fn">' + esc(labelFn(v)) + '</span><span class="fc" data-c="' + f + ':' + esc(v) + '"></span></label>';
  }).join("");
}
function chipRow(act, items) {
  return '<div class="chips">' + items.map(function (it) {
    return '<button type="button" class="cb" data-act="' + act + '" data-v="' + esc(it[0]) + '" aria-pressed="false">' + esc(it[1]) + '<span class="cn" data-cn="' + act + ':' + esc(it[0]) + '"></span></button>';
  }).join("") + '</div>';
}
function numPair(a, b, ph1, ph2, label) {
  return '<span class="flab">' + label + '</span><div class="row2"><input class="fin" type="text" inputmode="decimal" data-k="' + a + '" placeholder="' + ph1 + '" aria-label="' + label + ' od"><input class="fin" type="text" inputmode="decimal" data-k="' + b + '" placeholder="' + ph2 + '" aria-label="' + label + ' do"></div>';
}
function toggleRow(k, label, extra) {
  return '<label class="tg"><input type="checkbox" data-t="' + k + '"><span>' + label + '</span><span class="fc" data-tc="' + k + '"></span></label>' + (extra || "");
}
function buildFacets() {
  var N = AGE_STOPS.length;
  var age = '<div class="seg" role="group" aria-label="Které stáří filtrovat"><button type="button" data-act="agemode" data-v="ag" aria-pressed="true" title="Odhad motoru z ID inzerátu, přeinzerování a historie ceny">Skutečné stáří (motor)</button>' +
    '<button type="button" data-act="agemode" data-v="ao" aria-pressed="false" title="Kolik dní inzerát sledujeme my (od prvního zachycení)">Jak dlouho sledujeme</button></div>' +
    '<div class="chips" id="agequick">' + [30, 60, 90, 180, 365].map(function (d) { return '<button type="button" class="cb" data-act="agequick" data-v="' + d + '" aria-pressed="false">' + d + '+</button>'; }).join("") + '</div>' +
    '<div class="row2" style="margin-top:8px"><input class="fin" type="text" inputmode="numeric" data-k="gMin" placeholder="od (dní)" aria-label="Stáří od, dní"><input class="fin" type="text" inputmode="numeric" data-k="gMax" placeholder="do (dní)" aria-label="Stáří do, dní"></div>' +
    '<svg id="hist" class="hist" viewBox="0 0 260 46" preserveAspectRatio="none" role="img" aria-label="Rozložení stáří ve výběru"></svg>' +
    '<div class="hax"><span>0</span><span>30</span><span>90</span><span>180</span><span>365</span><span>730</span><span>1100+</span></div>' +
    '<div class="dual"><div class="rail"><i id="dualfill"></i></div><input type="range" id="sl-lo" min="0" max="' + N + '" step="1" value="0" aria-label="Stáří od (posuvník)"><input type="range" id="sl-hi" min="0" max="' + N + '" step="1" value="' + N + '" aria-label="Stáří do (posuvník)"></div>' +
    '<p class="note">Rozložení stáří u inzerátů, které prošly ostatními filtry (výška = odmocnina počtu, ať je vidět i ocas starých). Klik na sloupec = filtr na ten rozsah.</p>';
  var kontakt =
    '<span class="flab">Telefon</span>' + chipRow("tel", [["", "Vše"], ["any", "Má (vč. na webu)"], ["yes", "Přímo v inzerátu"], ["web", "Jen na webu"], ["no", "Bez"]]) +
    '<span class="flab">E-mail</span>' + chipRow("em", [["", "Vše"], ["yes", "Má e-mail"], ["no", "Bez"]]) +
    '<span class="flab">Adresa</span>' + checkList("adr", ADR_LIST, function (v) { return ADR[v]; }) +
    '<span class="flab">Prodejce</span>' + checkList("sl", SL_LIST, function (v) { return SL_LABEL[v]; }, "") +
    '<p class="note box">Hodnoty kontaktů nemáme a nezveřejňujeme, jen příznaky (☎ ✉ ⌂). Majitele lze oslovit jen <b>papírovým dopisem</b> — e-maily zakazuje zákon č. 480/2004 Sb. — proto je nejcennější <b>adresa</b>.</p>' +
    '<p class="note" id="ctnote"></p>';
  var cena = numPair("pMin", "pMax", "od, např. 2m", "do, např. 5m", "Cena (Kč)") + numPair("m2Min", "m2Max", "od", "do", "Kč/m²") + numPair("aMin", "aMax", "od", "do", "Plocha (m²)");
  var fer = '<span class="flab">Pod férovou cenou alespoň (%)</span><div class="row2"><input class="fin" type="text" inputmode="decimal" data-k="dv" placeholder="např. 25" aria-label="Pod férovou cenou alespoň, procent"><div class="chips">' +
    [10, 25, 40].map(function (d) { return '<button type="button" class="cb" data-act="dvquick" data-v="' + d + '" aria-pressed="false">' + d + '+</button>'; }).join("") + '</div></div>' +
    toggleRow("drop", "Jen zlevněné") + toggleRow("pz", "Jen reálné kupy (model)");
  var cas = '<span class="flab">Nové (první zachycení)</span><select class="fin" data-k="nove" aria-label="Nové inzeráty"><option value="">Vše</option><option value="0">Jen dnes</option><option value="7">Za 7 dní</option><option value="30">Za 30 dní</option></select>';
  var anal = '<span class="flab">Motivace prodávajícího alespoň (0–100)</span><input class="fin" type="text" inputmode="numeric" data-k="mot" placeholder="např. 60" aria-label="Motivace alespoň">' +
    '<span class="flab">Prezentace nejvýš (0–100)</span><input class="fin" type="text" inputmode="numeric" data-k="prMax" placeholder="např. 45" aria-label="Prezentační skóre nejvýš">' +
    '<p class="note" id="xnote"></p>';
  var cist = toggleRow("clean", "Skrýt balast (podíly, mobilheimy, dražby…)") + toggleRow("rk", "Skrýt „RK nevolat“") +
    '<span class="flab">Podezřele levné</span><select class="fin" data-k="pc" aria-label="Podezřele levné"><option value="">Zobrazit vše</option><option value="hide">Skrýt</option><option value="only">Jen podezřele levné</option></select>';
  $("facets").innerHTML =
    sec("q", "Hledat", '<input id="f-q" class="fin" type="search" placeholder="Lokalita, titulek…  ( / )" autocomplete="off" aria-label="Fulltext v titulku a lokalitě">') +
    sec("age", "Stáří inzerátu", age) + sec("kontakt", "Kontakty a adresa", kontakt) +
    sec("typ", "Typ", checkList("typ", P.typList, function (v) { return TYP[v] || v; })) +
    sec("kraj", "Kraj", '<div class="scroll">' + checkList("kraj", P.krajList, krajLabel) + '</div>') +
    sec("cena", "Cena a plocha", cena) + sec("fer", "Férová cena a slevy", fer) + sec("cas", "Novost", cas) +
    sec("src", "Zdroj", checkList("src", P.srcList, function (v) { return SRC[v] || v; })) +
    sec("akce", "Co s tím (akce)", checkList("akce", P.akList, function (v) { return (AKCE[v] || [v])[0]; })) +
    sec("tag", "Pro klienty", checkList("tag", P.tagList, function (v) { return TAGS[v] || v; })) +
    sec("anal", "Analytika", anal) + sec("cist", "Čištění", cist);
  // reference na prvky pro rychlou synchronizaci (bez přestavby DOMu — nezruší focus)
  FE = { cnt: {}, chk: {}, fv: {}, cn: {}, inp: {}, tg: {}, tc: {}, sb: {} };
  var q;
  q = $("facets").querySelectorAll("[data-c]"); for (var i = 0; i < q.length; i++) FE.cnt[q[i].dataset.c] = q[i];
  q = $("facets").querySelectorAll("input[data-f]"); for (i = 0; i < q.length; i++) { FE.chk[q[i].dataset.f + ":" + q[i].dataset.v] = q[i]; FE.fv[q[i].dataset.f + ":" + q[i].dataset.v] = q[i].parentNode; }
  q = $("facets").querySelectorAll("[data-cn]"); for (i = 0; i < q.length; i++) FE.cn[q[i].dataset.cn] = q[i];
  q = $("facets").querySelectorAll("[data-k]"); for (i = 0; i < q.length; i++) FE.inp[q[i].dataset.k] = q[i];
  q = $("facets").querySelectorAll("input[data-t]"); for (i = 0; i < q.length; i++) FE.tg[q[i].dataset.t] = q[i];
  q = $("facets").querySelectorAll("[data-tc]"); for (i = 0; i < q.length; i++) FE.tc[q[i].dataset.tc] = q[i];
  q = $("facets").querySelectorAll("[data-sb]"); for (i = 0; i < q.length; i++) FE.sb[q[i].dataset.sb] = q[i];
}
function setCnt(key, v) { var e = FE.cnt[key]; if (e) e.textContent = v == null ? "" : fmt(v); var fv = FE.fv[key]; if (fv) fv.classList.toggle("zero", !v); }
function setVal(k, v) { var e = FE.inp[k]; if (e && document.activeElement !== e) e.value = v == null ? "" : String(v); }

function binInRange(k) {
  var lo = S.gMin == null ? -Infinity : S.gMin, hi = S.gMax == null ? Infinity : S.gMax;
  var bl = AGE_STOPS[k], bh = k < AGE_STOPS.length - 1 ? AGE_STOPS[k + 1] - 1 : Infinity;
  return bh >= lo && bl <= hi;
}
function binLabel(k) {
  var bl = AGE_STOPS[k];
  return k < AGE_STOPS.length - 1 ? bl + "–" + (AGE_STOPS[k + 1] - 1) + " d" : bl + "+ d";
}
function lowPos(g) { if (g == null) return 0; var p = 0; for (var i = 0; i < AGE_STOPS.length; i++) if (AGE_STOPS[i] <= g) p = i; return p; }
function highPos(g) { if (g == null) return AGE_STOPS.length; for (var i = 0; i < AGE_STOPS.length; i++) if (AGE_STOPS[i] >= g) return i; return AGE_STOPS.length; }

function renderHist() {
  var C = R ? R.C.age : new Int32Array(AGE_STOPS.length), N = AGE_STOPS.length, w = 260, h = 44, bw = w / N, mx = 1, k;
  for (k = 0; k < N; k++) if (C[k] > mx) mx = C[k];
  var s = "";
  for (k = 0; k < N; k++) {
    var hh = C[k] ? Math.max(2, Math.round(Math.sqrt(C[k] / mx) * (h - 2))) : 0, on = binInRange(k);   // odmocnina: dlouhý ocas starých inzerátů musí být vidět
    s += '<g data-bin="' + k + '"><title>' + binLabel(k) + ": " + fmt(C[k]) + '</title>' +
      '<rect class="hit" x="' + (k * bw) + '" y="0" width="' + bw + '" height="' + h + '"/>' +
      '<rect class="hb' + (on ? " on" : "") + '" x="' + (k * bw + 1) + '" y="' + (h - hh) + '" width="' + (bw - 2) + '" height="' + hh + '" pointer-events="none"/></g>';
  }
  $("hist").innerHTML = s;
  var lo = $("sl-lo"), hi = $("sl-hi"), lp = lowPos(S.gMin), hp = highPos(S.gMax);
  if (document.activeElement !== lo) lo.value = lp;
  if (document.activeElement !== hi) hi.value = hp;
  lo.style.zIndex = lp >= N - 1 ? 3 : 1; hi.style.zIndex = 2;
  var span = N, f = $("dualfill"); f.style.left = (lp / span * 100) + "%"; f.style.right = (100 - hp / span * 100) + "%";
}

function syncFacets() {
  if (!FE || !R) return;
  var C = R.C, i;
  // zaškrtávací seznamy
  [["kraj", P.krajList, S.kraj, function (j) { return C.kraj[j]; }], ["typ", P.typList, S.typ, function (j) { return C.typ[j]; }],
   ["src", P.srcList, S.src, function (j) { return C.src[j]; }], ["akce", P.akList, S.akce, function (j) { return C.akce[j]; }],
   ["tag", P.tagList, S.tag, function (j) { return C.tag[j]; }],
   ["adr", ADR_LIST, S.adr, function (j) { return C.adr[ADR_CODE[ADR_LIST[j]]]; }],
   ["sl", SL_LIST, S.sl, function (j) { return C.sl[SL_CODE[SL_LIST[j]]]; }]
  ].forEach(function (d) {
    d[1].forEach(function (v, j) {
      var key = d[0] + ":" + v, chk = FE.chk[key];
      if (chk) chk.checked = d[2].has(v);
      setCnt(key, d[3](j));
    });
  });
  var se = FE.fv["sl:m"]; if (se) se.classList.add("warn");
  // chipy telefonu / e-mailu
  var tc = { "": C.tel[0] + C.tel[1] + C.tel[2], any: C.tel[1] + C.tel[2], yes: C.tel[1], web: C.tel[2], no: C.tel[0] };
  var ec = { "": C.em[0] + C.em[1], yes: C.em[1], no: C.em[0] };
  Object.keys(tc).forEach(function (v) { var e = FE.cn["tel:" + v]; if (e) e.textContent = fmt(tc[v]); });
  Object.keys(ec).forEach(function (v) { var e = FE.cn["em:" + v]; if (e) e.textContent = fmt(ec[v]); });
  document.querySelectorAll('[data-act="tel"]').forEach(function (b) { b.setAttribute("aria-pressed", b.dataset.v === S.tel ? "true" : "false"); });
  document.querySelectorAll('[data-act="em"]').forEach(function (b) { b.setAttribute("aria-pressed", b.dataset.v === S.em ? "true" : "false"); });
  document.querySelectorAll('[data-act="agemode"]').forEach(function (b) { b.setAttribute("aria-pressed", b.dataset.v === S.ageMode ? "true" : "false"); });
  document.querySelectorAll('[data-act="agequick"]').forEach(function (b) { b.setAttribute("aria-pressed", (S.gMin === +b.dataset.v && S.gMax == null) ? "true" : "false"); });
  document.querySelectorAll('[data-act="dvquick"]').forEach(function (b) { b.setAttribute("aria-pressed", S.dv === +b.dataset.v ? "true" : "false"); });
  // číselné vstupy (nepřepisovat, když v nich uživatel píše)
  ["pMin", "pMax", "m2Min", "m2Max", "aMin", "aMax", "dv", "mot", "prMax", "gMin", "gMax"].forEach(function (k) { setVal(k, S[k]); });
  var q = $("f-q"); if (document.activeElement !== q) q.value = S.q;
  if (FE.inp.nove) FE.inp.nove.value = S.nove == null ? "" : String(S.nove);
  if (FE.inp.pc) FE.inp.pc.value = S.pc;
  ["drop", "pz", "clean", "rk"].forEach(function (k) { if (FE.tg[k]) FE.tg[k].checked = !!S[k]; });
  var noX = !P.hasX;
  FE.inp.mot.disabled = noX; FE.inp.mot.placeholder = noX ? "čeká na analytiku" : "např. 60";
  $("xnote").textContent = noX ? "Motivace a srovnatelné inzeráty zatím nejsou ve datech — filtr se zapne, až je analytik dodá." : "";
  var ov = P.meta.kontakty_overeno || 0;
  $("ctnote").textContent = "Příznaky jsou " + (ov ? "u " + fmt(ov) + " inzerátů ověřené z detailu, u ostatních" : "zatím") + " odhad z textu inzerátu — „bez telefonu“ proto neznamená, že ho prodejce nemá.";
  renderHist();
  // odznaky počtu aktivních filtrů u sekcí
  var sb = {
    q: S.q ? 1 : 0, age: (S.gMin != null || S.gMax != null) ? 1 : 0, kontakt: (S.tel ? 1 : 0) + (S.em ? 1 : 0) + S.adr.size + S.sl.size,
    typ: S.typ.size, kraj: S.kraj.size, cena: [S.pMin, S.pMax, S.m2Min, S.m2Max, S.aMin, S.aMax].filter(function (v) { return v != null; }).length,
    fer: (S.dv != null ? 1 : 0) + (S.drop ? 1 : 0) + (S.pz ? 1 : 0), cas: S.nove != null ? 1 : 0, src: S.src.size, akce: S.akce.size, tag: S.tag.size,
    anal: (S.mot != null ? 1 : 0) + (S.prMax != null ? 1 : 0), cist: (!S.clean ? 1 : 0) + (S.rk ? 1 : 0) + (S.pc ? 1 : 0)
  };
  Object.keys(sb).forEach(function (k) { if (FE.sb[k]) FE.sb[k].textContent = sb[k] ? String(sb[k]) : ""; });
  var fb = Object.keys(sb).reduce(function (a, k) { return a + (sb[k] || 0); }, 0);
  $("fbadge").textContent = fb ? String(fb) : "";
  $("side-apply").textContent = "Zobrazit " + fmt(R.idx.length) + " inzerátů";
}

/* ---------- předvolby ---------- */
function renderPresets() {
  var act = activePresetId(), fp = document.activeElement && document.activeElement.dataset ? document.activeElement.dataset.preset : null;
  $("presets").innerHTML = PRESETS.map(function (p) {
    var dis = p.needsX && !P.hasX, cnt = presetCounts[p.id];
    return '<button type="button" class="pre" data-preset="' + p.id + '" aria-pressed="' + (act === p.id ? "true" : "false") + '"' + (dis ? " disabled" : "") +
      ' title="' + esc(p.tip + (dis ? " (zatím bez dat)" : "")) + '">' + esc(p.label) + (cnt != null ? '<span class="pn">' + fmt(cnt) + '</span>' : "") + '</button>';
  }).join("");
  // innerHTML zahodil prvek s focusem → vrátit ho (klávesová obsluha předvoleb)
  if (fp) { var b = $("presets").querySelector('[data-preset="' + fp + '"]'); if (b && !b.disabled) b.focus({ preventScroll: true }); }
}
function applyPreset(id) {
  var p = PRESETS.filter(function (x) { return x.id === id; })[0]; if (!p) return;
  var keepImg = S.img;
  if (activePresetId() === id) S = defState(); else S = presetState(p);
  S.img = keepImg; S.tab = "leady";
  onFilterChange();
}

/* ---------- aktivní filtry jako odklikávací štítky ---------- */
function renderChips() {
  CHIPS = [];
  if (S.tab === "fav") { $("achips").innerHTML = ""; return; }    // v Oblíbených se filtry neuplatňují
  function add(label, rm) { CHIPS.push({ label: label, rm: rm }); }
  function setChips(prefix, set, lab) { set.forEach(function (v) { add(prefix + lab(v), function () { set.delete(v); }); }); }
  var d = defState();
  if (S.q) add("Hledání: „" + S.q + "“", function () { S.q = ""; });
  setChips("Kraj: ", S.kraj, krajLabel); setChips("Typ: ", S.typ, function (v) { return TYP[v] || v; });
  setChips("Zdroj: ", S.src, function (v) { return SRC[v] || v; }); setChips("Akce: ", S.akce, function (v) { return (AKCE[v] || [v])[0]; });
  setChips("Pro: ", S.tag, function (v) { return TAGS[v] || v; });
  setChips("Adresa: ", S.adr, function (v) { return ADR[v]; }); setChips("Prodejce: ", S.sl, function (v) { return SL_LABEL[v]; });
  if (S.tel) add("Telefon: " + ({ any: "má", yes: "přímo v inzerátu", web: "jen na webu", no: "bez" })[S.tel], function () { S.tel = ""; });
  if (S.em) add("E-mail: " + (S.em === "yes" ? "má" : "bez"), function () { S.em = ""; });
  if (S.gMin != null || S.gMax != null) {
    var an = (S.ageMode === "ao" ? "Sledujeme " : "Stáří ") + (S.gMin != null && S.gMax != null ? S.gMin + "–" + S.gMax : (S.gMin != null ? "≥ " + S.gMin : "≤ " + S.gMax)) + " d";
    add(an, function () { S.gMin = null; S.gMax = null; });
  }
  function rng(lab, lo, hi, f, k1, k2) {
    if (lo == null && hi == null) return;
    add(lab + " " + (lo != null && hi != null ? f(lo) + "–" + f(hi) : (lo != null ? "≥ " + f(lo) : "≤ " + f(hi))), function () { S[k1] = null; S[k2] = null; });
  }
  rng("Cena", S.pMin, S.pMax, fmtM, "pMin", "pMax"); rng("Kč/m²", S.m2Min, S.m2Max, fmt, "m2Min", "m2Max"); rng("Plocha", S.aMin, S.aMax, function (v) { return fmt(v) + " m²"; }, "aMin", "aMax");
  if (S.dv != null) add("Pod férovou ≥ " + S.dv + " %", function () { S.dv = null; });
  if (S.drop) add("Jen zlevněné", function () { S.drop = false; });
  if (S.nove != null) add(S.nove === 0 ? "Nové dnes" : "Nové ≤ " + S.nove + " d", function () { S.nove = null; });
  if (!S.clean) add("Balast zobrazen", function () { S.clean = true; });
  if (S.rk) add("Bez „RK nevolat“", function () { S.rk = false; });
  if (S.pc) add(S.pc === "hide" ? "Bez podezřele levných" : "Jen podezřele levné", function () { S.pc = ""; });
  if (S.pz) add("Jen reálné kupy", function () { S.pz = false; });
  if (S.mot != null) add("Motivace ≥ " + S.mot, function () { S.mot = null; });
  if (S.prMax != null) add("Prezentace ≤ " + S.prMax, function () { S.prMax = null; });
  if (S.hid) add("Jen skryté", function () { S.hid = 0; });
  $("achips").innerHTML = CHIPS.map(function (c, i) {
    return '<span class="ach">' + esc(c.label) + '<button type="button" data-rm="' + i + '" aria-label="Zrušit filtr: ' + esc(c.label) + '">&#10005;</button></span>';
  }).join("");
}

/* ---------- souhrn ---------- */
function renderSummary() {
  var el = $("sumline");
  if (S.tab === "fav") {
    el.innerHTML = '<span class="big"><b>' + fmt(SORTED.length) + '</b> oblíbených</span>' + favMissingHTML();
    return;
  }
  var sm = summarize(P, S, R.idx), n = sm.n;
  if (!n) { el.innerHTML = '<span class="big"><b>0</b> inzerátů</span><span>Nic neodpovídá filtrům.</span>'; return; }
  var ageLbl = S.ageMode === "ao" ? "medián sledování" : "medián stáří";
  el.innerHTML = '<span class="big"><b>' + fmt(n) + '</b> inzerátů <span class="of">z ' + fmt(P.n) + '</span></span>' +
    '<span>medián ceny <b>' + fmtM(sm.medP) + '</b></span><span>medián Kč/m² <b>' + fmt(sm.medM2) + '</b></span>' +
    '<span>' + ageLbl + ' <b>' + fmt(sm.medAg) + ' d</b></span><span>zlevněných <b>' + fmt1(sm.dropPct) + ' %</b></span>' +
    '<span>s adresou <b>' + fmt(sm.adr) + '</b></span>';
}
function favMissingHTML() {
  var miss = [];
  FAVS.forEach(function (u) { if (!P.urlMap.has(u)) miss.push(u); });
  return miss.length ? '<span>· ' + miss.length + ' uložených už v datech není (inzerát stažen)</span>' : "";
}

/* ---------- seznam ---------- */
function hbtn(key, label, cls) {
  var on = S.sort === key, dir = S.dir || SORTS[key].d;
  return '<button type="button" class="' + cls + '" data-sort="' + key + '"' + (on ? ' aria-sort="' + (dir > 0 ? "ascending" : "descending") + '"' : "") + '>' + label + '</button>';
}
function rowHTML(n, pos) {
  var l = P.L[n], im = S.img ? safeUrl(l.im) : "";
  var img = im ? '<img class="th" src="' + esc(im) + '" alt="" width="52" height="39" decoding="async" referrerpolicy="no-referrer">' : '<span class="th ni"></span>';
  var price = l.p != null ? '<b>' + fmt(l.p) + '</b>' + (l.p0 ? '<s>' + fmt(l.p0) + '</s>' : "") + (l.dd ? '<span class="dd">−' + fmt1(l.dd) + ' %</span>' : "") : '<span class="mut">na dotaz</span>';
  var pct = P.pct[n], pbar = "";
  if (pct === pct) {
    var est = P.pctSrc[n] === 2;
    pbar = '<span class="pbar' + (est ? " est" : "") + '" title="' + (est ? "Percentil Kč/m² v kraji a typu (hrubý odhad z dat boardu)" : "Percentil Kč/m² mezi srovnatelnými") + ': ' + Math.round(pct) + '. — levnější než ' + Math.round(100 - pct) + ' % trhu"><i style="width:' + pct.toFixed(0) + '%"></i><u style="left:' + pct.toFixed(0) + '%"></u></span>';
  }
  var m2 = l.m2 != null ? '<span class="lbl">Kč/m²</span><span class="v">' + fmt(l.m2) + '</span>' + pbar : '<span class="lbl">Kč/m²</span><span class="mut">—</span>';
  var fair = '<span class="lbl">vs. fér.</span>';
  if (l.dv != null) {
    fair += l.dv >= 1 ? '<span class="fair-pod" title="Cena je o ' + l.dv + ' % pod modelovou férovou cenou">−' + fmt(l.dv) + ' %</span>' :
      (l.dv <= -1 ? '<span class="fair-nad" title="Cena je o ' + (-l.dv) + ' % nad modelovou férovou cenou">+' + fmt(-l.dv) + ' %</span>' : '<span class="mut">≈</span>');
    if (l.f) fair += '<span class="fair-sub">fér. ' + fmtM(l.f) + '</span>';
  } else fair += '<span class="mut">—</span>';
  var asz = S.ageMode === "ao" ? P.ao[n] : P.agm[n];
  var age = '<span class="lbl">Stáří</span><b>' + fmt(asz) + ' d</b>' + (S.ageMode === "ao" ? "" : jdot(l.aj)) + (l.ab ? '<small>obn. ' + fmtDateShort(l.ab) + '</small>' : "");
  var srcs = (l.s || []).map(function (s) { return '<span class="src ' + esc(s) + '">' + esc(SRC[s] || s) + '</span>'; }).join(" + ");
  var l3 = [esc(krajLabel(l.k)), esc(TYP[l.c] || l.c), l.a != null ? fmt(l.a) + " m²" : "", srcs].filter(Boolean).join(" · ");
  var favOn = P.favf[n], hidOn = P.hidf[n];
  return '<article class="row' + (pos === cur ? " cur" : "") + (favOn ? " fav" : "") + (hidOn ? " hid" : "") + '" data-n="' + n + '" data-pos="' + pos + '" tabindex="' + ((cur >= 0 ? pos === cur : pos === page * PAGE) ? 0 : -1) + '" aria-label="' + esc((l.l || "") + (l.p != null ? ", " + fmt(l.p) + " Kč" : "")) + '">' +
    '<div class="c-img">' + img + '</div>' +
    '<div class="c-main"><div class="l1"><span class="loc">' + esc(l.l || "—") + '</span>' + badges(l) + '</div><div class="l2">' + esc(redact(l.t || "")) + '</div><div class="l3">' + l3 + '</div></div>' +
    '<div class="c-price"><span class="lbl">Cena</span>' + price + '</div>' +
    '<div class="c-m2">' + m2 + '</div><div class="c-fair">' + fair + '</div>' +
    '<div class="c-age" title="' + esc(ageTitle(l)) + '">' + age + '</div>' +
    '<div class="c-ct">' + ctIcons(l) + '</div>' +
    '<div class="c-tip">' + akBadge(l.ak) + '<span class="tptxt">' + esc(l.tp || "") + '</span></div>' +
    '<div class="c-act"><button type="button" class="act' + (favOn ? " on" : "") + '" data-act="fav" aria-pressed="' + (favOn ? "true" : "false") + '" aria-label="Oblíbené" title="Oblíbené (f)">&#9733;</button>' +
    '<button type="button" class="act" data-act="hide" aria-label="' + (hidOn ? "Vrátit mezi viditelné" : "Skrýt") + '" title="' + (hidOn ? "Vrátit (x)" : "Skrýt (x)") + '">' + (hidOn ? "&#8617;" : "&#10005;") + '</button></div>' +
    '</article>';
}
function renderList() {
  var el = $("list"), hadFocus = el.contains(document.activeElement);   // innerHTML zahodí prvek s focusem → po překreslení ho vrátíme na kurzor
  var sortFocus = hadFocus && document.activeElement.dataset ? document.activeElement.dataset.sort : null;
  renderListInner(el);
  if (sortFocus) { var sb = el.querySelector('[data-sort="' + sortFocus + '"]'); if (sb) sb.focus({ preventScroll: true }); return; }
  if (hadFocus && cur >= 0) { var fr = el.querySelector('.row[data-pos="' + cur + '"]'); if (fr) { fr.tabIndex = 0; fr.focus({ preventScroll: true }); } }
}
function renderListInner(el) {
  if (!SORTED.length) {
    el.innerHTML = S.tab === "fav" ?
      '<div class="empty">Zatím žádné oblíbené. Hvězdičkou ★ u inzerátu (nebo klávesou f) si je tu uložíš.</div>' :
      '<div class="empty">Nic neodpovídá filtrům.<br><button type="button" class="btn" data-act="reset">Zrušit všechny filtry</button></div>';
    if (S.tab === "fav") el.innerHTML += missingFavsHTML();
    return;
  }
  var from = page * PAGE, to = Math.min(SORTED.length, from + PAGE), h =
    '<div class="hdr" role="row"><span class="h-img"></span>' + hbtn("l", "Lokalita / titulek", "h-main") + hbtn("p", "Cena", "h-price") + hbtn("m2", "Kč/m²", "h-m2") +
    hbtn("dv", "vs. férová", "h-fair") + hbtn("ag", "Stáří", "h-age") + '<span class="h-ct">Kontakt</span>' + hbtn("sc", "Akce / tip", "h-tip") + '<span class="h-act"></span></div>';
  for (var p = from; p < to; p++) h += rowHTML(SORTED[p], p);
  el.innerHTML = h + (S.tab === "fav" ? missingFavsHTML() : "");
}
function missingFavsHTML() {
  var miss = [];
  FAVS.forEach(function (u) { if (!P.urlMap.has(u)) miss.push(u); });
  if (!miss.length) return "";
  return '<div class="empty" style="text-align:left"><b>Už nejsou v datech</b> (inzerát stažen / prodán) — ' + miss.length + ' uložených odkazů:<ul>' +
    miss.map(function (u) { var su = safeUrl(u); return '<li>' + (su ? '<a href="' + esc(su) + '" target="_blank" rel="noopener noreferrer">' + esc(u) + '</a>' : esc(u)) + ' <button type="button" class="lnk" data-act="unfavurl" data-u="' + esc(u) + '">odebrat</button></li>'; }).join("") + '</ul></div>';
}
function renderPager() {
  var pages = Math.ceil(SORTED.length / PAGE), el = $("pager");
  if (pages <= 1) { el.innerHTML = SORTED.length ? '<span>' + fmt(SORTED.length) + ' z ' + fmt(SORTED.length) + '</span>' : ""; return; }
  var from = page * PAGE + 1, to = Math.min(SORTED.length, (page + 1) * PAGE);
  el.innerHTML = '<button type="button" class="btn" data-p="0"' + (page <= 0 ? " disabled" : "") + ' aria-label="První strana">&laquo;</button>' +
    '<button type="button" class="btn" data-p="' + (page - 1) + '"' + (page <= 0 ? " disabled" : "") + ' aria-label="Předchozí strana">&lsaquo;</button>' +
    '<span>' + fmt(from) + '–' + fmt(to) + ' z ' + fmt(SORTED.length) + ' · strana ' + (page + 1) + ' / ' + pages + '</span>' +
    '<button type="button" class="btn" data-p="' + (page + 1) + '"' + (page >= pages - 1 ? " disabled" : "") + ' aria-label="Další strana">&rsaquo;</button>' +
    '<button type="button" class="btn" data-p="' + (pages - 1) + '"' + (page >= pages - 1 ? " disabled" : "") + ' aria-label="Poslední strana">&raquo;</button>';
}
function gotoPage(p) {
  var pages = Math.max(1, Math.ceil(SORTED.length / PAGE));
  page = Math.max(0, Math.min(pages - 1, p)); cur = -1;
  renderList(); renderPager();
  var sc = $("list").getBoundingClientRect().top + window.scrollY - 110; window.scrollTo(0, Math.max(0, sc));
}
function setCur(pos, scroll) {
  if (!SORTED.length) return;
  pos = Math.max(0, Math.min(SORTED.length - 1, pos));
  var pg = Math.floor(pos / PAGE);
  cur = pos;
  if (pg !== page) { page = pg; renderList(); renderPager(); }
  else {
    var old = $("list").querySelector(".row.cur"); if (old) old.classList.remove("cur");
    var nw = $("list").querySelector('.row[data-pos="' + pos + '"]'); if (nw) nw.classList.add("cur");
  }
  // roving tabindex: fokus jde za kurzorem (čtečky + Enter na řádku), Tab pak vede z aktuálního řádku
  $("list").querySelectorAll('.row[tabindex="0"]').forEach(function (r) { r.tabIndex = -1; });
  var fr = $("list").querySelector('.row[data-pos="' + pos + '"]'); if (fr) { fr.tabIndex = 0; fr.focus({ preventScroll: true }); }
  if (scroll !== false) {
    var r = $("list").querySelector('.row[data-pos="' + pos + '"]');
    if (r) { var b = r.getBoundingClientRect(); if (b.top < 110 || b.bottom > window.innerHeight - 10) r.scrollIntoView({ block: "center" }); }
  }
}
function leadAtCur() { return cur >= 0 && cur < SORTED.length ? SORTED[cur] : -1; }

/* ---------- detail ---------- */
function loadShard(id) {
  var s = shardOf(id);
  if (!SHARD[s]) {
    SHARD[s] = fetch(shardFile(id) + "?v=" + encodeURIComponent(P.gen || ""))
      .then(function (r) { if (!r.ok) throw new Error("HTTP " + r.status); return r.json(); })
      .catch(function (e) { delete SHARD[s]; throw e; });
  }
  return SHARD[s];
}
function findPos(n) { for (var i = 0; i < SORTED.length; i++) if (SORTED[i] === n) return i; return -1; }
function openDetail(n, pos) {
  if (pos == null) pos = findPos(n);
  if (pos >= 0) { cur = pos; var pg = Math.floor(pos / PAGE); if (pg !== page) { page = pg; renderList(); renderPager(); } }
  if (detailN < 0) lastFocus = document.activeElement;
  detailN = n; S.d = P.L[n].i;
  $("dwrap").hidden = false; document.body.classList.add("noscroll"); setInert(true);
  renderDetail(n, null, "loading");
  var oldRow = $("list").querySelector(".row.cur"); if (oldRow) oldRow.classList.remove("cur");
  var newRow = pos >= 0 ? $("list").querySelector('.row[data-pos="' + pos + '"]') : null; if (newRow) newRow.classList.add("cur");
  loadShard(P.L[n].i).then(function (sh) {
    if (detailN !== n) return;
    renderDetail(n, sh[P.L[n].i] || {}, "ok");
  }).catch(function () { if (detailN === n) renderDetail(n, null, "err"); });
  var dp = $("dp"); dp.scrollTop = 0; dp.focus({ preventScroll: true });
  syncHash();
}
// pozadí za otevřeným detailem nesmí dostávat focus ani být čtené (modální panel)
function setInert(on) {
  ["top", "pane-list", "pane-trh", "foot"].forEach(function (id) { var e = $(id); if (e) { if (on) e.setAttribute("inert", ""); else e.removeAttribute("inert"); } });
}
function closeDetail() {
  if (detailN < 0) return;
  detailN = -1; S.d = null; $("dwrap").hidden = true; document.body.classList.remove("noscroll"); setInert(false);
  if (lastFocus && lastFocus.focus) { try { lastFocus.focus({ preventScroll: true }); } catch (e) { /* nic */ } }
  syncHash();
}
function detailStep(d) {
  var pos = findPos(detailN); if (pos < 0) return;
  var np = pos + d; if (np < 0 || np >= SORTED.length) return;
  openDetail(SORTED[np], np);
  var r = $("list").querySelector('.row[data-pos="' + np + '"]'); if (r) r.scrollIntoView({ block: "nearest" });
}
function sparkSVG(ph) {
  var pts = (ph || []).filter(function (a) { return a && a.length >= 2 && a[1] != null; });
  if (pts.length < 2) return "";
  var xs = pts.map(function (a) { return dayNum(a[0]); }), ys = pts.map(function (a) { return a[1]; });
  var x0 = Math.min.apply(null, xs), x1 = Math.max.apply(null, xs), y0 = Math.min.apply(null, ys), y1 = Math.max.apply(null, ys);
  if (x1 === x0) x1 = x0 + 1; if (y1 === y0) { y1 = y0 + 1; }
  var W = 300, H = 60, px = function (i) { return 6 + (xs[i] - x0) / (x1 - x0) * (W - 12); }, py = function (i) { return 6 + (1 - (ys[i] - y0) / (y1 - y0)) * (H - 12); };
  var d = pts.map(function (a, i) { return (i ? "L" : "M") + px(i).toFixed(1) + " " + py(i).toFixed(1); }).join(" ");
  var dots = pts.map(function (a, i) { return '<circle class="pt' + (i === pts.length - 1 ? " last" : "") + '" cx="' + px(i).toFixed(1) + '" cy="' + py(i).toFixed(1) + '" r="3"><title>' + esc(fmtDate(a[0]) + ": " + fmt(a[1]) + " Kč") + '</title></circle>'; }).join("");
  return '<svg class="spark" viewBox="0 0 ' + W + ' ' + H + '" preserveAspectRatio="none" role="img" aria-label="Vývoj ceny"><path class="ln" d="' + d + '"/>' + dots + '</svg>' +
    '<div class="sparklab"><span>' + esc(fmtDate(pts[0][0])) + ': ' + fmt(pts[0][1]) + ' Kč</span><span>' + esc(fmtDate(pts[pts.length - 1][0])) + ': ' + fmt(pts[pts.length - 1][1]) + ' Kč</span></div>';
}
function cell(k, v, s) { return '<div class="cell"><div class="k">' + esc(k) + '</div><div class="v">' + v + '</div>' + (s ? '<div class="s">' + s + '</div>' : "") + '</div>'; }
function negHTML(neg) {
  if (neg == null || neg === "") return "";
  if (typeof neg === "number") return neg <= 100 ? "až " + fmt1(neg) + " %" : "až " + fmt(neg) + " Kč";
  if (typeof neg === "string") return esc(neg);
  if (typeof neg === "object") return Object.keys(neg).map(function (k) { return esc(k) + ": " + esc(typeof neg[k] === "object" ? JSON.stringify(neg[k]) : neg[k]); }).join(" · ");
  return "";
}
function renderDetail(n, dt, state) {
  var l = P.L[n], x = (l.x && typeof l.x === "object") ? l.x : null, dd = dt || {}, pos = findPos(n), h = "";
  var hero = S.img ? safeUrl(dd.ib) || safeUrl(l.im) : "";
  h += '<div class="dnav"><button type="button" class="btn" data-act="dprev" aria-label="Předchozí inzerát (←)"' + (pos <= 0 ? " disabled" : "") + '>&larr;</button>' +
    '<button type="button" class="btn" data-act="dnext" aria-label="Další inzerát (→)"' + (pos < 0 || pos >= SORTED.length - 1 ? " disabled" : "") + '>&rarr;</button>' +
    '<span class="pos">' + (pos >= 0 ? fmt(pos + 1) + " / " + fmt(SORTED.length) : "mimo aktuální výběr") + '</span>' +
    '<button type="button" class="btn" data-act="dclose" aria-label="Zavřít detail (Esc)">&#10005; Zavřít</button></div>';
  h += hero ? '<img class="dhero" id="dhero" src="' + esc(hero) + '" data-fb="' + esc(safeUrl(l.im)) + '" alt="" decoding="async" referrerpolicy="no-referrer">' :
    '<div class="dhero-ni">' + (S.img ? "bez fotky" : "fotky jsou vypnuté (tlačítko Fotky)") + '</div>';
  h += '<div class="db"><h2 class="dt">' + esc(redact(l.t || l.l || "")) + '</h2><div class="dl">' + esc(l.l || "") + ' · ' + esc(krajLabel(l.k)) + ' · ' + esc(TYP[l.c] || l.c) + ' · ' +
    (l.s || []).map(function (s) { return esc(SRC[s] || s); }).join(" + ") + '</div><div class="dbadges">' + akBadge(l.ak) + badges(l) + '</div>';
  // klíčová čísla
  var dv = l.dv != null ? (l.dv >= 1 ? "o " + fmt(l.dv) + " % pod férovou" : (l.dv <= -1 ? "o " + fmt(-l.dv) + " % nad férovou" : "≈ férová")) : "";
  var pct = P.pct[n];
  var cells = cell("Cena", l.p != null ? fmt(l.p) + " Kč" : "na dotaz", l.p0 ? '<s>' + fmt(l.p0) + ' Kč</s>' + (l.dd ? " · −" + fmt1(l.dd) + " %" : "") : "");
  cells += cell("Kč/m²", l.m2 != null ? fmt(l.m2) : "—", l.a != null ? fmt(l.a) + " m²" : "");
  if (l.f) cells += cell("Férová cena (model)", fmt(l.f) + " Kč", esc(dv));
  if (pct === pct) cells += cell("Percentil Kč/m²", "P" + Math.round(pct), (P.pctSrc[n] === 2 ? "hrubý odhad v kraji a typu" : "mezi srovnatelnými") + (x && x.cn != null && typeof x.cn !== "object" ? " · n = " + esc(x.cn) : ""));
  cells += cell("Stáří", fmt(l.ag != null ? l.ag : l.ao) + " d " + (l.ag != null ? jdot(l.aj) : ""), "jistota " + (l.ag != null ? JTXT[l.aj] || "nízká" : "—"));
  if (x && x.mot != null) cells += cell("Motivace", esc(fmt(x.mot)) + " / 100", x.liq ? esc(LIQ_LABEL[x.liq] || x.liq) : "");
  h += '<div class="dgrid">' + cells + '</div>';
  // vývoj ceny
  var spark = sparkSVG(dd.ph);
  h += '<div class="dh">Vývoj ceny</div>' + (spark || '<div class="dtxt mut">' + (state === "loading" ? "Načítám…" : "Bez změny ceny za dobu sledování (" + fmt(l.ao) + " d).") + '</div>');
  // stáří s důkazem
  h += '<div class="dh">Stáří a důkaz</div><div class="dtxt"><b>' + (l.ag != null ? fmt(l.ag) + " dní" : "—") + '</b> ' + (l.ag != null ? jdot(l.aj) : "") +
    '<ul class="dlist" style="margin-top:6px"><li>Vznikl (odhad motoru): <b>' + esc(fmtDate(l.an)) + '</b></li>' +
    '<li>Naposledy obnoveno — to datum vidí majitel na portálu: <b>' + esc(fmtDate(l.ab)) + '</b></li>' +
    '<li>Sledujeme: <b>' + fmt(l.ao) + ' dní</b> (poprvé viděno ' + esc(fmtDate(l.fs)) + ', naposledy ' + esc(fmtDate(l.ls)) + ')</li></ul>' +
    (dd.aw ? '<p class="note">' + esc(dd.aw) + '</p>' : (state === "loading" ? '<p class="note">Načítám důkaz…</p>' : "")) + '</div>';
  // motivace
  if (x && (x.mw && x.mw.length || x.neg != null)) {
    h += '<div class="dh">Motivace a vyjednávání</div>';
    if (Array.isArray(x.mw) && x.mw.length) h += '<ul class="dlist">' + x.mw.map(function (w) { return '<li class="mot">' + esc(w) + '</li>'; }).join("") + '</ul>';
    var ng = negHTML(x.neg); if (ng) h += '<div class="dtxt" style="margin-top:6px">Prostor k vyjednávání: <b>' + ng + '</b></div>';
  }
  // srovnatelné
  if (x && Array.isArray(x.cp) && x.cp.length) h += compsHTML(l, x);
  // kontakty
  h += '<div class="dh">Kontakt (jen příznaky)</div><div class="ctrow">' +
    '<span class="it">' + ctIcons(l) + '</span>' +
    '<span class="it">Tel.: <b>' + (l.tel === true ? "v inzerátu" : (l.tel === "w" ? "jen na webu" : "nenalezen")) + '</b></span>' +
    '<span class="it">E-mail: <b>' + (l.em ? "ano" : "ne") + '</b></span>' +
    '<span class="it">Adresa: <b>' + esc(ADR[l.adr] || "nenalezena") + '</b></span></div>';
  if (l.sl === "m") h += '<div class="warnbox"><b>Pozor:</b> detail inzerátu říká, že prodává makléř / realitka. Neoslovuj jako soukromníka.</div>';
  else if (l.sl === "s") h += '<div class="dtxt mut">Ověřený soukromý prodejce (z detailu inzerátu).</div>';
  h += '<p class="note box">Oslovení majitelů = jen <b>papírový dopis</b> (e-maily zakazuje zákon č. 480/2004 Sb.), proto je nejcennější adresa. ' +
    (l.kz === "text" ? "Příznaky jsou zatím odhad z textu inzerátu." : "Příznaky jsou ověřené z detailu inzerátu.") + '</p>';
  // tip + důvody
  if (l.tp) h += '<div class="dh">Co s tím</div><div class="dtxt"><b>' + esc(l.tp) + '</b></div>';
  if (dd.w && dd.w.length) h += '<ul class="dlist" style="margin-top:8px">' + dd.w.map(function (w) { return '<li' + (/pozor|podíl|mobilheim|dražb|pronáj|výkup/i.test(w) ? ' class="neg"' : "") + '>' + esc(w) + '</li>'; }).join("") + '</ul>';
  // popis
  h += '<div class="dh">Popis z inzerátu</div>' + (dd.d ? '<div class="dtxt desc">' + esc(redact(dd.d).replace(/\s*\n\s*(\n\s*)+/g, "\n\n").trim()) + '</div>' :
    '<div class="dtxt mut">' + (state === "loading" ? "Načítám popis…" : (state === "err" ? "Detail se nepodařilo načíst (zkus to za chvíli)." : "Bez popisu.")) + '</div>');
  // odkazy + akce
  var urls = [l.u].concat(l.us || []);
  h += '<div class="links">' + urls.map(function (u, i) {
    var su = safeUrl(u), srcName = /bazos/i.test(u) ? "bazoš" : (/annonce/i.test(u) ? "annonce.cz" : "inzerát");
    return su ? '<a href="' + esc(su) + '" target="_blank" rel="noopener noreferrer">Otevřít na ' + srcName + (urls.length > 1 ? " #" + (i + 1) : "") + ' &nearr;</a>' : "";
  }).join("") +
    '<button type="button" class="sec" data-act="dfav" aria-pressed="' + (P.favf[n] ? "true" : "false") + '">&#9733; ' + (P.favf[n] ? "V oblíbených" : "Do oblíbených") + ' (f)</button>' +
    '<button type="button" class="sec" data-act="dhide">' + (P.hidf[n] ? "&#8617; Vrátit" : "&#10005; Skrýt") + ' (x)</button></div></div>';
  $("dp").innerHTML = h;
}
function compsHTML(l, x) {
  var rows = x.cp.filter(function (c) { return Array.isArray(c); }), m2s = rows.map(function (c) { return c[3]; }).filter(function (v) { return typeof v === "number"; });
  var med = m2s.length >= 3 ? median(m2s) : NaN;
  var h = '<div class="dh">Srovnatelné inzeráty</div>';
  if (x.cg != null && typeof x.cg !== "object") h += '<div class="dtxt mut" style="margin-bottom:6px">Srovnání: ' + esc(CG_LABEL[x.cg] || x.cg) + (x.cn != null && typeof x.cn !== "object" ? " (n = " + esc(x.cn) + ")" : "") + '</div>';
  h += '<table class="cmp"><thead><tr><th>Inzerát</th><th>Cena</th><th>m²</th><th>Kč/m²</th><th>vs. tento</th></tr></thead><tbody>';
  h += '<tr class="me"><td>Tento inzerát</td><td>' + fmt(l.p) + '</td><td>' + fmt(l.a) + '</td><td>' + fmt(l.m2) + '</td><td>' + (med === med && l.m2 ? (l.m2 < med ? "−" : "+") + fmt(Math.abs(l.m2 - med) / med * 100) + " % vs. medián" : "") + '</td></tr>';
  rows.forEach(function (c) {
    var key = String(c[0] == null ? "" : c[0]), nn = P.idMap.get(key), cl = nn != null ? P.L[nn] : null;
    var name = cl ? (cl.l || key) : key;
    var diff = (l.m2 && typeof c[3] === "number" && c[3]) ? (l.m2 < c[3] ? "−" : "+") + fmt(Math.abs(l.m2 - c[3]) / c[3] * 100) + " %" : "";
    h += '<tr><td>' + (nn != null ? '<button type="button" data-act="cmp" data-n="' + nn + '">' + esc(name) + '</button>' : esc(name)) + '</td><td>' + fmt(c[1]) + '</td><td>' + fmt(c[2]) + '</td><td>' + fmt(c[3]) + '</td><td>' + diff + '</td></tr>';
  });
  return h + '</tbody></table>';
}

/* ---------- záložka Trh ---------- */
function getTrh() { if (!TRH) TRH = trhMatrix(P); return TRH; }
function metricRank(vals) {   // pořadí hodnot → 0..1 (heatmapa po sloupcích, ať se srovnávají kraje v rámci jednoho typu)
  var s = vals.filter(function (v) { return v != null; }).sort(function (a, b) { return a - b; });
  return function (v) { if (v == null || s.length < 2) return 0; var lo = s.indexOf(v); return lo / (s.length - 1); };
}
function renderTrh() {
  var M = getTrh(), mt = METRICS.filter(function (m) { return m.k === S.mt; })[0] || METRICS[0];
  var krs = P.krajList.filter(function (k) { return M[k + "|*"]; }), typs = P.typList.filter(function (t) { return M["*|" + t]; });
  var h = '<h2>Trh podle kraje a typu</h2><div class="msw" role="group" aria-label="Ukazatel">' + METRICS.map(function (m) {
    return '<button type="button" class="cb" data-metric="' + m.k + '" aria-pressed="' + (m.k === mt.k ? "true" : "false") + '" title="' + esc(m.tip) + '">' + esc(m.l) + '</button>';
  }).join("") + '</div>';
  var rank = {};
  typs.forEach(function (t) { rank[t] = metricRank(krs.map(function (k) { var c = M[k + "|" + t]; return c ? c[mt.k] : null; })); });
  h += '<table class="hm" style="--hue:var(' + mt.hue + ')"><thead><tr><th class="rh" scope="col">Kraj</th>' + typs.map(function (t) { return '<th scope="col">' + esc(TYP[t] || t) + '</th>'; }).join("") + '<th scope="col">Celkem</th></tr></thead><tbody>';
  function cellHTML(c, k, t, heat) {
    if (!c) return '<button type="button" class="hmc na" disabled>—</button>';
    // buňka existuje (je v ní n inzerátů), jen vybraný ukazatel nemá z čeho vzniknout (např. Kč/m² u pozemků) → klikatelná, bez barvy
    if (c[mt.k] == null) return '<button type="button" class="hmc na" data-cell-k="' + esc(k) + '" data-cell-t="' + esc(t) + '" title="Ukazatel nelze spočítat (málo dat), klik = seznam leadů">—<small>n ' + fmt(c.n) + '</small></button>';
    var tip = (k === "*" ? "Celá ČR" : krajLabel(k)) + " · " + (t === "*" ? "všechny typy" : TYP[t] || t) + "\n" + METRICS.map(function (m) { return m.l + ": " + (c[m.k] == null ? "—" : m.f(c[m.k])); }).join("\n");
    return '<button type="button" class="hmc' + (heat == null ? " tot" : "") + '" data-cell-k="' + esc(k) + '" data-cell-t="' + esc(t) + '"' + (heat != null ? ' style="--t:' + Math.round(heat * 45) + '%"' : "") +
      ' title="' + esc(tip) + '">' + mt.f(c[mt.k]) + '<small>n ' + fmt(c.n) + '</small></button>';
  }
  krs.forEach(function (k) {
    h += '<tr><th class="rh" scope="row">' + esc(krajLabel(k)) + '</th>' + typs.map(function (t) { var c = M[k + "|" + t]; return '<td>' + cellHTML(c, k, t, c && c[mt.k] != null ? rank[t](c[mt.k]) : null) + '</td>'; }).join("") + '<td>' + cellHTML(M[k + "|*"], k, "*", null) + '</td></tr>';
  });
  h += '<tr><th class="rh" scope="row">Celá ČR</th>' + typs.map(function (t) { return '<td>' + cellHTML(M["*|" + t], "*", t, null) + '</td>'; }).join("") + '<td>' + cellHTML(M["*|*"], "*", "*", null) + '</td></tr></tbody></table>';
  h += '<div class="legend" style="--hue:var(' + mt.hue + ')">méně <i></i> více (barva se porovnává uvnitř typu — kraj proti krajům) · klik na buňku = seznam leadů s tímto filtrem</div>';
  h += radarHTML();
  $("pane-trh").innerHTML = h;
}
function radarHTML() {
  var R0 = (P.meta && P.meta.radar) || null; if (!R0) return "";
  var h = '<h2>Radar trhu</h2><div class="rstats">';
  if (R0.n_deals != null) h += '<button type="button" class="rstat" data-go="preset:kupy"><b>' + fmt(R0.n_deals) + '</b>reálných kupů pod férovou cenou</button>';
  if (R0.n_suspicious != null) h += '<button type="button" class="rstat" data-go="susp"><b>' + fmt(R0.n_suspicious) + '</b>podezřele levných (háček?)</button>';
  h += '</div><div class="rad">';
  // nejzamrzlejší trhy
  var fz = Array.isArray(R0.frozen_markets) ? R0.frozen_markets : [];
  if (fz.length) {
    var mx = Math.max.apply(null, fz.map(function (f) { return f.avg_age || 0; })) || 1;
    h += '<div class="rcard"><h3>Nejzamrzlejší trhy</h3><p>Kde inzeráty visí nejdéle (průměrné stáří). Tam majitelé sami neprodávají — nábor a nabídka služeb mají největší šanci.</p>' +
      fz.map(function (f) {
        return '<button type="button" class="rr" data-go="cell:' + esc(f.kraj) + ':' + esc(f.cat) + '"><span>' + esc(krajLabel(f.kraj)) + ' · ' + esc(TYP[f.cat] || f.cat) + '<span class="sub">n = ' + fmt(f.n) + '</span></span><span class="bar"><i style="width:' + Math.round((f.avg_age || 0) / mx * 100) + '%"></i></span><b>' + fmt1(f.avg_age) + ' d</b></button>';
      }).join("") + '</div>';
  }
  // poptávka výkupců
  var dm = R0.demand_map && typeof R0.demand_map === "object" ? Object.keys(R0.demand_map).map(function (k) { var v = R0.demand_map[k] || {}; return { k: k, nab: v.nabidka || 0, pop: v.poptavka || 0, idx: v.index || 0 }; }) : [];
  if (dm.length) {
    dm.sort(function (a, b) { return b.pop - a.pop || b.idx - a.idx || b.nab - a.nab; });
    var mp = Math.max.apply(null, dm.map(function (d) { return d.pop; })) || 1, tot = dm.reduce(function (a, d) { return a + d.pop; }, 0);
    h += '<div class="rcard"><h3>Poptávka výkupců</h3><p>Výkupní inzeráty („koupím / ihned zaplatím“) vs. nabídky v kraji = kde je hlad kupců.' + (tot < 20 ? " Zatím jen " + fmt(tot) + " výkupních inzerátů, takže spíš orientačně." : "") + '</p>' +
      dm.slice(0, 8).map(function (d) {
        return '<button type="button" class="rr" data-go="cell:' + esc(d.k) + ':*"><span>' + esc(krajLabel(d.k)) + '<span class="sub">' + fmt(d.nab) + ' nabídek</span></span><span class="bar"><i style="width:' + Math.round(d.pop / mp * 100) + '%"></i></span><b>' + fmt(d.pop) + '</b></button>';
      }).join("") + '</div>';
  }
  // kraj index
  var ki = R0.kraj_index && typeof R0.kraj_index === "object" ? Object.keys(R0.kraj_index).filter(function (k) { return k !== "?"; }).map(function (k) { return [k, R0.kraj_index[k]]; }) : [];
  if (ki.length) {
    ki.sort(function (a, b) { return b[1] - a[1]; });
    var ma = Math.max.apply(null, ki.map(function (e) { return Math.abs(e[1]); })) || 1;
    h += '<div class="rcard"><h3>Cenová hladina krajů</h3><p>O kolik je kraj dražší / levnější než průměr při stejné ploše (model, očištěno).</p>' +
      ki.map(function (e) {
        var w = Math.round(Math.abs(e[1]) / ma * 50), st = e[1] >= 0 ? 'left:50%;width:' + w + '%' : 'left:' + (50 - w) + '%;width:' + w + '%;background:var(--drop)';
        return '<button type="button" class="rr" data-go="cell:' + esc(e[0]) + ':*"><span>' + esc(e[0]) + '</span><span class="bar mid"><i style="' + st + '"></i></span><b>' + (e[1] > 0 ? "+" : (e[1] < 0 ? "−" : "")) + Math.abs(Math.round(e[1] * 100)) + ' %</b></button>';
      }).join("") + '</div>';
  }
  // doba prodeje
  var sv = R0.survival && typeof R0.survival === "object" ? Object.keys(R0.survival) : [];
  if (sv.length) {
    var ms = Math.max.apply(null, sv.map(function (k) { return R0.survival[k].median_dni || 0; })) || 1;
    h += '<div class="rcard"><h3>Jak dlouho inzerát žije</h3><p>Medián dní, než inzerát zmizí (prodej nebo stažení), podle typu. Delší než medián = nadprůměrně zaseknutý.</p>' +
      sv.map(function (k) {
        var v = R0.survival[k] || {};
        return '<button type="button" class="rr" data-go="cell:*:' + esc(k) + '"><span>' + esc(TYP[k] || k) + '<span class="sub">n = ' + fmt(v.n_events) + ' událostí</span></span><span class="bar"><i style="width:' + Math.round((v.median_dni || 0) / ms * 100) + '%"></i></span><b>' + fmt(v.median_dni) + ' d</b></button>';
      }).join("") + '</div>';
  }
  // cenové hladiny (model)
  var pl = R0.price_levels && typeof R0.price_levels === "object" ? R0.price_levels : null;
  if (pl) {
    var kk = {}, tt = {};
    Object.keys(pl).forEach(function (key) { var p = key.split("|"); kk[p[0]] = 1; tt[p[1]] = 1; });
    var tl = TYP_ORDER.filter(function (t) { return tt[t]; }), kl = Object.keys(kk).sort();
    if (tl.length) h += '<div class="rcard"><h3>Cenové hladiny modelu (Kč/m²)</h3><p>Referenční hladina, ze které se počítá férová cena.</p><table class="lvl"><thead><tr><th>Kraj</th>' + tl.map(function (t) { return '<th>' + esc(TYP[t] || t) + '</th>'; }).join("") + '</tr></thead><tbody>' +
      kl.map(function (k) { return '<tr><td>' + esc(krajLabel(k)) + '</td>' + tl.map(function (t) { return '<td>' + (pl[k + "|" + t] != null ? fmt(pl[k + "|" + t]) : "—") + '</td>'; }).join("") + '</tr>'; }).join("") + '</tbody></table></div>';
  }
  return h + '</div>';
}
function goCell(k, t, extra) {
  var keepImg = S.img; S = defState(); S.img = keepImg; S.tab = "leady";
  if (k && k !== "*") S.kraj.add(k); if (t && t !== "*") S.typ.add(t);
  if (extra) extra(S);
  $("pane-trh").hidden = true; setTab("leady");
}

/* ---------- uložené pohledy, nápověda, toast, motiv ---------- */
function popClose() { $("pop").hidden = true; $("btn-views").setAttribute("aria-expanded", "false"); $("btn-keys").setAttribute("aria-expanded", "false"); $("pop").dataset.kind = ""; }
function popViews() {
  var vs = lsGet("hlidac_views", []); if (!Array.isArray(vs)) vs = [];
  var h = '<h4>Uložené pohledy</h4>' + (vs.length ? vs.map(function (v, i) {
    return '<div class="vrow"><button type="button" class="go" data-vgo="' + i + '">' + esc(v.name) + '</button><button type="button" class="del" data-vdel="' + i + '" aria-label="Smazat pohled ' + esc(v.name) + '">&#10005;</button></div>';
  }).join("") : '<div class="mut">Zatím žádné. Nastav filtry a ulož je pod názvem.</div>') +
    '<div class="vsave"><input id="vname" class="fin" type="text" placeholder="Název pohledu" aria-label="Název pohledu" maxlength="60"><button type="button" class="btn primary" id="vsave">Uložit</button></div>';
  $("pop").innerHTML = h; $("pop").hidden = false; $("pop").dataset.kind = "views"; $("btn-views").setAttribute("aria-expanded", "true");
}
function popKeys() {
  $("pop").innerHTML = '<h4>Klávesové zkratky</h4>' + [["/", "hledat"], ["j / k", "další / předchozí řádek"], ["Enter", "otevřít detail"], ["← →", "předchozí / další inzerát v detailu"],
    ["Esc", "zavřít detail / panel"], ["f", "oblíbené"], ["x", "skrýt"], ["?", "tato nápověda"]].map(function (k) { return '<div class="krow"><kbd>' + k[0] + '</kbd>' + k[1] + '</div>'; }).join("");
  $("pop").hidden = false; $("pop").dataset.kind = "keys"; $("btn-keys").setAttribute("aria-expanded", "true");
}
function saveView() {
  var name = ($("vname").value || "").trim(); if (!name) { $("vname").focus(); return; }
  var vs = lsGet("hlidac_views", []); if (!Array.isArray(vs)) vs = [];
  var h = toHash(Object.assign({}, S, { d: null })); vs = vs.filter(function (v) { return v.name !== name; }); vs.push({ name: name, h: h });
  lsSet("hlidac_views", vs); popViews(); toast("Pohled „" + name + "“ uložen");
}
var toastT = null;
function toast(msg, label, fn) {
  var t = $("toast"); t.innerHTML = '<span>' + esc(msg) + '</span>' + (label ? '<button type="button" id="toast-act">' + esc(label) + '</button>' : "");
  t.hidden = false; clearTimeout(toastT); toastT = setTimeout(function () { t.hidden = true; }, 6000);
  if (label) $("toast-act").onclick = function () { t.hidden = true; fn(); };
}
function themeNow() { return document.documentElement.getAttribute("data-theme") || (matchMedia("(prefers-color-scheme: dark)").matches ? "dark" : "light"); }
function toggleTheme() { var t = themeNow() === "dark" ? "light" : "dark"; document.documentElement.setAttribute("data-theme", t); try { localStorage.setItem("hlidac_theme", t); } catch (e) { /* bez uložení */ } }
function openSheet() { $("side").classList.add("open"); document.body.classList.add("noscroll"); }
function closeSheet() { $("side").classList.remove("open"); if (detailN < 0) document.body.classList.remove("noscroll"); }

/* ---------- hash ---------- */
function syncHash() {
  if (suppressHash) return;
  var h = toHash(S);
  if (h === hashLast) return;
  hashLast = h;
  try { history.replaceState(null, "", h ? "#" + h : location.pathname + location.search); } catch (e) { /* file:// apod. */ }
}
function applyHashState() {
  var raw = location.hash.replace(/^#/, "");
  hashLast = raw;
  var keepDense = UIP.dense;
  S = fromHash(raw);
  UIP.dense = keepDense;
}

/* ---------- události ---------- */
function setSet(name, v, on) { var s = S[name]; if (on) s.add(v); else s.delete(v); }
var NUMKEYS = { pMin: 1, pMax: 1, m2Min: 1, m2Max: 1, aMin: 1, aMax: 1, dv: 1, mot: 1, prMax: 1, gMin: 1, gMax: 1 };
function bindEvents() {
  document.addEventListener("click", onClick);
  document.addEventListener("keydown", onKey);
  document.addEventListener("focusin", function (e) {
    var r = e.target.closest && e.target.closest(".row"); if (r && r.dataset.pos != null) { cur = +r.dataset.pos; var o = $("list").querySelector(".row.cur"); if (o && o !== r) o.classList.remove("cur"); r.classList.add("cur"); }
  });
  // chyby obrázků nebublají → zachytit v capture fázi (náhled bez fotky prostě zmizí, velký detail spadne na malý náhled)
  document.addEventListener("error", function (e) {
    var t = e.target; if (!t || t.tagName !== "IMG") return;
    if (t.id === "dhero" && t.dataset.fb && t.src !== t.dataset.fb) { t.src = t.dataset.fb; t.dataset.fb = ""; return; }
    if (t.id === "dhero") { t.outerHTML = '<div class="dhero-ni">fotka se nenačetla</div>'; return; }
    t.style.visibility = "hidden";
  }, true);
  $("facets").addEventListener("change", function (e) {
    var t = e.target;
    if (t.dataset.f) { setSet(t.dataset.f, t.dataset.v, t.checked); onFilterChange(); }
    else if (t.dataset.t) { S[t.dataset.t] = t.checked; onFilterChange(); }
    else if (t.dataset.k === "nove") { S.nove = t.value === "" ? null : +t.value; onFilterChange(); }
    else if (t.dataset.k === "pc") { S.pc = t.value; onFilterChange(); }
  });
  $("facets").addEventListener("input", function (e) {
    var t = e.target;
    if (t.id === "f-q") { debounce("q", function () { S.q = t.value.trim(); onFilterChange(); }, 120); return; }
    if (t.id === "sl-lo" || t.id === "sl-hi") {
      var lo = +$("sl-lo").value, hi = +$("sl-hi").value, N = AGE_STOPS.length;
      if (lo > hi) { if (t.id === "sl-lo") lo = hi; else hi = lo; }
      S.gMin = lo > 0 ? AGE_STOPS[Math.min(lo, N - 1)] : null; S.gMax = hi >= N ? null : AGE_STOPS[hi];
      debounce("sl", onFilterChange, 30); return;
    }
    if (NUMKEYS[t.dataset.k]) { var v = parseNum(t.value); debounce("n", function () { S[t.dataset.k] = v; onFilterChange(); }, 200); }
  });
  $("facets").addEventListener("toggle", function (e) { var d = e.target; if (d.dataset && d.dataset.sec) { UIP.open[d.dataset.sec] = d.open; lsSet("hlidac_ui", UIP); } }, true);
  $("hist").addEventListener("click", function (e) {
    var g = e.target.closest("[data-bin]"); if (!g) return; var k = +g.dataset.bin;
    S.gMin = AGE_STOPS[k] || null; S.gMax = k < AGE_STOPS.length - 1 ? AGE_STOPS[k + 1] - 1 : null;
    if (S.gMin === 0) S.gMin = null; onFilterChange();
  });
  $("sortsel").addEventListener("change", function () { S.sort = this.value; S.dir = SORTS[S.sort].d; page = 0; cur = -1; refresh("sort"); });
  window.addEventListener("hashchange", function () {
    if (location.hash.replace(/^#/, "") === hashLast) return;
    applyHashState(); applyStateToUI();
  });
}
function applyStateToUI() {
  $("pane-list").hidden = S.tab === "trh"; $("pane-trh").hidden = S.tab !== "trh";
  var fav = S.tab === "fav"; $("pane-list").classList.toggle("favmode", fav);
  $("side").hidden = fav; $("presets").hidden = fav; $("btn-filters").hidden = fav;
  $("sortsel").value = S.sort; document.body.classList.toggle("dense", UIP.dense);
  page = 0; cur = -1; refresh();
  if (S.d) { var n = P.idMap.get(S.d); if (n != null) openDetail(n); else { S.d = null; } }
}

function onClick(e) {
  var t = e.target, a;
  if (t.closest("#pop") === null && !t.closest("#btn-views") && !t.closest("#btn-keys") && !$("pop").hidden) popClose();
  // záložky
  if ((a = t.closest("[data-tab]"))) { setTab(a.dataset.tab); return; }
  if ((a = t.closest("[data-preset]"))) { applyPreset(a.dataset.preset); return; }
  if ((a = t.closest("[data-rm]"))) { var c = CHIPS[+a.dataset.rm]; if (c) { c.rm(); onFilterChange(); } return; }
  if ((a = t.closest("[data-sort]"))) {
    var k = a.dataset.sort; if (S.sort === k) S.dir = -(S.dir || SORTS[k].d); else { S.sort = k; S.dir = SORTS[k].d; }
    $("sortsel").value = S.sort; page = 0; cur = -1; refresh("sort"); return;
  }
  if ((a = t.closest("[data-p]"))) { gotoPage(+a.dataset.p); return; }
  if ((a = t.closest("[data-metric]"))) { S.mt = a.dataset.metric; renderTrh(); syncHash(); return; }
  if ((a = t.closest("[data-cell-k]"))) { goCell(a.dataset.cellK, a.dataset.cellT); return; }
  if ((a = t.closest("[data-go]"))) {
    var g = a.dataset.go;
    if (g.indexOf("cell:") === 0) { var pr = g.split(":"); goCell(pr[1], pr[2], function (s) { if (pr[1] !== "*" || pr[2] !== "*") { s.sort = "ag"; s.dir = -1; } }); }
    else if (g === "preset:kupy") { var ki0 = S.img; S = presetState(PRESETS.filter(function (p) { return p.id === "kupy"; })[0]); S.img = ki0; setTab("leady"); }
    else if (g === "susp") { goCell("*", "*", function (s) { s.pc = "only"; s.sort = "m2"; s.dir = 1; }); }
    return;
  }
  if ((a = t.closest("[data-vgo]"))) {
    var vs = lsGet("hlidac_views", []); var v = vs[+a.dataset.vgo]; if (v) { var keep = UIP.dense; S = fromHash(v.h); UIP.dense = keep; popClose(); applyStateToUI(); } return;
  }
  if ((a = t.closest("[data-vdel]"))) { var vs2 = lsGet("hlidac_views", []); vs2.splice(+a.dataset.vdel, 1); lsSet("hlidac_views", vs2); popViews(); return; }
  if ((a = t.closest("[data-act]"))) {
    var act = a.dataset.act, rowEl = a.closest(".row"), n = rowEl ? +rowEl.dataset.n : detailN;
    switch (act) {
      case "fav": toggleFav(n); afterFavChange(); if (detailN === n) reloadDetail(n); return;
      case "hide": doHide(n); return;
      case "dfav": toggleFav(detailN); afterFavChange(); reloadDetail(detailN); return;
      case "dhide": doHide(detailN); return;
      case "dclose": closeDetail(); return;
      case "dprev": detailStep(-1); return;
      case "dnext": detailStep(1); return;
      case "cmp": openDetail(+a.dataset.n); return;
      case "reset": resetFilters(); return;
      case "tel": S.tel = a.dataset.v; onFilterChange(); return;
      case "em": S.em = a.dataset.v; onFilterChange(); return;
      case "agemode": S.ageMode = a.dataset.v; onFilterChange(); return;
      case "agequick": { var d = +a.dataset.v; if (S.gMin === d && S.gMax == null) S.gMin = null; else { S.gMin = d; S.gMax = null; } onFilterChange(); return; }
      case "dvquick": { var q = +a.dataset.v; S.dv = S.dv === q ? null : q; onFilterChange(); return; }
      case "unfavurl": FAVS.delete(a.dataset.u); saveUserSets(); refresh(); return;
    }
  }
  if (t.closest("#btn-reset")) { resetFilters(); return; }
  if (t.closest("#btn-filters")) { openSheet(); return; }
  if (t.closest("#side-close") || t.closest("#side-apply") || t.closest("#side-back")) { closeSheet(); return; }
  if (t.closest("#dback")) { closeDetail(); return; }
  if (t.closest("#btn-theme")) { toggleTheme(); return; }
  if (t.closest("#btn-dens")) { UIP.dense = !UIP.dense; document.body.classList.toggle("dense", UIP.dense); lsSet("hlidac_ui", UIP); return; }
  if (t.closest("#btn-views")) { if ($("pop").dataset.kind === "views" && !$("pop").hidden) popClose(); else popViews(); return; }
  if (t.closest("#btn-keys")) { if ($("pop").dataset.kind === "keys" && !$("pop").hidden) popClose(); else popKeys(); return; }
  if (t.closest("#vsave")) { saveView(); return; }
  if (t.closest("#btn-hid")) { S.hid = S.hid ? 0 : 1; onFilterChange(); return; }
  if (t.closest("#btn-img")) { S.img = !S.img; refresh("list"); return; }
  if (t.closest("#btn-dir")) { S.dir = -(S.dir || SORTS[S.sort].d); page = 0; cur = -1; refresh("sort"); return; }
  if (t.closest("#btn-csv")) { exportCsv(); return; }
  if ((a = t.closest(".row")) && !t.closest("a")) { openDetail(+a.dataset.n, +a.dataset.pos); return; }
}
// v záložce Oblíbené odebrání hvězdičky musí řádek zrušit (nový výběr), jinde stačí překreslit seznam
function afterFavChange() { refresh(S.tab === "fav" ? undefined : "list"); }
function reloadDetail(n) {
  if (detailN !== n) return;
  loadShard(P.L[n].i).then(function (sh) { if (detailN === n) renderDetail(n, sh[P.L[n].i] || {}, "ok"); }).catch(function () { if (detailN === n) renderDetail(n, null, "err"); });
}
function doHide(n) {
  if (n == null || n < 0) return;
  var nowHidden = toggleHide(n), inDetail = detailN === n, l = P.L[n];
  // v detailu přeskočit na další inzerát (jinak by zmizel pod rukama)
  if (inDetail) { var pos = findPos(n); var nextN = (pos >= 0 && pos + 1 < SORTED.length) ? SORTED[pos + 1] : -1; }
  recompute(); computePresetCountsSoon(); refresh("list");
  if (inDetail) { if (nextN >= 0 && !P.hidf[nextN] === !S.hid) openDetail(nextN); else closeDetail(); }
  toast((nowHidden ? "Skryto: " : "Vráceno: ") + (l.l || redact(l.t) || ""), "Zpět", function () { toggleHide(n); recompute(); computePresetCountsSoon(); refresh("list"); });
}
function computePresetCountsSoon() { debounce("pc", function () { computePresetCounts(); renderPresets(); }, 400); }
function resetFilters() { var keep = S.img, tab = S.tab; S = defState(); S.img = keep; S.tab = tab; $("sortsel").value = S.sort; onFilterChange(); }
function exportCsv() {
  if (!SORTED.length) { toast("Není co exportovat"); return; }
  var blob = new Blob(["﻿" + toCSV(P, SORTED)], { type: "text/csv;charset=utf-8" }), a = document.createElement("a");
  a.href = URL.createObjectURL(blob); a.download = "hlidac_" + (P.gen || "data") + "_" + SORTED.length + ".csv";
  document.body.appendChild(a); a.click(); document.body.removeChild(a); setTimeout(function () { URL.revokeObjectURL(a.href); }, 2000);
  toast("Export: " + fmt(SORTED.length) + " řádků (bez kontaktních hodnot)");
}
function inField(el) { return el && (/^(INPUT|TEXTAREA|SELECT)$/.test(el.tagName) || el.isContentEditable); }
function onKey(e) {
  if (e.ctrlKey || e.metaKey || e.altKey) return;
  var k = e.key;
  if (k === "Escape") {
    if (!$("pop").hidden) { popClose(); return; }
    if (detailN >= 0) { closeDetail(); return; }
    if ($("side").classList.contains("open")) { closeSheet(); return; }
    if (inField(document.activeElement)) { document.activeElement.blur(); return; }
    return;
  }
  if (inField(e.target)) return;
  if (k === "Tab" && detailN >= 0) { trapTab(e); return; }
  if (k === "/") { e.preventDefault(); if (S.tab === "trh") setTab("leady"); if (window.innerWidth < 980) openSheet(); var q = $("f-q"); if (q) { var d = q.closest("details"); if (d) d.open = true; q.focus(); q.select(); } return; }
  if (k === "?") { e.preventDefault(); popKeys(); return; }
  if (S.tab === "trh") return;
  if (detailN >= 0) {
    if (k === "ArrowRight" || k === "j") { e.preventDefault(); detailStep(1); return; }
    if (k === "ArrowLeft" || k === "k") { e.preventDefault(); detailStep(-1); return; }
    if (k === "f") { toggleFav(detailN); afterFavChange(); reloadDetail(detailN); return; }
    if (k === "x") { doHide(detailN); return; }
    return;
  }
  if (k === "j") { e.preventDefault(); setCur(cur < 0 ? 0 : cur + 1); return; }
  if (k === "k") { e.preventDefault(); setCur(cur < 0 ? 0 : cur - 1); return; }
  if (k === "Enter") {
    var rf = e.target.closest && e.target.closest(".row");
    if (rf) { e.preventDefault(); openDetail(+rf.dataset.n, +rf.dataset.pos); return; }
    if (/^(BUTTON|A|SUMMARY)$/.test(e.target.tagName)) return;     // nativní chování tlačítek a odkazů nechat být
    var ne = leadAtCur(); if (ne >= 0) { e.preventDefault(); openDetail(ne, cur); }
    return;
  }
  if (k === "f") { var nf = leadAtCur(); if (nf >= 0) { toggleFav(nf); afterFavChange(); } return; }
  if (k === "x") { var nx = leadAtCur(); if (nx >= 0) doHide(nx); return; }
}
function trapTab(e) {
  var f = $("dp").querySelectorAll('button:not([disabled]),a[href],[tabindex="0"]'); if (!f.length) return;
  var first = f[0], last = f[f.length - 1];
  if (!$("dp").contains(document.activeElement)) { e.preventDefault(); first.focus(); return; }
  if (e.shiftKey && document.activeElement === first) { e.preventDefault(); last.focus(); }
  else if (!e.shiftKey && document.activeElement === last) { e.preventDefault(); first.focus(); }
}

/* ---------- patička ---------- */
function renderFoot() {
  var m = P.meta, z = m.zdroje || {};
  $("foot").innerHTML = 'Data z <b>' + esc(fmtDate(m.gen)) + '</b> · <b>' + fmt(P.n) + '</b> aktivních inzerátů · ' +
    Object.keys(z).map(function (s) { return esc(SRC[s] || s) + " " + fmt(z[s]); }).join(" · ") +
    (m.stari_vypocet ? ' · stáří přepočteno ' + esc(fmtDate(m.stari_vypocet)) : "") + ' · soukromí prodejci, bez kontaktních hodnot';
}

/* ---------- start ---------- */
function bootError(e) {
  $("boot").hidden = false;
  $("boot").innerHTML = 'Data se nepodařilo načíst (' + esc(e && e.message ? e.message : e) + '). <br><button type="button" class="btn primary" id="boot-retry">Zkusit znovu</button>';
  $("boot-retry").onclick = function () { $("boot").textContent = "Načítám data…"; boot(); };
}
function boot() {
  fetch("data.json", { cache: "no-cache" }).then(function (r) { if (!r.ok) throw new Error("HTTP " + r.status); return r.json(); })
    .then(function (d) { Dt = d; P = prep(d); start(); }).catch(bootError);
}
function start() {
  $("boot").hidden = true;
  var ui = lsGet("hlidac_ui", null); if (ui && typeof ui === "object") { UIP.open = ui.open || {}; UIP.dense = !!ui.dense; }
  loadUserSets();
  applyHashState();
  // seznam pro řazení
  $("sortsel").innerHTML = Object.keys(SORTS).map(function (k) { return '<option value="' + k + '">' + esc(SORTS[k].l) + '</option>'; }).join("");
  buildFacets(); renderFoot(); bindEvents(); computePresetCounts();
  $("pane-list").hidden = false;
  applyStateToUI();
}
if (typeof document !== "undefined" && document.getElementById("pane-list")) {
  // chyby uvnitř boot() (např. prep) se ukážou uživateli, ne jen v konzoli
  try { boot(); } catch (e) { bootError(e); }
}
