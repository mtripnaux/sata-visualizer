"use strict";

const S = {vars:[], clauses:[], selected:null};

const EXAMPLES = [
  ["Running example (Sec. 4.2)", "(-x | y) & (x | y) & (x | -y) & (-x | -y)"],
  ["Two singleton clauses (Ex. sat-1)", "(-x | y) & (x | -y)"],
  ["x ∧ ¬x unsatisfiable (Sec. 4)", "(x) & (-x)"],
  ["Polarised variant (Sec. 4.1)", "(-x1 | y2) & (y1 | y2) & (y1 | -x2) & (-x1 | -x2)"],
  ["Single ternary clause (Sec. 4.1)", "(-x | y1 | y2)"],
  ["Logic program P (Sec. 5)", "(a) & (-b | d) & (-c | d) & (-c | -d | b)"],
  ["Logic program Q ≡ P (Sec. 5)", "(a) & (-a | -b | d) & (-c | b)"]
];
const DEFAULT_FORMULA = EXAMPLES[0][1];

function parseInput(raw){
  const out = {vars:[], clauses:[], errors:[], notes:[]};
  const text = (raw||"").trim();
  if(!text) return out;
  const looksDimacs = /^\s*p\s+cnf/im.test(text) ||
                      (/^[\s\d+\-cp\n]+$/i.test(text) && /(^|\s)0(\s|$)/.test(text));
  return looksDimacs ? parseDimacs(text, out) : parseFree(text, out);
}

function parseDimacs(text, out){
  const nums = []; let declared = 0;
  for(const line of text.split(/\r?\n/)){
    const t = line.trim();
    if(!t || /^c\b/i.test(t)) continue;
    const p = t.match(/^p\s+cnf\s+(\d+)\s+(\d+)/i);
    if(p){ declared = parseInt(p[1],10); continue; }
    for(const tok of t.split(/\s+/)){
      if(!tok) continue;
      if(!/^-?\d+$/.test(tok)){ out.errors.push("Not a DIMACS token: " + tok); return out; }
      nums.push(parseInt(tok,10));
    }
  }
  let cur = [], maxV = declared;
  for(const v of nums){
    if(v === 0){ out.clauses.push(cur); cur = []; }
    else { cur.push(v); maxV = Math.max(maxV, Math.abs(v)); }
  }
  if(cur.length){ out.clauses.push(cur); out.notes.push("Last clause was not terminated by 0; closed it."); }
  for(let i=1;i<=maxV;i++) out.vars.push("x"+i);
  out.clauses = out.clauses.map(c => c.map(l => ({v:Math.abs(l)-1, neg:l<0})));
  return finish(out);
}

function parseFree(text, out){
  const t = text
    .replace(/¬/g,"-").replace(/~/g,"-").replace(/!/g,"-")
    .replace(/∨/g,"|").replace(/\\\//g,"|")
    .replace(/∧/g,"&").replace(/\/\\/g,"&");
  const index = new Map();
  for(const chunk of t.split(/[&\n]+/).map(s=>s.trim()).filter(Boolean)){
    const inner = chunk.replace(/^\(+/,"").replace(/\)+$/,"").trim();
    const lits = [];
    if(inner.length){
      for(const tok of inner.split(/[|,+\s]+/).filter(Boolean)){
        const m = tok.match(/^(-*)([A-Za-z_][A-Za-z0-9_]*|\d+)$/);
        if(!m){ out.errors.push("Not a literal: " + tok); return out; }
        let name = m[2];
        if(/^\d+$/.test(name)) name = "x" + name;
        if(!index.has(name)){ index.set(name, out.vars.length); out.vars.push(name); }
        lits.push({v:index.get(name), neg:(m[1].length % 2) === 1});
      }
    }
    out.clauses.push(lits);
  }
  return finish(out);
}

function finish(out){
  const vars = out.vars.map(n => ({name:n}));
  const clauses = out.clauses.map(lits => {
    const seen = new Set(), kept = [];
    for(const l of lits){
      const key = l.v + (l.neg ? "-" : "+");
      if(seen.has(key)) continue;
      seen.add(key); kept.push(l);
    }
    return {lits:kept};
  });
  return {vars, clauses, errors:out.errors, notes:out.notes};
}

const R = 3, ROW = 18, COL = 55, PAD = 16, BULGE = 12, BULGE_STEP = 7, RAIL = 5;

function layout(){
  const nV = S.vars.length, nC = S.clauses.length;
  const maxBulge = BULGE + Math.max(nV-1,0)*BULGE_STEP;
  const pad = Math.max(PAD, maxBulge + 4);
  const xNeg = pad, xC = xNeg + COL, xPos = xC + COL;
  const W = xPos + pad;
  const rows = Math.max(nV, nC, 1);
  const bodyH = (rows-1)*ROW;
  const topMargin = 10 + nV*RAIL;
  const top = topMargin + 8;
  const bodyBottom = top + bodyH;
  const H = bodyBottom + 8;
  const rank = i => nV - 1 - i;
  return {nV,nC,xNeg,xC,xPos,W,H,top,
    yV: i => top + (bodyH-(nV-1)*ROW)/2 + i*ROW,
    yC: j => top + (bodyH-(nC-1)*ROW)/2 + j*ROW,
    railY: i => topMargin - 4 - rank(i)*RAIL,
    bulge: i => BULGE + rank(i)*BULGE_STEP};
}

function isWire(c){
  const neg = c.lits.filter(l=>l.neg).length, pos = c.lits.length - neg;
  return neg===1 && pos===1;
}

function varOccurs(i){
  return S.clauses.some(c => c.lits.some(l => l.v===i));
}

function renderEmptySVG(){
  return `<svg class="id0" viewBox="0 0 32 32" xmlns="http://www.w3.org/2000/svg" role="img" aria-label="Empty diagram">`
    + `<rect x="8" y="8" width="16" height="16" fill="none" stroke="#000" stroke-width="0.75" stroke-dasharray="3,3"/>`
    + `</svg>`;
}

function isEditable(){
  for(let i=0;i<S.clauses.length;i++)
    for(let j=i+1;j<S.clauses.length;j++)
      if(findResolution(S.clauses[i], S.clauses[j])!==null) return true;
  return false;
}

function renderSVG(){
  const L = layout();
  const editable = isEditable();
  const p = [`<svg viewBox="0 0 ${L.W} ${L.H}" xmlns="http://www.w3.org/2000/svg" role="img" aria-label="SATA diagram">`];

  S.clauses.forEach((c,j) => {
    const cy = L.yC(j);
    const sel = S.selected===j ? " sel" : "";
    if(isWire(c)){
      const vNeg = c.lits.find(l=>l.neg).v, vPos = c.lits.find(l=>!l.neg).v;
      const vyNeg = L.yV(vNeg), vyPos = L.yV(vPos);
      const d = `M ${L.xNeg+R} ${vyNeg} C ${L.xNeg+24} ${vyNeg}, ${L.xC-24} ${cy}, ${L.xC} ${cy}`
        + ` C ${L.xC+24} ${cy}, ${L.xPos-24} ${vyPos}, ${L.xPos-R} ${vyPos}`;
      p.push(editable
        ? `<g class="clause" data-clause="${j}"><path class="hit" d="${d}"/><path class="wire${sel}" d="${d}"/></g>`
        : `<path class="wire${sel}" d="${d}"/>`);
      return;
    }
    c.lits.forEach(l => {
      const vy = L.yV(l.v);
      const d = l.neg
        ? `M ${L.xNeg+R} ${vy} C ${L.xNeg+24} ${vy}, ${L.xC-24} ${cy}, ${L.xC-R} ${cy}`
        : `M ${L.xC+R} ${cy} C ${L.xC+24} ${cy}, ${L.xPos-24} ${vy}, ${L.xPos-R} ${vy}`;
      p.push(`<path class="wire" d="${d}"/>`);
    });
  });

  S.vars.forEach((v,i) => {
    if(!varOccurs(i)) return;
    const y = L.yV(i), rail = L.railY(i), bg = L.bulge(i);
    const loop = `M ${L.xNeg-R} ${y} C ${L.xNeg-bg} ${y}, ${L.xNeg-bg} ${rail}, ${L.xNeg-2} ${rail}`
      + ` L ${L.xPos+2} ${rail} C ${L.xPos+bg} ${rail}, ${L.xPos+bg} ${y}, ${L.xPos+R} ${y}`;
    p.push(`<path class="wire" d="${loop}"/>`);
    p.push(`<circle class="bnode" cx="${L.xNeg}" cy="${y}" r="${R}"/>`);
    p.push(`<circle class="bnode" cx="${L.xPos}" cy="${y}" r="${R}"/>`);
  });

  S.clauses.forEach((c,j) => {
    if(isWire(c)) return;
    const sel = S.selected===j ? " sel" : "";
    p.push(editable
      ? `<g class="clause" data-clause="${j}"><circle class="hit" cx="${L.xC}" cy="${L.yC(j)}" r="8"/><circle class="wnode${sel}" cx="${L.xC}" cy="${L.yC(j)}" r="${R}"/></g>`
      : `<circle class="wnode${sel}" cx="${L.xC}" cy="${L.yC(j)}" r="${R}"/>`);
  });

  p.push(`</svg>`);
  return p.join("");
}

function dimacs(){
  const l = [`p cnf ${S.vars.length} ${S.clauses.length}`];
  S.clauses.forEach(c => l.push((c.lits.map(x => (x.neg?"-":"") + (x.v+1)).join(" ") + " 0").trim()));
  return l.join("\n");
}

function tikz(){
  if(!S.clauses.length) return "";
  const L = layout(), SX = 33, SY = 33;
  const x = v => (v/SX).toFixed(3), y = v => (-v/SY).toFixed(3);
  const o = [];
  o.push("\\documentclass[tikz,border=4pt]{standalone}");
  o.push("\\begin{document}");
  o.push("\\tikzstyle{black dot}=[fill=black, draw=black, shape=circle, scale=0.3]");
  o.push("\\tikzstyle{empty dot}=[fill=none, draw=black, shape=circle, scale=0.3]");
  o.push("\\begin{tikzpicture}[line width=.4pt]");
  S.vars.forEach((v,i) => {
    const vy = L.yV(i), rail = L.railY(i), bg = L.bulge(i);
    o.push(`  \\node[black dot] (n${i}) at (${x(L.xNeg)},${y(vy)}) {};`);
    o.push(`  \\node[black dot] (p${i}) at (${x(L.xPos)},${y(vy)}) {};`);
    o.push(`  \\coordinate (rl${i}) at (${x(L.xNeg-bg)},${y(rail)});`);
    o.push(`  \\coordinate (rr${i}) at (${x(L.xPos+bg)},${y(rail)});`);
  });
  S.clauses.forEach((c,j) => { if(!isWire(c)) o.push(`  \\node[empty dot] (c${j}) at (${x(L.xC)},${y(L.yC(j))}) {};`); });
  S.clauses.forEach((c,j) => {
    if(isWire(c)){
      const vNeg = c.lits.find(l=>l.neg).v, vPos = c.lits.find(l=>!l.neg).v;
      o.push(`  \\draw (n${vNeg}) to[out=0,in=180] (p${vPos});`);
      return;
    }
    c.lits.forEach(l => o.push(l.neg
      ? `  \\draw (n${l.v}) to[out=0,in=180] (c${j});`
      : `  \\draw (c${j}) to[out=0,in=180] (p${l.v});`));
  });
  S.vars.forEach((v,i) => o.push(
    `  \\draw (n${i}) to[out=180,in=180] (rl${i}) -- (rr${i}) to[out=0,in=0] (p${i});`
  ));
  o.push("\\end{tikzpicture}");
  o.push("\\end{document}");
  return o.join("\n");
}

let codeMode = "dimacs";

function draw(){
  document.getElementById("figure").innerHTML = S.clauses.length
    ? renderSVG()
    : renderEmptySVG();
  document.getElementById("diagramTitle").textContent = isEditable() ? "Diagram (click two clauses to resolve)" : "Diagram";
  document.getElementById("codeTitle").textContent = codeMode === "latex" ? "LaTeX" : "DIMACS";
  document.getElementById("code").textContent = codeMode === "latex" ? tikz() : dimacs();
}

let toastTimer = null;
function note(t){
  const el = document.getElementById("toast");
  clearTimeout(toastTimer);
  if(!t){ el.classList.remove("show"); return; }
  el.textContent = t;
  el.classList.add("show");
  toastTimer = setTimeout(() => el.classList.remove("show"), 4000);
}

const src = document.getElementById("src");

function reload(){
  const r = parseInput(src.value);
  S.vars = r.vars; S.clauses = r.clauses;
  S.selected = null;
  note(r.errors.concat(r.notes).join(" "));
  draw();
}

let t = null;
src.addEventListener("input", () => { clearTimeout(t); t = setTimeout(reload, 180); });

function findResolution(a, b){
  for(const la of a.lits) for(const lb of b.lits)
    if(la.v===lb.v && la.neg!==lb.neg) return la.v;
  return null;
}

function resolveClauses(i, j){
  const a = S.clauses[i], b = S.clauses[j];
  S.selected = null;
  const v = findResolution(a, b);
  if(v===null){ note("These two clauses share no complementary variable."); draw(); return; }
  const merged = a.lits.filter(l=>l.v!==v).concat(b.lits.filter(l=>l.v!==v));
  const seen = new Set(), kept = [];
  for(const l of merged){
    const key = l.v+(l.neg?"-":"+");
    if(seen.has(key)) continue;
    seen.add(key); kept.push(l);
  }
  const tautology = kept.some(l => kept.some(m => m.v===l.v && m.neg!==l.neg));
  const rest = S.clauses.filter((_,k) => k!==i && k!==j);
  if(tautology) S.clauses = rest;
  else if(kept.length===0) S.clauses = rest.concat([{lits:[]}]);
  else S.clauses = rest.concat([{lits:kept}]);
  note("");
  draw();
}

document.getElementById("figure").addEventListener("click", e => {
  const el = e.target.closest("[data-clause]");
  if(!el) return;
  const j = +el.dataset.clause;
  if(S.selected===null){ S.selected = j; draw(); return; }
  if(S.selected===j){ S.selected = null; draw(); return; }
  resolveClauses(S.selected, j);
});

document.getElementById("resetProof").addEventListener("click", reload);

document.getElementById("examples").innerHTML =
  EXAMPLES.map((e,i) => `<button data-ex="${i}">${e[0]}</button>`).join("");
document.getElementById("examples").addEventListener("click", e => {
  const b = e.target.closest("[data-ex]"); if(!b) return;
  src.value = EXAMPLES[+b.dataset.ex][1];
  reload();
});

document.getElementById("toggleCode").addEventListener("click", e => {
  codeMode = codeMode === "latex" ? "dimacs" : "latex";
  e.target.textContent = codeMode === "latex" ? "Show DIMACS" : "Show LaTeX";
  draw();
});

src.value = DEFAULT_FORMULA;
reload();
