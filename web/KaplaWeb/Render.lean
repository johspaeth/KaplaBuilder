import KaplaCore

/-!
# KaplaWeb.Render — the Lean-generated webpage

One self-contained HTML file: a three.js 3D view (pinned CDN version) with a step slider,
step cards with a top-down plan of the current layer, mm offsets, angles, grip and approach
hints, a "two hands" badge, and the verified report. Print stylesheet = build booklet.

The page never claims more than the physics report's `Guarantees`.
-/

namespace Kapla.Web

open Kapla Lean

def escape (s : String) : String :=
  s.foldl (fun acc c => acc ++ match c with
    | '<' => "&lt;" | '>' => "&gt;" | '&' => "&amp;" | '"' => "&quot;" | '\'' => "&#39;"
    | c => c.toString) ""

/-- JSON safe to embed inside `<script>`. -/
def scriptJson (j : Json) : String :=
  (j.compress.replace "</" "<\\/").replace "<!--" "<\\!--"

def fmt1 (x : Float) : String :=
  let r := (x * 10).round / 10
  let s := toString r
  -- trim trailing zeros of Float's default formatting
  match s.splitOn "." with
  | [a, b] => let b := String.ofList (b.toList.take 1); if b == "0" then a else a ++ "." ++ b
  | _ => s

def pct (q : Q) : String := fmt1 (q.toFloat * 100) ++ "%"

def gripText : Grip → String
  | .longSides => "hold at the long sides"
  | .shortEnds => "hold at the short ends"
  | .topEnd => "hold at the top end"

def approachText : Approach → String
  | .fromAbove => "lower from above"
  | .slideXPos => "slide in along +x"
  | .slideXNeg => "slide in along −x"
  | .slideYPos => "slide in along +y"
  | .slideYNeg => "slide in along −y"

def uprightText : Upright → String
  | .flat => "flat" | .edge => "on edge" | .upright => "upright"

/-- Display data for one block (floats; the exact plan is in the JSON download). -/
def blockJson (step : Nat) (b : Pose) : Json :=
  let h := b.half
  Json.mkObj [
    ("step", step), ("up", uprightText b.up),
    ("c", toJson b.center.toFloats),
    ("size", toJson #[(2 * h.x).toFloat, (2 * h.y).toFloat, (2 * h.z).toFloat]),
    ("yaw", toJson (b.rot.toDeg)),
    ("fp", toJson (b.footprint.map fun p => #[p.x.toFloat, p.y.toFloat])),
    ("bottom", toJson b.bottomZ.toFloat)]

def pageData (i : RenderInput) : Json :=
  let plan := i.candidate.plan
  let blocks := (plan.steps.zipIdx.flatMap fun (s, k) => s.blocks.map (blockJson k))
  let steps := plan.steps.map fun s => Json.mkObj [
    ("phase", s.phase), ("n", s.blocks.length),
    ("grip", gripText s.grip), ("approach", approachText s.approach)]
  Json.mkObj [("blocks", Json.arr blocks.toArray), ("steps", Json.arr steps.toArray)]

def difficultyText : Difficulty → String
  | .easy => "easy" | .medium => "medium" | .expert => "expert"

def check (b : Bool) (label : String) : String :=
  if b then s!"<li class=\"yes\"><span class=\"mark\">✓</span>{label}</li>"
  else s!"<li class=\"no\"><span class=\"mark\">–</span>{label} <em>(not checked yet)</em></li>"

def reportHtml (i : RenderInput) : String :=
  let c := i.candidate
  let ph := c.physics
  let g := ph.guarantees
  let status :=
    if ph.ok && ph.verified then "<span class=\"badge ok\">verified: stands at every step</span>"
    else if ph.ok then "<span class=\"badge warn\">accepted by an unverified checker</span>"
    else "<span class=\"badge bad\">rejected by the physics checker</span>"
  let diags := if ph.diagnostics.isEmpty then "" else
    "<h3>Problems</h3><ul>" ++ String.join (ph.diagnostics.map fun d =>
      s!"<li>{escape d.describe}</li>") ++ "</ul>"
  let parts := if c.score.perPart.isEmpty then "" else
    "<h3>Parts</h3><table><tr><th>part</th><th>covered</th></tr>" ++
    String.join (c.score.perPart.map fun p =>
      s!"<tr><td>{escape p.tag}</td><td>{pct p.iou}</td></tr>") ++ "</table>"
  s!"<section class=\"report\">
  <div class=\"badges\">{status}
    <span class=\"badge\">{c.plan.blockCount} / {i.request.blocks} blocks</span>
    <span class=\"badge\">likeness {pct c.score.score} · {Verdict.describe (Verdict.ofScore c.score.score)}</span>
    <span class=\"badge\">ceiling {pct i.bound.maxScore}</span>
    <span class=\"badge\">difficulty: {difficultyText c.difficulty}</span>
  </div>
  <h3>What the checker guarantees <small>(engine: {escape ph.engine})</small></h3>
  <ul class=\"guarantees\">
    {check g.equilibriumEveryStep "stands after every build step (H3)"}
    {check g.nonOverlap "no two blocks overlap"}
    {check g.handsPerStep s!"at most {i.human.hands} blocks per step (H7)"}
    {check g.robust s!"stands, also under the press, if each block is off by up to {fmt1 i.human.epsRel.toFloat} mm against the block it is lined up with and {fmt1 i.human.eAbs.toFloat} mm overall (H1, H2; sideways shifts — twists not yet covered)"}
    {check g.press "survives pressing the new block down (H4)"}
    {check g.reachable "every block reachable by hand (H5)"}
    {check g.clearance "no tight gaps (H6)"}
    {check g.parallelSupports "even parallel supports (H8)"}
  </ul>
  {diags}
  <p class=\"meta\">Motif: {escape c.motif} · scale {fmt1 c.target.unitMM.toFloat} mm/unit ·
    target {c.score.targetVoxels} voxels, {c.score.missing} missing, {c.score.extra} extra</p>
  {parts}
</section>"

def css : String := "
:root{--bg:#faf7f2;--fg:#2b2420;--muted:#7a6f66;--card:#fff;--line:#e5ddd2;--accent:#c8742c;
--ok:#2e7d4f;--bad:#b3392f;--warn:#a6761d;--wood:#e2b47a;--wood2:#c99558}
@media (prefers-color-scheme:dark){:root:not([data-theme=light]){--bg:#1d1a17;--fg:#efe7dd;
--muted:#a39587;--card:#28231f;--line:#3b342e;--accent:#e39a52;--ok:#6cc08b;--bad:#ef7d72;--warn:#e0b45c}}
:root[data-theme=dark]{--bg:#1d1a17;--fg:#efe7dd;--muted:#a39587;--card:#28231f;--line:#3b342e;
--accent:#e39a52;--ok:#6cc08b;--bad:#ef7d72;--warn:#e0b45c}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--fg);
font:15px/1.5 system-ui,-apple-system,Segoe UI,sans-serif}
header,main{max-width:1100px;margin:0 auto;padding:16px}
h1{font-size:1.6rem;margin:.2em 0}h3{margin:1.2em 0 .4em}.sub{color:var(--muted)}
.badges{display:flex;flex-wrap:wrap;gap:8px;margin:8px 0}
.badge{border:1px solid var(--line);border-radius:999px;padding:3px 10px;background:var(--card);font-size:.85rem}
.badge.ok{border-color:var(--ok);color:var(--ok);font-weight:600}
.badge.bad{border-color:var(--bad);color:var(--bad);font-weight:600}
.badge.warn{border-color:var(--warn);color:var(--warn);font-weight:600}
.guarantees{list-style:none;padding:0}.guarantees li{margin:2px 0}
.mark{display:inline-block;width:1.4em;font-weight:700}.yes .mark{color:var(--ok)}.no{color:var(--muted)}
#view{width:100%;height:min(60vh,520px);border:1px solid var(--line);border-radius:10px;background:var(--card);touch-action:none}
.controls{display:flex;gap:10px;align-items:center;margin:10px 0;flex-wrap:wrap}
.controls input[type=range]{flex:1;min-width:160px}
button{font:inherit;border:1px solid var(--line);background:var(--card);color:var(--fg);border-radius:8px;padding:4px 12px;cursor:pointer}
#cards{display:grid;grid-template-columns:repeat(auto-fill,minmax(250px,1fr));gap:12px}
.card{background:var(--card);border:1px solid var(--line);border-radius:10px;padding:10px;break-inside:avoid}
.card h4{margin:0 0 4px}.card .hint{color:var(--muted);font-size:.85rem}
.card svg{width:100%;height:auto;display:block;margin:6px 0}
.two{color:var(--accent);font-weight:700}
table{border-collapse:collapse}td,th{border-bottom:1px solid var(--line);padding:2px 10px;text-align:left}
.meta{color:var(--muted);font-size:.85rem}
@media print{#view,.controls,.noprint{display:none}body{background:#fff;color:#000}
#cards{grid-template-columns:repeat(2,1fr)}}
"

/-- Client-side script: 3D view and step cards. Uses globals `THREE` and `DATA`. -/
def js : String := "
const D = DATA, B = D.blocks, S = D.steps;
const css = n => getComputedStyle(document.documentElement).getPropertyValue(n).trim();
// ---------- step cards (top-down plan of the current layer) ----------
function card(k){
  const nb = B.filter(b => b.step === k), z = nb.length ? nb[0].bottom : 0;
  const same = B.filter(b => b.step < k && Math.abs(b.bottom - z) < 1e-6);
  const below = B.filter(b => b.step < k && b.bottom < z - 1e-6 && b.bottom + b.size[2] > z - 1e-3 - 0.5 && Math.abs(b.bottom + b.size[2] - z) < 1e-3);
  const all = B.filter(b => b.step <= k);
  let xs=[],ys=[]; all.forEach(b=>b.fp.forEach(p=>{xs.push(p[0]);ys.push(p[1]);}));
  const pad=10, x0=Math.min(...xs)-pad, x1=Math.max(...xs)+pad, y0=Math.min(...ys)-pad, y1=Math.max(...ys)+pad;
  const poly=(b,cls)=>`<polygon class='${cls}' points='${b.fp.map(p=>`${p[0]},${-p[1]}`).join(' ')}'/>`;
  const svg=`<svg viewBox='${x0} ${-y1} ${x1-x0} ${y1-y0}'><style>.f{fill:none;stroke:var(--line);stroke-width:1}
   .b{fill:var(--wood);fill-opacity:.35;stroke:var(--wood2);stroke-width:1}.s{fill:var(--wood);stroke:var(--wood2);stroke-width:1.2}
   .n{fill:var(--accent);stroke:var(--fg);stroke-width:1.5}</style>
   ${all.filter(b=>!below.includes(b)&&!same.includes(b)&&!nb.includes(b)).map(b=>poly(b,'f')).join('')}
   ${below.map(b=>poly(b,'b')).join('')}${same.map(b=>poly(b,'s')).join('')}${nb.map(b=>poly(b,'n')).join('')}
   <circle cx='0' cy='0' r='2.5' fill='var(--muted)'/></svg>`;
  const s=S[k], lines=nb.map(b=>`${b.up}, centre (${b.c[0].toFixed(1)}, ${b.c[1].toFixed(1)}) mm, height ${b.bottom.toFixed(1)} mm, turned ${(((b.yaw%180)+180)%180).toFixed(1)}°`).join('<br>');
  return `<div class='card' id='step${k}'><h4>Step ${k+1} <span class='hint'>· ${s.phase}</span>${s.n>1?\" <span class='two'>✋✋ two hands</span>\":''}</h4>
   ${svg}<div>${lines}</div><div class='hint'>${s.grip}, ${s.approach}. Offsets are from the dot (origin).</div></div>`;
}
document.getElementById('cards').innerHTML = S.map((_,k)=>card(k)).join('');
// ---------- 3D view ----------
const el = document.getElementById('view'), slider = document.getElementById('slider'), label = document.getElementById('label');
slider.max = S.length; slider.value = S.length;
let render = () => {};
if (window.THREE) {
  const scene = new THREE.Scene(), cam = new THREE.PerspectiveCamera(40, 1, 1, 20000);
  const ren = new THREE.WebGLRenderer({antialias:true, alpha:true}); el.appendChild(ren.domElement);
  scene.add(new THREE.HemisphereLight(0xffffff, 0x887766, 0.9));
  const sun = new THREE.DirectionalLight(0xffffff, 0.6); sun.position.set(300,-400,800); scene.add(sun);
  const ground = new THREE.Mesh(new THREE.CircleGeometry(2000, 64), new THREE.MeshLambertMaterial({color:0x998877, transparent:true, opacity:.15}));
  scene.add(ground);
  const wood = new THREE.MeshLambertMaterial({color:0xe2b47a}), hot = new THREE.MeshLambertMaterial({color:0xe07b2a});
  const edges = new THREE.LineBasicMaterial({color:0x6b4a2b, transparent:true, opacity:.5});
  const meshes = B.map(b => { const g = new THREE.BoxGeometry(b.size[0], b.size[1], b.size[2]);
    const m = new THREE.Mesh(g, wood); m.position.set(b.c[0], b.c[1], b.c[2]); m.rotation.z = b.yaw*Math.PI/180;
    m.add(new THREE.LineSegments(new THREE.EdgesGeometry(g), edges)); scene.add(m); return m; });
  let xs=B.map(b=>b.c[0]), ys=B.map(b=>b.c[1]), zs=B.map(b=>b.c[2]+b.size[2]/2);
  const cx=(Math.min(...xs)+Math.max(...xs))/2||0, cy=(Math.min(...ys)+Math.max(...ys))/2||0, top=Math.max(...zs,120);
  const span=Math.max(Math.max(...xs)-Math.min(...xs), Math.max(...ys)-Math.min(...ys), top, 150);
  cam.up.set(0,0,1);
  const ctl = THREE.OrbitControls ? new THREE.OrbitControls(cam, ren.domElement) : null;
  cam.position.set(cx+span*1.3, cy-span*1.6, top*0.6+span*0.9);
  if (ctl) { ctl.target.set(cx, cy, top/3); ctl.update(); ctl.addEventListener('change', ()=>render()); } else cam.lookAt(cx, cy, top/3);
  render = () => { const k = +slider.value;
    meshes.forEach((m,i)=>{ m.visible = B[i].step < k; m.material = (B[i].step === k-1) ? hot : wood; });
    ren.render(scene, cam); };
  const resize = () => { const w = el.clientWidth, h = el.clientHeight; ren.setSize(w, h); cam.aspect = w/h; cam.updateProjectionMatrix(); render(); };
  window.addEventListener('resize', resize); resize();
} else { el.innerHTML = \"<p style='padding:1em'>3D view unavailable (three.js could not be loaded). The step cards below are complete.</p>\"; }
const update = () => { const k=+slider.value; label.textContent = k===0 ? 'empty' : `after step ${k} of ${S.length}`; render(); };
slider.addEventListener('input', update);
document.getElementById('prev').onclick = () => { slider.value = Math.max(0, +slider.value-1); update(); };
document.getElementById('next').onclick = () => { slider.value = Math.min(S.length, +slider.value+1); update(); };
update();
"

/-- The whole page. -/
def render (i : RenderInput) : String :=
  let title := s!"Kapla: {i.candidate.target.name}"
  s!"<!doctype html>
<html lang=\"en\"><head><meta charset=\"utf-8\"><meta name=\"viewport\" content=\"width=device-width,initial-scale=1\">
<title>{escape title}</title><style>{css}</style>
<script src=\"https://cdn.jsdelivr.net/npm/three@0.128.0/build/three.min.js\"></script>
<script src=\"https://cdn.jsdelivr.net/npm/three@0.128.0/examples/js/controls/OrbitControls.js\"></script>
</head><body>
<header><h1>{escape i.candidate.target.name}</h1>
<div class=\"sub\">“{escape i.request.prompt}” · {i.request.blocks} blocks · profile {escape i.request.profile}</div></header>
<main>
{reportHtml i}
<h3 class=\"noprint\">Build it</h3>
<div id=\"view\"></div>
<div class=\"controls\"><button id=\"prev\">◀</button><input id=\"slider\" type=\"range\" min=\"0\" step=\"1\">
<button id=\"next\">▶</button><span id=\"label\"></span>
<button class=\"noprint\" onclick=\"window.print()\">Print booklet</button></div>
<h3>Steps</h3><div id=\"cards\"></div>
</main>
<script>const DATA = {scriptJson (pageData i)};</script>
<script>{js}</script>
</body></html>"

def renderer : Renderer where
  name := "web-v1"
  render := render

end Kapla.Web
