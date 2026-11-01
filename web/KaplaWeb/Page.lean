import KaplaWeb.Blueprint

/-! # The blueprint page

One self-contained HTML file: a 3D view with a step slider (three.js, pinned version from a
CDN), one card per step with a top-down plan of the current layer, and a print layout that
turns the cards into a build booklet. If three.js cannot load, the cards still work.
-/

namespace KaplaWeb

open Lean

/-- Escape text for HTML. -/
def escape (s : String) : String :=
  s.foldl (fun acc c => acc ++ match c with
    | '<' => "&lt;" | '>' => "&gt;" | '&' => "&amp;" | '"' => "&quot;" | '\'' => "&#39;"
    | c => c.toString) ""

#guard escape "<a href=\"x\">&</a>" == "&lt;a href=&quot;x&quot;&gt;&amp;&lt;/a&gt;"

/-- JSON that is safe to put inside a `<script>` element. -/
def scriptJson (j : Json) : String :=
  (j.compress.replace "</" "<\\/").replace "<!--" "<\\!--"

-- a "</script>" inside the data cannot end the script element early
#guard ((scriptJson (Json.str "</script>")).splitOn "</").length == 1

/-- Builder hint for a grip name from the blueprint. -/
def gripText : String → String
  | "longSides" => "hold at the long sides"
  | "shortEnds" => "hold at the short ends"
  | "topEnd" => "hold at the top end"
  | "" => "hold at the long sides"
  | g => g

/-- Builder hint for an approach name from the blueprint. -/
def approachText : String → String
  | "fromAbove" => "lower from above"
  | "slideXPos" => "slide in along +x"
  | "slideXNeg" => "slide in along −x"
  | "slideYPos" => "slide in along +y"
  | "slideYNeg" => "slide in along −y"
  | "" => "lower from above"
  | a => a

private def fnum (x : Float) : Json := match JsonNumber.fromFloat? x with
  | .inr n => .num n
  | .inl _ => .null

/-- Display data for one block. -/
def blockJson (step : Nat) (b : ViewBlock) : Json :=
  let (sx, sy, sz) := b.size
  Json.mkObj [
    ("step", step), ("up", b.up),
    ("c", Json.arr #[fnum b.x, fnum b.y, fnum b.z]),
    ("size", Json.arr #[fnum sx, fnum sy, fnum sz]),
    ("yaw", fnum b.yawDeg),
    ("fp", Json.arr (b.footprint.map fun (x, y) => Json.arr #[fnum x, fnum y]).toArray),
    ("bottom", fnum b.bottom)]

/-- Everything the page script needs. -/
def pageData (p : ViewPlan) : Json :=
  let blocks := p.steps.zipIdx.flatMap fun (s, k) => s.blocks.map (blockJson k)
  let steps := p.steps.map fun s => Json.mkObj [
    ("phase", s.phase), ("n", s.blocks.length),
    ("grip", gripText s.grip), ("approach", approachText s.approach)]
  let bubbles := p.bubbles.map fun b => Json.mkObj [("label", b.label),
    ("c", Json.arr #[fnum b.x, fnum b.y, fnum b.z]), ("r", Json.arr #[fnum b.rx, fnum b.ry, fnum b.rz])]
  Json.mkObj [("blocks", Json.arr blocks.toArray), ("steps", Json.arr steps.toArray),
    ("bubbles", Json.arr bubbles.toArray)]

/-- Page style (light and dark). -/
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
.notes{margin:6px 0;padding-left:1.2em;color:var(--muted)}
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
#error{border:1px solid var(--bad);color:var(--bad);border-radius:8px;padding:8px 12px;margin:0 0 10px;font-weight:600}
#info{margin:10px 0}#info ul{list-style:none;margin:4px 0;padding:0}
#info li{display:flex;gap:8px;align-items:center}
.swatch{width:12px;height:12px;border-radius:50%;flex:none}
@media print{#view,.controls,.noprint{display:none}body{background:#fff;color:#000}
#cards{grid-template-columns:repeat(2,1fr)}}
"

def js : String := "
const D = DATA, B = D.blocks, S = D.steps, U = D.bubbles || [];
const css = n => getComputedStyle(document.documentElement).getPropertyValue(n).trim();
// ---------- step cards (top-down plan of the current layer) ----------
function card(k){
  const nb = B.filter(b => b.step === k), z = nb.length ? nb[0].bottom : 0;
  const same = B.filter(b => b.step < k && Math.abs(b.bottom - z) < 1e-6);
  const below = B.filter(b => b.step < k && b.bottom < z - 1e-6 && b.bottom + b.size[2] > z - 1e-3 - 0.1 && Math.abs(b.bottom + b.size[2] - z) < 1e-3);
  const all = B.filter(b => b.step <= k);
  let xs=[],ys=[]; all.forEach(b=>b.fp.forEach(p=>{xs.push(p[0]);ys.push(p[1]);}));
  const pad=1.5, x0=Math.min(...xs)-pad, x1=Math.max(...xs)+pad, y0=Math.min(...ys)-pad, y1=Math.max(...ys)+pad;
  const poly=(b,cls)=>`<polygon class='${cls}' points='${b.fp.map(p=>`${p[0]},${-p[1]}`).join(' ')}'/>`;
  const svg=`<svg viewBox='${x0} ${-y1} ${x1-x0} ${y1-y0}'><style>.f{fill:none;stroke:var(--line);stroke-width:.15}
   .b{fill:var(--wood);fill-opacity:.35;stroke:var(--wood2);stroke-width:.15}.s{fill:var(--wood);stroke:var(--wood2);stroke-width:.18}
   .n{fill:var(--accent);stroke:var(--fg);stroke-width:.2}</style>
   ${all.filter(b=>!below.includes(b)&&!same.includes(b)&&!nb.includes(b)).map(b=>poly(b,'f')).join('')}
   ${below.map(b=>poly(b,'b')).join('')}${same.map(b=>poly(b,'s')).join('')}${nb.map(b=>poly(b,'n')).join('')}
   <circle cx='0' cy='0' r='.35' fill='var(--muted)'/></svg>`;
  const s=S[k], lines=nb.map(b=>`${b.up}, centre (${b.c[0].toFixed(1)}, ${b.c[1].toFixed(1)}), height ${b.bottom.toFixed(1)}, turned ${(((b.yaw%180)+180)%180).toFixed(1)}°`).join('<br>');
  return `<div class='card' id='step${k}'><h4>Step ${k+1} <span class='hint'>· ${s.phase}</span>${s.n>1?\" <span class='two'>✋✋ two hands</span>\":''}</h4>
   ${svg}<div>${lines}</div><div class='hint'>${s.grip}, ${s.approach}. Offsets are from the dot (origin).</div></div>`;
}
document.getElementById('cards').innerHTML = S.map((_,k)=>card(k)).join('');
// ---------- 3D view ----------
const el = document.getElementById('view'), slider = document.getElementById('slider'), label = document.getElementById('label');
slider.max = S.length; slider.value = S.length;
let render = () => {}, drawBubbles = () => {};
const COLORS = ['#5b8fd9','#d9705b','#4fa66b','#a66bd9','#d9a93f','#3fb0b8','#d95b9c','#7f8c4f'];
// the part of a bubble above the ground (z = 0): its size and where it reaches
const aboveGround = u => { const [cx,cy,cz] = u.c, [a,b,c] = u.r, f = cz < 0 ? Math.sqrt(Math.max(0, 1-(cz/c)*(cz/c))) : 1;
  return {x:2*a*f, y:2*b*f, z:Math.min(2*c, cz+c), x0:cx-a*f, x1:cx+a*f, y0:cy-b*f, y1:cy+b*f, top:cz+c}; };
if (window.THREE) {
  const scene = new THREE.Scene(), cam = new THREE.PerspectiveCamera(40, 1, 0.1, 2500);
  const ren = new THREE.WebGLRenderer({antialias:true, alpha:true}); el.appendChild(ren.domElement);
  scene.add(new THREE.HemisphereLight(0xffffff, 0x887766, 0.9));
  const sun = new THREE.DirectionalLight(0xffffff, 0.6); sun.position.set(40,-50,100); scene.add(sun);
  const ground = new THREE.Mesh(new THREE.PlaneGeometry(1, 1), new THREE.MeshLambertMaterial({color:0x998877, transparent:true, opacity:.25, depthWrite:false, side:THREE.DoubleSide}));
  scene.add(ground);
  const wood = new THREE.MeshLambertMaterial({color:0xe2b47a}), hot = new THREE.MeshLambertMaterial({color:0xe07b2a});
  const edges = new THREE.LineBasicMaterial({color:0x6b4a2b, transparent:true, opacity:.5});
  const meshes = B.map(b => { const g = new THREE.BoxGeometry(b.size[0], b.size[1], b.size[2]);
    const m = new THREE.Mesh(g, wood); m.position.set(b.c[0], b.c[1], b.c[2]); m.rotation.z = b.yaw*Math.PI/180;
    m.add(new THREE.LineSegments(new THREE.EdgesGeometry(g), edges)); scene.add(m); return m; });
  // the target's bubbles: see-through ellipsoids, cut off at the ground (z = 0)
  ren.localClippingEnabled = true;
  const clip = [new THREE.Plane(new THREE.Vector3(0,0,1), 0)];
  const skinShape = new THREE.SphereGeometry(1, 40, 24), wireShape = new THREE.WireframeGeometry(new THREE.SphereGeometry(1, 16, 10));
  let bubbles = [], shown = [], bubblesOn = true, ruler = null, unit = 'blocks';
  const tog = document.getElementById('bubbles');
  tog.onclick = () => { bubblesOn = !bubblesOn; bubbles.forEach(m => m.visible = bubblesOn);
    tog.textContent = bubblesOn ? 'Hide bubbles' : 'Show bubbles'; render(); };
  cam.up.set(0,0,1);
  const ctl = THREE.OrbitControls ? new THREE.OrbitControls(cam, ren.domElement) : null;
  // the view can turn all the way round, but it cannot go under the ground
  if (ctl) { ctl.maxPolarAngle = Math.PI/2 - 0.01; ctl.addEventListener('change', ()=>render()); }
  // ---------- ground and axes, with numbers in real units ----------
  const label = (txt, x, y, z, h) => { const c = document.createElement('canvas'), g = c.getContext('2d'), font = \"48px system-ui,sans-serif\";
    g.font = font; c.width = Math.ceil(g.measureText(txt).width)+8; c.height = 64; g.font = font;
    g.fillStyle = css('--fg'); g.textAlign = 'center'; g.textBaseline = 'middle'; g.fillText(txt, c.width/2, 32);
    const s = new THREE.Sprite(new THREE.SpriteMaterial({map:new THREE.CanvasTexture(c), transparent:true, depthTest:false}));
    s.position.set(x, y, z); s.scale.set(h*c.width/64, h, 1); s.renderOrder = 2; return s; };
  const niceStep = raw => { const p = Math.pow(10, Math.floor(Math.log10(raw)));
    return [1,2,5,10].map(n => n*p).find(v => v >= raw*(1-1e-9)); };
  const num = v => String(+v.toFixed(6));
  const drawRuler = (x0, x1, y0, y1, top) => {
    if (ruler) { scene.remove(ruler); ruler.traverse(o => { if (o.geometry) o.geometry.dispose();
      if (o.material) { if (o.material.map) o.material.map.dispose(); o.material.dispose(); } }); }
    ruler = new THREE.Group();
    const size = Math.max(x1-x0, y1-y0, top), step = niceStep(size/5), h = size/22;
    const ix0 = Math.floor(x0/step+1e-9), ix1 = Math.ceil(x1/step-1e-9), iy0 = Math.floor(y0/step+1e-9), iy1 = Math.ceil(y1/step-1e-9), iz1 = Math.max(1, Math.ceil(top/step-1e-9));
    const X0 = ix0*step, X1 = ix1*step, Y0 = iy0*step, Y1 = iy1*step, pts = [];
    for (let i = ix0; i <= ix1; i++) { pts.push(i*step,Y0,0, i*step,Y1,0); ruler.add(label(num(i*step), i*step, Y0-h*1.2, 0, h)); }
    for (let j = iy0; j <= iy1; j++) { pts.push(X0,j*step,0, X1,j*step,0); ruler.add(label(num(j*step), X0-h*1.5, j*step, 0, h)); }
    pts.push(X0,Y0,0, X0,Y0,iz1*step);
    for (let k = 0; k <= iz1; k++) { pts.push(X0-h/3,Y0,k*step, X0+h/3,Y0,k*step); if (k) ruler.add(label(num(k*step), X0-h*1.5, Y0, k*step, h)); }
    ruler.add(label('x ('+unit+')', X1+h*2.5, Y0-h*1.2, 0, h), label('y ('+unit+')', X0-h*1.5, Y1+h*3.5, 0, h), label('z ('+unit+')', X0, Y0, iz1*step+h*1.3, h));
    const g = new THREE.BufferGeometry(); g.setAttribute('position', new THREE.Float32BufferAttribute(pts, 3));
    ruler.add(new THREE.LineSegments(g, new THREE.LineBasicMaterial({color:css('--muted'), transparent:true, opacity:.55})));
    scene.add(ruler);
    ground.scale.set(X1-X0+2*step, Y1-Y0+2*step, 1); ground.position.set((X0+X1)/2, (Y0+Y1)/2, 0); };
  // ---------- fit the camera to what is drawn; a redraw keeps the direction you turned to ----------
  let turned = new THREE.Vector3(1.3, -1.6, 1.1).normalize(), fitted = false;
  const fit = () => {
    const xs = [], ys = [], zs = [];
    B.forEach(b => { b.fp.forEach(p => { xs.push(p[0]); ys.push(p[1]); }); zs.push(b.c[2]+b.size[2]/2); });
    shown.forEach(u => { const e = aboveGround(u); xs.push(e.x0, e.x1); ys.push(e.y0, e.y1); zs.push(e.top); });
    if (!shown.length && !B.length) { xs.push(-10, 10); ys.push(-10, 10); zs.push(20); }
    if (B.length) zs.push(15);
    const x0 = Math.min(...xs), x1 = Math.max(...xs), y0 = Math.min(...ys), y1 = Math.max(...ys), top = Math.max(...zs);
    drawRuler(x0, x1, y0, y1, top);
    const R = Math.hypot(x1-x0, y1-y0, top)/2, dist = 1.15*R/Math.sin(cam.fov*Math.PI/360)/Math.min(1, cam.aspect);
    const tx = (x0+x1)/2, ty = (y0+y1)/2, tz = top/2;
    if (fitted && ctl) turned = cam.position.clone().sub(ctl.target).normalize();
    cam.position.set(tx+turned.x*dist, ty+turned.y*dist, tz+turned.z*dist);
    cam.near = R/50; cam.far = dist+R*30; cam.updateProjectionMatrix();
    if (ctl) { ctl.target.set(tx, ty, tz); ctl.update(); } else cam.lookAt(tx, ty, tz);
    fitted = true; };
  // Draw this list of bubbles in place of the ones drawn now. Each has c (middle) and r (half-widths).
  drawBubbles = (list, unitName) => {
    bubbles.forEach(m => { scene.remove(m); m.children[0].material.dispose(); m.material.dispose(); });
    shown = list; unit = unitName;
    bubbles = list.map((u, i) => { const color = COLORS[i % COLORS.length];
      const m = new THREE.Mesh(skinShape, new THREE.MeshLambertMaterial({color, transparent:true, opacity:.25, depthWrite:false, side:THREE.DoubleSide, clippingPlanes:clip}));
      m.position.set(u.c[0], u.c[1], u.c[2]); m.scale.set(u.r[0], u.r[1], u.r[2]); m.renderOrder = 1; m.visible = bubblesOn;
      m.add(new THREE.LineSegments(wireShape, new THREE.LineBasicMaterial({color, transparent:true, opacity:.45, clippingPlanes:clip})));
      scene.add(m); return m; });
    tog.hidden = !(list.length && B.length);
    fit(); render(); };
  render = () => { const k = +slider.value;
    meshes.forEach((m,i)=>{ m.visible = B[i].step < k; m.material = (B[i].step === k-1) ? hot : wood; });
    ren.render(scene, cam); };
  const resize = () => { const w = el.clientWidth, h = el.clientHeight; ren.setSize(w, h); cam.aspect = w/h; cam.updateProjectionMatrix(); render(); };
  window.addEventListener('resize', resize); resize();
  drawBubbles([], 'blocks');
} else { el.innerHTML = \"<p style='padding:1em'>3D view unavailable (three.js could not be loaded). The step cards below are complete.</p>\"; }
const update = () => { const k=+slider.value; label.textContent = k===0 ? 'empty' : `after step ${k} of ${S.length}`; render(); };
slider.addEventListener('input', update);
document.getElementById('prev').onclick = () => { slider.value = Math.max(0, +slider.value-1); update(); };
document.getElementById('next').onclick = () => { slider.value = Math.min(S.length, +slider.value+1); update(); };
update();
// a page with no blocks shows only the bubbles
if (!S.length) ['controls','sub','stepsTitle'].forEach(id => document.getElementById(id).style.display = 'none');
// ---------- bubble models: check, then draw ----------
// A number as the Lean reader takes it: a JSON number, or a string 'p/q' with q above 0.
const readNumber = v => { if (typeof v === 'number') return Number.isFinite(v) ? v : NaN;
  if (typeof v === 'string') { const p = v.split('/');
    if (p.length === 2 && /^-?[0-9]+$/.test(p[0]) && /^[0-9]+$/.test(p[1]) && +p[1] > 0) return +p[0] / +p[1]; }
  return NaN; };
const readThree = (v, what, who) => { if (!Array.isArray(v) || v.length !== 3) throw new Error(`${who}: ${what} needs three numbers`);
  const r = v.map(readNumber); if (r.some(Number.isNaN)) throw new Error(`${who}: ${what} has something that is not a usable number`);
  return r; };
// The same rules as decode in semantics/KaplaSemantics/Json.lean. Lean stays the final authority.
const readModel = m => {
  if (m === null || typeof m !== 'object' || typeof m.name !== 'string') throw new Error('the model needs a name');
  if (!Array.isArray(m.bubbles)) throw new Error('the model needs a list of bubbles');
  if (m.bubbles.length > 32) throw new Error('the model has more than 32 bubbles');
  const list = m.bubbles.map((b, i) => { const who = `bubble ${i+1}`;
    if (b === null || typeof b !== 'object' || typeof b.label !== 'string' || !b.label) throw new Error(`${who} needs a label`);
    if (!Array.isArray(b.tags) || b.tags.some(t => typeof t !== 'string')) throw new Error(`${b.label}: tags must be a list of words`);
    const c = readThree(b.center, 'center', b.label), r = readThree(b.semi, 'semi', b.label);
    if (r.some(v => v <= 0)) throw new Error(`${b.label}: every half-width must be above 0`);
    if (c[2] + r[2] <= 0) throw new Error(`${b.label}: it is entirely under the ground`);
    return {label:b.label, c, r}; });
  if (!list.some(u => u.c[2] - u.r[2] <= 0)) throw new Error('no bubble reaches the ground, so the model floats');
  return list; };
const errorBox = document.getElementById('error'), info = document.getElementById('info');
const fmt = v => String(+v.toFixed(2));
const showInfo = (title, list, unit) => { info.textContent = '';
  const head = document.createElement('div'); head.textContent = title; info.append(head);
  const ul = document.createElement('ul');
  list.forEach((u, i) => { const e = aboveGround(u), li = document.createElement('li'), dot = document.createElement('span'), t = document.createElement('span');
    dot.className = 'swatch'; dot.style.background = COLORS[i % COLORS.length];
    t.textContent = `${u.label}: ${fmt(e.x)} × ${fmt(e.y)} × ${fmt(e.z)} ${unit}`; li.append(dot, t); ul.append(li); });
  info.append(ul); };
const showError = msg => { errorBox.textContent = `Cannot show this model: ${msg}`; errorBox.hidden = false; info.textContent = ''; drawBubbles([], 'blocks'); };
// Show a model (height 1 and no fixed size) at a height. The model itself is not changed and never
// rescaled to fit. With no height, the numbers are the model's own (0 to 1).
const show = (model, height, shiftX = 0, shiftY = 0) => {
  try {
    const hasHeight = height !== undefined && height !== null, h = hasHeight ? height : 1;
    if (!(h > 0) || !Number.isFinite(h)) throw new Error('the height must be a number above 0');
    if (!Number.isFinite(shiftX) || !Number.isFinite(shiftY)) throw new Error('the shift must be a number');
    const placed = readModel(model).map(u => ({label:u.label, c:[u.c[0]*h+shiftX, u.c[1]*h+shiftY, u.c[2]*h], r:u.r.map(v => v*h)}));
    const unit = hasHeight ? 'blocks' : 'model units', top = Math.max(...placed.map(u => aboveGround(u).top));
    errorBox.hidden = true;
    showInfo(`${model.name}: ${hasHeight ? `height ${fmt(h)} blocks` : 'no height given'}, top at z = ${fmt(top)}`, placed, unit);
    drawBubbles(placed, unit);
    return true;
  } catch (e) { showError(e.message); return false; } };
// The chat calls this when it has a new model.
window.KaplaViewer = {show, showError};
const q = new URLSearchParams(location.search), src = q.get('bubbles');
const addressNumber = (name, d) => q.has(name) ? Number(q.get(name)) : d;
if (src) {
  fetch(src, {cache:'no-store'}).then(r => { if (!r.ok) throw new Error(`could not load ${src} (error ${r.status})`); return r.text(); })
    .then(t => { let m; try { m = JSON.parse(t); } catch (_) { throw new Error(`${src} is not valid JSON`); }
      show(m, addressNumber('height'), addressNumber('shiftX', 0), addressNumber('shiftY', 0)); })
    .catch(e => showError(e.message));
} else if (U.length) { showInfo('The target', U, 'blocks'); drawBubbles(U, 'blocks'); }
else if (!S.length) info.textContent = 'No model yet.';
"

/-- The whole page for a blueprint. -/
def render (p : ViewPlan) : String :=
  let nBlocks := (p.steps.map (·.blocks.length)).foldl (· + ·) 0
  let notes := if p.notes.isEmpty then "" else
    "<ul class=\"notes\">" ++ String.join (p.notes.map fun n => s!"<li>{escape n}</li>") ++ "</ul>"
  let sub := if p.subtitle.isEmpty then "" else s!"{escape p.subtitle} · "
  s!"<!doctype html>
<html lang=\"en\"><head><meta charset=\"utf-8\"><meta name=\"viewport\" content=\"width=device-width,initial-scale=1\">
<title>{escape p.title}</title><style>{css}</style>
<script src=\"https://cdn.jsdelivr.net/npm/three@0.128.0/build/three.min.js\"></script>
<script src=\"https://cdn.jsdelivr.net/npm/three@0.128.0/examples/js/controls/OrbitControls.js\"></script>
</head><body>
<header><h1>{escape p.title}</h1>
<div class=\"sub\" id=\"sub\">{sub}{nBlocks} blocks · {p.steps.length} steps</div>{notes}</header>
<main>
<div id=\"error\" role=\"alert\" hidden></div>
<div id=\"view\"></div>
<div id=\"info\"></div>
<div class=\"controls\" id=\"controls\"><button id=\"prev\">◀</button><input id=\"slider\" type=\"range\" min=\"0\" step=\"1\">
<button id=\"next\">▶</button><span id=\"label\"></span>
<button id=\"bubbles\" class=\"noprint\" hidden>Hide bubbles</button>
<button class=\"noprint\" onclick=\"window.print()\">Print booklet</button></div>
<h3 id=\"stepsTitle\">Steps</h3><div id=\"cards\"></div>
</main>
<script>const DATA = {scriptJson (pageData p)};</script>
<script>{js}</script>
</body></html>"

#guard ((parsePlan exampleJson).map fun p => (render p).contains "three.min.js").toOption == some true
-- the page has the call the chat uses to show a new model
#guard ((parsePlan exampleJson).map fun p => (render p).contains "window.KaplaViewer").toOption == some true
-- text from the file cannot break out of the page
#guard ((parsePlan "{\"title\": \"<script>x\", \"steps\": []}").map fun p =>
  (render p).contains "<title>&lt;script&gt;x</title>").toOption == some true

end KaplaWeb
