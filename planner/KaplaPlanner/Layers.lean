import KaplaPlanner.Motifs

/-!
# KaplaPlanner.Layers — the generic layer planner (untrusted)

Fills the target with courses of flat blocks, alternating direction every layer (like a
log cabin, so every course crosses the one below). A block is placed where most of its
volume lies in the target and its centre is spanned by supports in the course below.
-/

namespace Kapla.Planning

open Kapla

/-- Fraction of sample points of block `b` that lie inside the shape. -/
def fillFraction (s : Shape) (b : Pose) : Q :=
  let pts := (List.range 10).flatMap fun i => (List.range 2).map fun j =>
    b.toWorld ⟨((i : Q) + 1/2) / 10 * L - L / 2, ((j : Q) + 1/2) / 2 * W - W / 2, 0⟩
  ((pts.filter s.mem).length : Q) / pts.length

/-- Heuristic support test: some lower block lies under a point at or left of the centre and
some under a point at or right of it (along the block's long axis). Ground always supports. -/
def spanned (below : List Pose) (b : Pose) : Bool :=
  if b.bottomZ = 0 then true else
  let under (t : Q) : Bool :=
    let p := b.toWorld ⟨t, 0, -b.half.z⟩
    below.any fun a => a.topZ = b.bottomZ && decide (a.InFootprint p)
  let ts : List Q := [-2 * W, -W, -W/2, 0, W/2, W, 2 * W]
  (ts.any fun t => t ≤ 0 && under t) && (ts.any fun t => t ≥ 0 && under t)

/-- Lattice positions covering `[lo, hi]` with spacing `step`, aligned to `step·ℤ + off`. -/
def lattice (lo hi step off : Q) : List Q :=
  let a := ((lo - off) / step).floor - 1
  let b := ((hi - off) / step).ceil + 1
  (List.range (b - a + 1).toNat).map fun n => off + (a + n) * step

/-- One course at height index `k` in direction `alongX`. With `stagger = some e0` the
blocks sit on the lattice `e0 + L·ℤ` (running bond over a course in the same direction). -/
def course (s : Shape) (lo hi : Q3) (k : Nat) (alongX : Bool) (below : List Pose)
    (budget : Nat) (threshold off : Q) (stagger : Option Q) (phases : Nat := 5) :
    List Pose := Id.run do
  let z := layerZ k
  let (aLo, aHi, lLo, lHi) := if alongX then (lo.y, hi.y, lo.x, hi.x) else (lo.x, hi.x, lo.y, hi.y)
  let mut layer : List Pose := []
  -- the row's blocks, greedily from a start position, stepping `step` when nothing fits
  let run (a e0 step : Q) (room : Nat) : List Pose := Id.run do
    let mut e := e0
    let mut out : List Pose := []
    while e ≤ lHi do
      let c := e + L / 2
      let b := if alongX then flatAt c a z true else flatAt a c z false
      if out.length < room && fillFraction s b ≥ threshold && spanned below b then
        out := out ++ [b]
        e := e + L
      else
        e := e + step
    return out
  let mid := (lLo + lHi) / 2
  let along (b : Pose) : Q := if alongX then b.center.x else b.center.y
  for a in lattice aLo aHi W off do
    let room := budget - layer.length
    let row := match stagger with
      | some e0 => run a (e0 - (((e0 - (lLo - L)) / L).ceil : Q) * L) L room
      | none =>
        -- try the five lattice phases; prefer more blocks, then a better-centred run
        let options := (List.range phases).map fun φ => run a (lLo - L + φ * W) W room
        let off (r : List Pose) : Q :=
          match r.head?, r.getLast? with
          | some f, some l => |(along f + along l) / 2 - mid|
          | _, _ => 0
        options.foldl (fun best r =>
          if r.length > best.length || (r.length = best.length && off r < off best) then r
          else best) []
    layer := layer ++ row
  return layer

/-- The layer plan, bottom-up (at most `maxBlocks`). Courses alternate direction (log
cabin); where the crossing course would hold fewer blocks — thin walls — the course runs in
the same direction as the one below, staggered by a quarter block (running bond). -/
def layerPlan (s : Shape) (maxBlocks : Nat) (threshold : Q := 1/2) (off : Q := 0)
    (phases : Nat := 5) : List (List Pose) := Id.run do
  let (lo, hi) := s.bbox
  let nLayers := ((hi.z / T).ceil).toNat
  let mut layers : Array (List Pose) := #[]
  let mut below : List Pose := []
  let mut belowX := false
  let mut shift : Q := L / 4
  let mut count := 0
  for k in [0:nLayers] do
    let budget := maxBlocks - count
    if budget = 0 then break
    let cross := course s lo hi k (!belowX) below budget threshold off none phases
    let same :=
      if k = 0 then [] else
      match below.head? with
      | none => []
      | some b0 =>
        -- quarter-block stagger, alternating left/right so the wall does not drift and
        -- the end blocks keep a press-safe overhang
        let e0 := (if belowX then b0.center.x else b0.center.y) - L / 2 + shift
        course s lo hi k belowX below budget threshold off (some e0)
    let (layer, dirX) := if same.length > cross.length then (same, belowX) else (cross, !belowX)
    shift := if dirX == belowX then -shift else L / 4
    if layer.isEmpty then break
    layers := layers.push layer
    below := layer
    belowX := dirX
    count := count + layer.length
  return layers.toList

end Kapla.Planning
