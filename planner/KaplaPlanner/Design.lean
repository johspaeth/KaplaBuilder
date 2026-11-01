import KaplaPlanner.Bubble
import KaplaPlanner.Eyeball

/-! # Design: fill the bubbles' surface with blocks (DESIGN.md §3.4)

Minimal version (P3, demo):
- layer by layer from the ground up; flat blocks along x and along y in turn; where no flat
  block helps (a thin neck, a small head), a block on edge or upright;
- every block lies strictly inside the bubbles, can be placed by eye, does not overlap,
  and (above the ground) has its centre over the blocks it rests on;
- greedy shell: in each layer, keep adding the block with the best shell score (new surface
  cubes covered, plus a bonus for row ends and the outermost rows), until no block covers a
  new surface cube, or the budget is used up;
- a spine: each layer starts with a block near its centre, centred on the spine block below;
  it carries the inside (the top of a ball, a head above a neck); in a neck too narrow for
  flat blocks it goes on with blocks upright;
- the budget is shared between the layers by their surface, so the lowest part does not use
  it all up;
- stability is a parameter (`stands`); for now the demo passes an oracle that always says
  yes, because the physics engine is not merged yet;
- a few scales and ground heights are tried; the best surface coverage wins.

Untrusted: the result is checked again by `insideBubbles` (proven) and `eyeballable`. -/

namespace KaplaPlanner
open KaplaCore

deriving instance Hashable for Orient
deriving instance Hashable for GridBlock

/-! ## Fast inside test with a cache -/

/-- For points of the unit grid: which bubbles contain the point (one bit per bubble). -/
abbrev MaskCache := Std.HashMap (Int × Int × Int) Nat

/-- The bubbles that contain the grid point `p` (in units), as bits. -/
def pointMask (bs : Array Bubble) (p : Int × Int × Int) : Nat :=
  let q : Q3 := ⟨(p.1 : Q) * unit, (p.2.1 : Q) * unit, (p.2.2 : Q) * unit⟩
  (List.range bs.size).foldl (fun m i => if decide (bs[i]!.contains q) then m ||| (1 <<< i) else m) 0

/-- `pointMask`, remembered. -/
def maskAt (bs : Array Bubble) (p : Int × Int × Int) : StateM MaskCache Nat := do
  match (← get).get? p with
  | some m => pure m
  | none =>
    let m := pointMask bs p
    modify (·.insert p m)
    pure m

/-- The cube at `(i, j, k)` has its 8 corners in one bubble (same as `cellInside`). -/
def cubeOk (bs : Array Bubble) (c : Int × Int × Int) : StateM MaskCache Bool := do
  let (i, j, k) := c
  let mut m : Nat := (1 <<< bs.size) - 1
  for dx in [0, 4] do
    for dy in [0, 4] do
      for dz in [0, 4] do
        m := m &&& (← maskAt bs (i + dx, j + dy, k + dz))
  pure (m != 0)

/-- The whole block is strictly inside (same as `insideBubbles` for one block). -/
def blockOk (bs : Array Bubble) (b : GridBlock) : StateM MaskCache Bool :=
  b.cells.allM (cubeOk bs)

/-! ## Covering surface cubes -/

/-- The world cubes whose centre the block covers, in every layer the block spans. -/
def coveredCubes (b : GridBlock) : List Cell :=
  let start (lo : Int) : Int := (lo / 4) * 4 - 4
  let xs := (intRange (start b.x) (b.sx.toNat / 4 + 3) 4).filter fun i => b.x ≤ i + 2 && i + 2 < b.x + b.sx
  let ys := (intRange (start b.y) (b.sy.toNat / 4 + 3) 4).filter fun j => b.y ≤ j + 2 && j + 2 < b.y + b.sy
  let zs := intRange b.z (b.sz.toNat / 4) 4
  zs.flatMap fun k => xs.flatMap fun i => ys.map fun j => (i, j, k)

#guard (coveredCubes ⟨.flatX, 0, 0, 0⟩).length == 45
#guard (coveredCubes ⟨.flatX, 2, 0, 0⟩).length == 45
#guard (coveredCubes ⟨.uprightX, 0, 0, 0⟩).length == 45

/-- Above the ground, the block's centre lies over the area where it touches the blocks
below (a rough stability rule; physics checks properly later). -/
def centreSupported (below : List GridBlock) (b : GridBlock) : Bool :=
  if b.onGround then true else
  let sup := below.filter b.restsOn
  match sup with
  | [] => false
  | _ =>
    let lox := sup.foldl (fun m a => min m (max a.x b.x)) (b.x + b.sx)
    let hix := sup.foldl (fun m a => max m (min (a.x + a.sx) (b.x + b.sx))) b.x
    let loy := sup.foldl (fun m a => min m (max a.y b.y)) (b.y + b.sy)
    let hiy := sup.foldl (fun m a => max m (min (a.y + a.sy) (b.y + b.sy))) b.y
    2 * lox ≤ 2 * b.x + b.sx && 2 * b.x + b.sx ≤ 2 * hix &&
    2 * loy ≤ 2 * b.y + b.sy && 2 * b.y + b.sy ≤ 2 * hiy

/-- New blocks with their bottom at height `z`, in the given poses, that line up with
block `a` (by eye). -/
def candidatesFrom (os : List Orient) (a : GridBlock) (z : Int) : List GridBlock :=
  os.flatMap fun o =>
    let (sx, sy, _) := o.size
    (linedUpStarts a.x a.sx sx).flatMap fun x => (linedUpStarts a.y a.sy sy).map fun y =>
      ⟨o, x, y, z⟩

/-- State of the greedy filling. -/
structure Fill where
  /-- Blocks placed so far, in placement order. -/
  placed  : Array GridBlock := #[]
  /-- Surface cubes already covered. -/
  covered : Std.HashSet Cell := {}

/-- Add a block to the filling. -/
def Fill.add (f : Fill) (b : GridBlock) : Fill :=
  { placed := f.placed.push b, covered := (coveredCubes b).foldl (·.insert ·) f.covered }

/-- How many surface cubes not yet covered the block would cover. -/
def gain (surface : Std.HashSet Cell) (f : Fill) (b : GridBlock) : Nat :=
  (coveredCubes b).countP fun c => surface.contains c && !f.covered.contains c

/-- The direction of the blocks in layer number `k`: along x in even layers, along y in odd
layers. Each layer crosses the one below, which ties the walls together. -/
def layerOrient (k : Nat) : Orient := if k % 2 == 0 then .flatX else .flatY

/-- Where a block's row is (across the block), and where it is along the row. -/
def rowPos (b : GridBlock) : Int × Int := if b.orient == .flatX then (b.y, b.x) else (b.x, b.y)

/-- Shell score of a block (DESIGN.md §3.4): new surface cubes covered, plus a bonus for
the two ends of each row and for the two outermost rows. Together, over two crossing
layers, these close the outline from every side. `pool` are all blocks that may go into
this layer. -/
def shellScore (surface : Std.HashSet Cell) (f : Fill) (pool : List GridBlock)
    (b : GridBlock) : Nat :=
  let g := gain surface f b
  if g == 0 then 0 else
  let (r, a) := rowPos b
  let inRow := (pool.filter fun c => (rowPos c).1 == r).map (fun c => (rowPos c).2)
  let rows := pool.map fun c => (rowPos c).1
  let rowEnd := some a == inRow.min? || some a == inRow.max?
  let outerRow := some r == rows.min? || some r == rows.max?
  g + (if rowEnd then 30 else 0) + (if outerRow then 30 else 0)

/-- The centre (x, y, in units) of the allowed cubes in layer `z`, if there are any. -/
def layerCentre (allowed : List Cell) (z : Int) : Option (Q × Q) :=
  let cs := allowed.filter (·.2.2 == z)
  if cs.isEmpty then none else
  let n : Q := cs.length
  some ((cs.foldl (fun s c => s + c.1) 0 : Int) / n + 2, (cs.foldl (fun s c => s + c.2.1) 0 : Int) / n + 2)

/-- Squared distance (seen from above) from the block's centre to the point `c`. -/
def distTo (c : Q × Q) (b : GridBlock) : Q :=
  let dx : Q := ((2 * b.x + b.sx : Int) : Q) / 2 - c.1
  let dy : Q := ((2 * b.y + b.sy : Int) : Q) / 2 - c.2
  dx * dx + dy * dy

/-- Blocks on edge or upright: taller than one layer. Used where no flat block helps, for
example in a thin neck or a small head. -/
def tallOrients : List Orient := [.edgeX, .edgeY, .uprightX, .uprightY]

/-- Fill one layer: new blocks with their bottom at height `z`. Flat blocks go in direction
`o`; only if no flat block fits in the layer, blocks on edge or upright may go in. `below` are the blocks whose
top is at `z`; `active` are earlier blocks that reach into this layer from below (tall
blocks), which new blocks must not overlap. `seed` is the first block for the ground
layer.

**The spine.** Each layer starts with one block near the centre of the layer, centred on the
spine block below (`spine`, if its top is at `z`). It carries the inner part of the build,
for example the top of a ball or a head above a neck. Where no flat block fits, the spine
goes on with a block upright or on edge. Returns the new top block of the spine. -/
def fillLayer (bs : Array Bubble) (surface : Std.HashSet Cell) (stands : List GridBlock → Bool)
    (centre : Option (Q × Q)) (z : Int) (o : Orient) (below active : List GridBlock)
    (seed spine : Option GridBlock) (budget : Nat) (f0 : Fill) :
    StateM MaskCache (Fill × Option GridBlock) := do
  let mut f := f0
  let mut layer : List GridBlock := active
  -- blocks that may go in this layer: lined up with a block below (or, on the ground, with a
  -- block already on the ground), inside the bubbles, centre supported
  let mut pool : List GridBlock := []
  let mut refs : List GridBlock := below
  if z == 0 then
    match seed with
    | some s =>
      if (← blockOk bs s) then
        f := f.add s
        layer := [s]
        refs := [s]
    | none => pure ()
  -- the spine
  let mut top := spine
  match spine, centre with
  | some s, some c =>
    if s.top == z && budget > 0 then
      let mut cands : List GridBlock := []
      for b in candidatesFrom (o :: tallOrients) s z do
        if b.restsOn s && centreSupported below b && !layer.any (·.overlaps b) &&
            placedByEye f.placed.toList b && (← blockOk bs b) then
          cands := b :: cands
      let near (l : List GridBlock) := l.mergeSort fun a b => distTo c a ≤ distTo c b
      let tallRank (b : GridBlock) : Nat := match b.orient with
        | .uprightX | .uprightY => 0 | _ => 1
      let ordered := near (cands.filter (·.orient == o)) ++
        ((near (cands.filter (·.orient != o))).mergeSort fun a b => tallRank a ≤ tallRank b)
      match ordered.find? fun b => stands (f.placed.toList ++ [b]) with
      | some b =>
        f := f.add b
        layer := b :: layer
        refs := b :: refs
        top := some b
      | none => top := none
  | _, _ => pure ()
  let mut seen : Std.HashSet GridBlock := {}
  for _ in [0:budget - (f.placed.size - f0.placed.size)] do
    -- grow the pool from new reference blocks
    for a in refs do
      for b in candidatesFrom (o :: tallOrients) a z do
        if !seen.contains b then
          seen := seen.insert b
          if centreSupported below b && placedByEye (f.placed.toList) b && (← blockOk bs b) then
            pool := b :: pool
    refs := []
    -- best block that does not overlap the layer
    let free := pool.filter fun b => !layer.any (·.overlaps b)
    -- flat blocks first, best shell score first; then tall blocks, most new surface first;
    -- take the first one with which the structure still stands
    let flatPool := pool.filter (·.orient == o)
    let byScore (l : List (GridBlock × Nat)) := (l.filter (·.2 > 0)).mergeSort fun a b => a.2 ≥ b.2
    let flat := byScore ((free.filter (·.orient == o)).map fun b => (b, shellScore surface f flatPool b))
    -- tall blocks only in a layer where no flat block fits (they would block the layers above)
    let flatPlaced := layer.any fun b => b.orient == o && b.z == z
    let tall := if flatPlaced then [] else
      byScore ((free.filter (·.orient != o)).map fun b => (b, gain surface f b))
    let best := (flat ++ tall).find? fun (b, _) => stands (f.placed.toList ++ [b])
    match best with
    | none => break
    | some (b, _) =>
      f := f.add b
      layer := b :: layer
      if z == 0 then refs := [b]
  return (f, top)

/-- A finished design and how well it covers the surface. -/
structure Design where
  /-- The bubbles, scaled and moved; the design lies strictly inside them. -/
  bubbles  : List Bubble
  /-- The blocks in placement order. -/
  blocks   : List GridBlock
  /-- Surface cubes covered, and surface cubes in total (above the ground). -/
  covered  : Nat
  total    : Nat
  scale    : Q
  deriving Inhabited

/-- Share of the surface covered (0 to 1). -/
def Design.coverage (d : Design) : Q := if d.total == 0 then 0 else (d.covered : Q) / d.total

/-- The first block on the ground (and the bottom of the spine): the flat block inside the
bubbles that is nearest to the centre of the ground layer. -/
def bestSeed (bs : Array Bubble) (allowed : Std.HashSet Cell) :
    StateM MaskCache (Option GridBlock) := do
  let ground := allowed.toList.filter (·.2.2 == 0)
  match layerCentre ground 0 with
  | none => return none
  | some c =>
    let x0 := (c.1 - 30).floor
    let y0 := (c.2 - 6).floor
    let tries := ((intRange (x0 - 30) 61).flatMap fun x => (intRange (y0 - 30) 61).map fun y =>
      (⟨.flatX, x, y, 0⟩ : GridBlock)).mergeSort fun a b => distTo c a ≤ distTo c b
    tries.findM? (blockOk bs)

/-- Design for bubbles that are already scaled and placed, with at most `n` blocks.
`stands blocks` says whether the blocks, placed in this order, stand after every step. -/
def designPlaced (stands : List GridBlock → Bool) (bs : List Bubble) (n : Nat) (s : Q) :
    Design := Id.run do
  let arr := bs.toArray
  let allowed := allowedCells bs
  let surface : Std.HashSet Cell := (surfaceCells allowed).foldl (·.insert ·) {}
  let topZ := (allowed.toList.map (·.2.2)).max?.getD 0
  let run : StateM MaskCache Fill := do
    let seed ← bestSeed arr allowed
    let mut f : Fill := {}
    let mut spine : Option GridBlock := seed
    let allowedL := allowed.toList
    -- blocks are shared between the layers in proportion to their surface; a layer that uses
    -- fewer passes the rest on, so the lowest part does not use up the whole budget
    let surfaceL := surface.toList
    let mut spare : Q := 0
    for k in [0:(topZ / 4 + 1).toNat] do
      let z : Int := 4 * k
      if f.placed.size ≥ n then break
      let blocks := f.placed.toList
      -- nothing reaches this height: no block can be supported any more
      if z > 0 && !blocks.any (·.top ≥ z) then break
      let below := blocks.filter (·.top == z)
      let active := blocks.filter fun b => b.z < z && b.top > z
      let share : Q := spare + (n : Q) * ((surfaceL.countP (·.2.2 == z) : Nat) : Q) / (max surface.size 1 : Nat)
      let layerBudget := min (n - f.placed.size) (max 1 share.floor.toNat)
      let (f', sp) ← fillLayer arr surface stands (layerCentre allowedL z) z (layerOrient k)
        below active seed (if k == 0 then none else spine) layerBudget f
      spare := share - ((f'.placed.size - f.placed.size : Nat) : Q)
      f := f'
      if k > 0 then spine := sp
    return f
  let (f, _) := run.run {}
  { bubbles := bs, blocks := f.placed.toList,
    covered := (surface.toList.filter f.covered.contains).length,
    total := surface.size, scale := s }

/-- Scale the target by `s` and sink it so that the ground cuts it at `sink` (a share of its
height, from the bottom). -/
def placeTarget (t : TargetSpec) (s sink : Q) : List Bubble :=
  let scaled := t.bubbles.map (placeBubble s ⟨0, 0, 0⟩)
  let bounds := scaled.filterMap bubbleBounds
  let zlo := (bounds.map (·.lo.z)).foldl min ((bounds.head?.map (·.lo.z)).getD 0)
  let zhi := (bounds.map (·.hi.z)).foldl max ((bounds.head?.map (·.hi.z)).getD 0)
  scaled.map (placeBubble 1 ⟨0, 0, -(zlo + sink * (zhi - zlo))⟩)

/-- Try a few scales and ground heights; keep the design with the best surface coverage. -/
def design (stands : List GridBlock → Bool) (t : TargetSpec) (n : Nat)
    (scales : List Q := [1, 3 / 2, 2]) (sinks : List Q := [1 / 10, 1 / 5]) : Option Design :=
  let all := scales.flatMap fun s => sinks.map fun k => designPlaced stands (placeTarget t s k) n s
  all.foldl (fun acc d => match acc with
    | some b => if d.coverage > b.coverage then some d else acc
    | none => if d.blocks.isEmpty then none else some d) none

end KaplaPlanner
