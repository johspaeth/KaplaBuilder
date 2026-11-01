import KaplaPlanner.Bubble
import KaplaPlanner.Eyeball

/-! # Design: fill the bubbles' surface with blocks (DESIGN.md §3.4)

Minimal version (P3, demo):
- flat blocks only, both directions; layer by layer from the ground up;
- every block lies strictly inside the bubbles, can be placed by eye, does not overlap,
  and (above the ground) has its centre over the blocks it rests on;
- greedy: in each layer, keep adding the block that covers the most surface cubes not yet
  covered, until no block adds any, or the budget is used up;
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

/-- The world cubes in layer `z` whose centre the block covers (seen from above). -/
def coveredCubes (b : GridBlock) : List Cell :=
  let start (lo : Int) : Int := (lo / 4) * 4 - 4
  let xs := (intRange (start b.x) (b.sx.toNat / 4 + 3) 4).filter fun i => b.x ≤ i + 2 && i + 2 < b.x + b.sx
  let ys := (intRange (start b.y) (b.sy.toNat / 4 + 3) 4).filter fun j => b.y ≤ j + 2 && j + 2 < b.y + b.sy
  xs.flatMap fun i => ys.map fun j => (i, j, b.z)

#guard (coveredCubes ⟨.flatX, 0, 0, 0⟩).length == 45
#guard (coveredCubes ⟨.flatX, 2, 0, 0⟩).length == 45

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

/-- New blocks in layer `z` that line up with block `a` (by eye), both flat directions. -/
def candidatesFrom (a : GridBlock) (z : Int) : List GridBlock :=
  [Orient.flatX, .flatY].flatMap fun o =>
    let (sx, sy, _) := o.size
    (linedUpStarts a.x a.sx sx).flatMap fun x => (linedUpStarts a.y a.sy sy).map fun y =>
      ⟨o, x, y, z⟩

/-- State of the greedy filling. -/
structure Fill where
  /-- Blocks placed so far, in placement order. -/
  placed  : Array GridBlock := #[]
  /-- Surface cubes already covered. -/
  covered : Std.HashSet Cell := {}

/-- How many surface cubes not yet covered the block would cover. -/
def gain (surface : Std.HashSet Cell) (f : Fill) (b : GridBlock) : Nat :=
  (coveredCubes b).countP fun c => surface.contains c && !f.covered.contains c

/-- Fill one layer at height `z`. `below` are the blocks of the layer below; `seed` is the
first block for the ground layer. -/
def fillLayer (bs : Array Bubble) (surface : Std.HashSet Cell) (stands : List GridBlock → Bool)
    (z : Int) (below : List GridBlock) (seed : Option GridBlock) (budget : Nat) (f0 : Fill) :
    StateM MaskCache Fill := do
  let mut f := f0
  let mut layer : List GridBlock := []
  -- blocks that may go in this layer: lined up with a block below (or, on the ground, with a
  -- block already on the ground), inside the bubbles, centre supported
  let mut pool : List GridBlock := []
  let mut refs : List GridBlock := below
  if z == 0 then
    match seed with
    | some s =>
      if (← blockOk bs s) then
        f := { placed := f.placed.push s, covered := (coveredCubes s).foldl (·.insert ·) f.covered }
        layer := [s]
        refs := [s]
    | none => pure ()
  let mut seen : Std.HashSet GridBlock := {}
  for _ in [0:budget] do
    -- grow the pool from new reference blocks
    for a in refs do
      for b in candidatesFrom a z do
        if !seen.contains b then
          seen := seen.insert b
          if centreSupported below b && placedByEye (f.placed.toList) b && (← blockOk bs b) then
            pool := b :: pool
    refs := []
    -- best block that does not overlap the layer
    let free := pool.filter fun b => !layer.any (·.overlaps b)
    pool := free
    -- best gain first; take the first one with which the structure still stands
    let ranked := ((free.map fun b => (b, gain surface f b)).filter (·.2 > 0)).mergeSort
      fun a b => a.2 ≥ b.2
    let best := ranked.find? fun (b, _) => stands (f.placed.toList ++ [b])
    match best with
    | none => break
    | some (b, _) =>
      f := { placed := f.placed.push b, covered := (coveredCubes b).foldl (·.insert ·) f.covered }
      layer := b :: layer
      if z == 0 then refs := [b]
  return f

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

/-- The best first block on the ground: inside, covering the most surface cubes. -/
def bestSeed (bs : Array Bubble) (surface : Std.HashSet Cell) (allowed : Std.HashSet Cell) :
    StateM MaskCache (Option GridBlock) := do
  let ground := allowed.toList.filter (·.2.2 == 0)
  let xs := ground.map (·.1)
  let ys := ground.map (·.2.1)
  match (xs.min? : Option Int), (xs.max? : Option Int), (ys.min? : Option Int), (ys.max? : Option Int) with
  | some x0, some x1, some y0, some y1 =>
    let mut best : Option (GridBlock × Nat) := none
    for o in [Orient.flatX, .flatY] do
      for x in intRange (x0 - 60) ((x1 - x0 + 64).toNat / 3 + 1) 3 do
        for y in intRange (y0 - 60) ((y1 - y0 + 64).toNat / 3 + 1) 3 do
          let b : GridBlock := ⟨o, x, y, 0⟩
          let g := gain surface {} b
          if g > (best.map (·.2)).getD 0 then
            if (← blockOk bs b) then best := some (b, g)
    return best.map (·.1)
  | _, _, _, _ => return none

/-- Design for bubbles that are already scaled and placed, with at most `n` blocks.
`stands blocks` says whether the blocks, placed in this order, stand after every step. -/
def designPlaced (stands : List GridBlock → Bool) (bs : List Bubble) (n : Nat) (s : Q) :
    Design := Id.run do
  let arr := bs.toArray
  let allowed := allowedCells bs
  let surface : Std.HashSet Cell := (surfaceCells allowed).foldl (·.insert ·) {}
  let topZ := (allowed.toList.map (·.2.2)).max?.getD 0
  let run : StateM MaskCache Fill := do
    let seed ← bestSeed arr surface allowed
    let mut f : Fill := {}
    let mut below : List GridBlock := []
    let mut z : Int := 0
    for _ in [0:(topZ / 4 + 1).toNat] do
      if f.placed.size ≥ n then break
      let before := f.placed.size
      f ← fillLayer arr surface stands z below seed (n - f.placed.size) f
      below := (f.placed.toList.drop before)
      if below.isEmpty then break
      z := z + 4
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
