import KaplaPlanner.Grid

/-! # The cell table

At one height, place the bubbles once and mark, for every grid cell, which bubbles hold its
middle (a bit mask). This is the only place where the planner uses the ellipsoid formula; after
this, everything is a lookup. See `planner/DESIGN.md` §4.2.

The table covers a box around the bubbles, with room on every side for a block that sticks
out. Cells outside the box are in no bubble. -/

namespace KaplaPlanner

open KaplaCore

/-- Room left on each side of the bubbles in x and y, so a block that sticks out still fits. -/
def pad : Int := 16

/-- The cell table at one height. -/
structure Table where
  /-- The bubbles at their real size. -/
  placed : Array Bubble
  /-- Lowest corner of the box the table covers. Its z is always 0. -/
  x0 : Int
  y0 : Int
  /-- Size of the box, in cells. -/
  nx : Nat
  ny : Nat
  nz : Nat
  /-- For each cell, bit `i` is set when bubble `i` holds its middle. -/
  mask : Array UInt64
  /-- The number of cells in some bubble (`|T|` of the score). -/
  target : Nat
  /-- For each column (x, y): one above the highest bubble cell in it, 0 if none. -/
  colTop : Array Int
  /-- For each bubble and each column (x, y): the lowest course with a cell of that bubble in
  that column, `nz` if none. -/
  colLow : Array (Array Int)
  deriving Inhabited

/-- The cells with middle inside the box, faces included (as in the scorer). -/
def cellRange (lo hi : Q) : Int × Int := ((lo - 1 / 2).ceil, (hi - 1 / 2).floor)

/-- Is the cell in the box the table covers? -/
def Table.inside (t : Table) (c : Cell) : Bool :=
  t.x0 ≤ c.1 && c.1 < t.x0 + t.nx && t.y0 ≤ c.2.1 && c.2.1 < t.y0 + t.ny &&
    0 ≤ c.2.2 && c.2.2 < t.nz

/-- The position of a cell in the arrays. Only for cells inside the box. -/
def Table.index (t : Table) (c : Cell) : Nat :=
  ((c.2.2.toNat * t.ny) + (c.2.1 - t.y0).toNat) * t.nx + (c.1 - t.x0).toNat

/-- The bubbles that hold the cell, as a bit mask. 0 outside the box. -/
def Table.maskAt (t : Table) (c : Cell) : UInt64 :=
  if t.inside c then t.mask[t.index c]!  else 0

/-- One above the highest bubble cell in the column of the cell, 0 if none or outside the box. -/
def Table.topAt (t : Table) (x y : Int) : Int :=
  if t.x0 ≤ x && x < t.x0 + t.nx && t.y0 ≤ y && y < t.y0 + t.ny then
    t.colTop[(y - t.y0).toNat * t.nx + (x - t.x0).toNat]!
  else 0

/-- The lowest course of bubble `b` in column (x, y); `nz` if none or outside the box. -/
def Table.lowAt (t : Table) (b : Nat) (x y : Int) : Int :=
  if t.x0 ≤ x && x < t.x0 + t.nx && t.y0 ≤ y && y < t.y0 + t.ny then
    (t.colLow[b]!)[(y - t.y0).toNat * t.nx + (x - t.x0).toNat]!
  else t.nz

/-- Is there a bubble cell above this cell, in the same column? -/
def Table.under (t : Table) (c : Cell) : Bool := c.2.2 + 1 < t.topAt c.1 c.2.1

/-- Build the table for a model at a height. Uses at most the first 64 bubbles (core allows 32). -/
def Table.make (m : BubbleModel) (height : Q) : Table := Id.run do
  let placed := (m.bubbles.take 64).toArray.map (·.place (Frame.ofHeight height))
  let ranges := placed.map fun b =>
    let bx := b.box
    (cellRange bx.lo.x bx.hi.x, cellRange bx.lo.y bx.hi.y, cellRange (max 0 bx.lo.z) bx.hi.z)
  let xlo := ranges.foldl (fun a r => min a r.1.1) 0
  let xhi := ranges.foldl (fun a r => max a r.1.2) 0
  let ylo := ranges.foldl (fun a r => min a r.2.1.1) 0
  let yhi := ranges.foldl (fun a r => max a r.2.1.2) 0
  let zhi := ranges.foldl (fun a r => max a r.2.2.2) 0
  let x0 := xlo - pad
  let y0 := ylo - pad
  let nx := (xhi + pad + 1 - x0).toNat
  let ny := (yhi + pad + 1 - y0).toNat
  let nz := (zhi + 1).toNat
  let base : Table := { placed, x0, y0, nx, ny, nz, mask := #[], target := 0, colTop := #[], colLow := #[] }
  let mut mask : Array UInt64 := Array.replicate (nx * ny * nz) 0
  for h : i in [0:placed.size] do
    let b := placed[i]'h.upper
    let ((ax, bx), (ay, by_), (az, bz)) := ranges[i]!
    for z in intRange (max 0 az) bz do
      for y in intRange ay by_ do
        for x in intRange ax bx do
          if b.contains (cellCentre (x, y, z)) then
            let k := base.index (x, y, z)
            mask := mask.set! k (mask[k]! ||| ((1 : UInt64) <<< i.toUInt64))
  let target := mask.foldl (fun n v => if v != 0 then n + 1 else n) 0
  let mut colTop : Array Int := Array.replicate (nx * ny) 0
  for z in [0:nz] do
    for k in [0:nx * ny] do
      if mask[z * nx * ny + k]! != 0 then colTop := colTop.set! k ((z : Int) + 1)
  let mut colLow : Array (Array Int) := Array.replicate placed.size (Array.replicate (nx * ny) (nz : Int))
  for k in [0:nx * ny] do
    for b in [0:placed.size] do
      let mut z := 0
      while z < nz && (mask[z * nx * ny + k]! >>> b.toUInt64) &&& 1 == 0 do z := z + 1
      if z < nz then colLow := colLow.modify b (·.set! k (z : Int))
  return { base with mask, target, colTop, colLow }

/-- Example: one ball of height 1 with its bottom on the ground. -/
def ballModel : BubbleModel :=
  { name := "ball"
    bubbles := [{ label := "ball", tags := [], center := ⟨0, 0, 1 / 2⟩, semi := ⟨1 / 2, 1 / 2, 1 / 2⟩ }] }

/-- Example: the bunny of `semantics/APPROACH.md` §1, six bubbles. -/
def bunnyModel : BubbleModel :=
  { name := "bunny"
    bubbles :=
      [ { label := "body", tags := ["tower"], center := ⟨0, 0, 28 / 100⟩, semi := ⟨30 / 100, 22 / 100, 28 / 100⟩ }
      , { label := "head", tags := ["tower"], center := ⟨22 / 100, 0, 60 / 100⟩, semi := ⟨17 / 100, 15 / 100, 16 / 100⟩ }
      , { label := "left ear", tags := ["wall"], center := ⟨20 / 100, -7 / 100, 86 / 100⟩, semi := ⟨5 / 100, 3 / 100, 14 / 100⟩ }
      , { label := "right ear", tags := ["wall"], center := ⟨20 / 100, 7 / 100, 86 / 100⟩, semi := ⟨5 / 100, 3 / 100, 14 / 100⟩ }
      , { label := "tail", tags := [], center := ⟨-32 / 100, 0, 30 / 100⟩, semi := ⟨7 / 100, 7 / 100, 7 / 100⟩ }
      , { label := "paws", tags := ["slab"], center := ⟨30 / 100, 0, 5 / 100⟩, semi := ⟨8 / 100, 14 / 100, 5 / 100⟩ } ] }

-- The same cell counts as the scorer: the ball has 8 cells at height 2 and 136 at height 6,
-- and the egg has 5152 at height 30 (`semantics/KaplaSemantics/Grid.lean`).
#guard (Table.make ballModel 2).target == 8
#guard (Table.make ballModel 6).target == 136
#guard (Table.make BubbleModel.egg 30).target == 5152
#guard (Table.make ballModel 2).maskAt (-1, -1, 0) == 1
#guard (Table.make ballModel 2).maskAt (5, 5, 5) == 0
#guard (Table.make ballModel 2).maskAt (500, 0, 0) == 0
-- Under the ball at height 2, the ground cell below its top half is "under" it.
#guard (Table.make ballModel 2).under (0, 0, 0) && !(Table.make ballModel 2).under (0, 0, 1)
#guard !(Table.make ballModel 2).under (9, 0, 0)

end KaplaPlanner
