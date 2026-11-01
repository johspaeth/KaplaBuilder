import KaplaCore

/-! # The planning grid

The planner works on a grid of cubes with side 7.8 mm (one block thickness). A Kapla
block is exactly 15 × 3 × 1 cells, so every grid block fills whole cells. Checks on the
grid (overlap, "rests on") are plain integer arithmetic. We convert to the exact `Pose`
of `KaplaCore` only at the end (`GridBlock.toPose`). -/

namespace KaplaPlanner
open KaplaCore

/-- The six ways a block can lie on the grid. -/
inductive Orient where
  /-- flat, long side along x -/
  | flatX
  /-- flat, long side along y -/
  | flatY
  /-- on its long edge, long side along x -/
  | edgeX
  /-- on its long edge, long side along y -/
  | edgeY
  /-- standing, the wide side along x -/
  | uprightX
  /-- standing, the wide side along y -/
  | uprightY
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The size of a block in cells along x, y, z. -/
def Orient.size : Orient → Nat × Nat × Nat
  | .flatX    => (15, 3, 1)
  | .flatY    => (3, 15, 1)
  | .edgeX    => (15, 1, 3)
  | .edgeY    => (1, 15, 3)
  | .uprightX => (3, 1, 15)
  | .uprightY => (1, 3, 15)

/-- A block on the grid: how it lies, and the cell of its lowest corner. -/
structure GridBlock where
  orient : Orient
  x : Int
  y : Int
  z : Int
  deriving Repr, BEq, DecidableEq, Inhabited

namespace GridBlock

/-- Size along x, y, z (cells). -/
def sx (b : GridBlock) : Int := b.orient.size.1
def sy (b : GridBlock) : Int := b.orient.size.2.1
def sz (b : GridBlock) : Int := b.orient.size.2.2

/-- The z of the top face (cells). -/
def top (b : GridBlock) : Int := b.z + b.sz

/-- Two intervals `[a, a + la)` and `[b, b + lb)` share a part of positive length. -/
def spansOverlap (a la b lb : Int) : Bool := a < b + lb && b < a + la

/-- The footprints of the two blocks (seen from above) share some area. -/
def footprintsOverlap (a b : GridBlock) : Bool :=
  spansOverlap a.x a.sx b.x b.sx && spansOverlap a.y a.sy b.y b.sy

/-- The two blocks share some volume. -/
def overlaps (a b : GridBlock) : Bool :=
  footprintsOverlap a b && spansOverlap a.z a.sz b.z b.sz

/-- `upper` sits directly on `lower`: its bottom is at the top of `lower`, and the
footprints share some area. -/
def restsOn (upper lower : GridBlock) : Bool :=
  upper.z == lower.top && footprintsOverlap upper lower

/-- The block sits on the ground. -/
def onGround (b : GridBlock) : Bool := b.z == 0

/-- Move the block by `(dx, dy, dz)` cells. -/
def shift (dx dy dz : Int) (b : GridBlock) : GridBlock :=
  { b with x := b.x + dx, y := b.y + dy, z := b.z + dz }

/-- The same block as a `Pose` (mm). -/
def toPose (b : GridBlock) : Pose :=
  let (up, rot) : Upright × Rot := match b.orient with
    | .flatX => (.flat, .id)       | .flatY => (.flat, .quarter)
    | .edgeX => (.onEdge, .id)     | .edgeY => (.onEdge, .quarter)
    | .uprightX => (.standing, .id) | .uprightY => (.standing, .quarter)
  let c (lo : Int) (s : Int) : Q := ((2 * lo + s : Int) : Q) * blockThickness / 2
  ⟨up, rot, ⟨c b.x b.sx, c b.y b.sy, c b.z b.sz⟩⟩

/-- The block's box in mm, computed on the grid. -/
def boxMm (b : GridBlock) : Box :=
  let mm (v : Int) : Q := (v : Q) * blockThickness
  ⟨⟨mm b.x, mm b.y, mm b.z⟩, ⟨mm (b.x + b.sx), mm (b.y + b.sy), mm (b.z + b.sz)⟩⟩

end GridBlock

/-- All six orientations. -/
def Orient.all : List Orient := [.flatX, .flatY, .edgeX, .edgeY, .uprightX, .uprightY]

-- The pose we output fills exactly the same box as the grid block, in every orientation.
#guard Orient.all.all fun o =>
  let b : GridBlock := ⟨o, 2, -1, 3⟩
  b.toPose.box == b.boxMm

-- a flat block on the ground, and one on top of it
#guard (GridBlock.mk .flatY 0 0 1).restsOn ⟨.flatX, 0, 0, 0⟩
#guard !(GridBlock.mk .flatY 20 0 1).restsOn ⟨.flatX, 0, 0, 0⟩
#guard (GridBlock.mk .flatX 0 0 0).overlaps ⟨.flatY, 14, 2, 0⟩
#guard !(GridBlock.mk .flatX 0 0 0).overlaps ⟨.flatY, 15, 0, 0⟩

end KaplaPlanner
