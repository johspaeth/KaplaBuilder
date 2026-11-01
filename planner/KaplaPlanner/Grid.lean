import KaplaCore

/-! # The planning grid

Positions are whole numbers of **grid units**; one grid unit is a quarter of the block
thickness (`1/4` of a block unit, see `KaplaCore`). A Kapla block is 60 × 12 × 4 grid units
(15 × 3 × 1 block units). With this unit, the points a person can place a block at by eye
(the ends, the centre and the quarter points of the block below) are all whole numbers.

For the "strictly inside" check, a block is cut into **cubes** of 4 × 4 × 4 grid units (one
block thickness): 15 × 3 × 1 cubes for a flat block.

Checks on the grid (overlap, "rests on") are plain integer arithmetic. We convert to the
exact `Pose` of `KaplaCore` only at the end (`GridBlock.toPose`). -/

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

/-- One grid unit in block units: a quarter of the block thickness. -/
def unit : Q := blockThickness / 4

/-- Side of a cube in units (one block thickness). -/
def cubeSide : Nat := 4

/-- The size of a block in cubes (one block thickness each) along x, y, z. -/
def Orient.cubes : Orient → Nat × Nat × Nat
  | .flatX    => (15, 3, 1)
  | .flatY    => (3, 15, 1)
  | .edgeX    => (15, 1, 3)
  | .edgeY    => (1, 15, 3)
  | .uprightX => (3, 1, 15)
  | .uprightY => (1, 3, 15)

/-- The size of a block in units along x, y, z. -/
def Orient.size (o : Orient) : Nat × Nat × Nat :=
  (cubeSide * o.cubes.1, cubeSide * o.cubes.2.1, cubeSide * o.cubes.2.2)

/-- A block on the grid: how it lies, and its lowest corner (in units). -/
structure GridBlock where
  orient : Orient
  x : Int
  y : Int
  z : Int
  deriving Repr, BEq, DecidableEq, Inhabited

namespace GridBlock

/-- Size along x (units). -/
def sx (b : GridBlock) : Int := b.orient.size.1
/-- Size along y (units). -/
def sy (b : GridBlock) : Int := b.orient.size.2.1
/-- Size along z (units). -/
def sz (b : GridBlock) : Int := b.orient.size.2.2

/-- The z of the top face (units). -/
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

/-- Move the block by `(dx, dy, dz)` units. -/
def shift (dx dy dz : Int) (b : GridBlock) : GridBlock :=
  { b with x := b.x + dx, y := b.y + dy, z := b.z + dz }

/-- The same block as a `Pose`. -/
def toPose (b : GridBlock) : Pose :=
  let (up, rot) : Upright × Rot := match b.orient with
    | .flatX => (.flat, .id)       | .flatY => (.flat, .quarter)
    | .edgeX => (.onEdge, .id)     | .edgeY => (.onEdge, .quarter)
    | .uprightX => (.standing, .id) | .uprightY => (.standing, .quarter)
  let c (lo : Int) (s : Int) : Q := ((2 * lo + s : Int) : Q) * unit / 2
  ⟨up, rot, ⟨c b.x b.sx, c b.y b.sy, c b.z b.sz⟩⟩

/-- The space the block fills (in block units), computed on the grid. -/
def box (b : GridBlock) : Box :=
  let q (v : Int) : Q := (v : Q) * unit
  ⟨⟨q b.x, q b.y, q b.z⟩, ⟨q (b.x + b.sx), q (b.y + b.sy), q (b.z + b.sz)⟩⟩

end GridBlock

/-- All six orientations. -/
def Orient.all : List Orient := [.flatX, .flatY, .edgeX, .edgeY, .uprightX, .uprightY]

-- The pose we output fills exactly the same box as the grid block, in every orientation.
#guard Orient.all.all fun o =>
  let b : GridBlock := ⟨o, 2, -1, 3⟩
  b.toPose.box == b.box

-- a flat block on the ground, and one on top of it
#guard (GridBlock.mk .flatY 0 0 4).restsOn ⟨.flatX, 0, 0, 0⟩
#guard !(GridBlock.mk .flatY 80 0 4).restsOn ⟨.flatX, 0, 0, 0⟩
#guard (GridBlock.mk .flatX 0 0 0).overlaps ⟨.flatY, 59, 11, 0⟩
#guard !(GridBlock.mk .flatX 0 0 0).overlaps ⟨.flatY, 60, 0, 0⟩
-- a flat block is 15 long
#guard (GridBlock.mk .flatX 0 0 0).box.size.x == blockLength

end KaplaPlanner
