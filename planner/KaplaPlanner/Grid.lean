import KaplaCore

/-! # Grid blocks

The planner places blocks on the integer grid: every corner of a block has whole-number
coordinates, and every turn is a quarter turn. A block lies flat, on its long edge, or stands
on its small end. Then a block fills exactly 45 whole grid cells,
and every test (overlap, rests on, inside a bubble) is integer arithmetic. We turn a grid block
into a core `Pose` only at the end. See `planner/DESIGN.md` §3. -/

namespace KaplaPlanner

open KaplaCore

/-- A grid cell `(x, y, z)`: the unit cube with its lowest corner at `(x, y, z)`. -/
abbrev Cell := Int × Int × Int

/-- Which way a grid block lies. The letter says which axis the longer side of its foot
follows. -/
inductive Orient where
  /-- Flat, long side along x: 15 × 3 × 1. -/
  | flatX
  /-- Flat, long side along y: 3 × 15 × 1. -/
  | flatY
  /-- On its long edge, along x: 15 × 1 × 3. -/
  | edgeX
  /-- On its long edge, along y: 1 × 15 × 3. -/
  | edgeY
  /-- Standing, wide side along x: 3 × 1 × 15. -/
  | standX
  /-- Standing, wide side along y: 1 × 3 × 15. -/
  | standY
  deriving Repr, BEq, DecidableEq, Inhabited, Hashable

/-- The size of the block along x, y and z. -/
def Orient.size : Orient → Int × Int × Int
  | .flatX => (15, 3, 1)
  | .flatY => (3, 15, 1)
  | .edgeX => (15, 1, 3)
  | .edgeY => (1, 15, 3)
  | .standX => (3, 1, 15)
  | .standY => (1, 3, 15)

/-- True if the longer side of the block's foot follows x. -/
def Orient.alongX : Orient → Bool
  | .flatX | .edgeX | .standX => true
  | .flatY | .edgeY | .standY => false

/-- True for a block lying flat. -/
def Orient.isFlat : Orient → Bool
  | .flatX | .flatY => true
  | _ => false

/-- Which face is down, in core's terms. -/
def Orient.upright : Orient → Upright
  | .flatX | .flatY => .flat
  | .edgeX | .edgeY => .onEdge
  | .standX | .standY => .standing

/-- The flat ways to lie. -/
def Orient.flats : List Orient := [.flatX, .flatY]

/-- The upright ways: on edge and standing. -/
def Orient.uprights : List Orient := [.edgeX, .edgeY, .standX, .standY]

/-- A block on the grid: how it lies, and its lowest corner. -/
structure GBlock where
  orient : Orient
  x : Int
  y : Int
  z : Int
  deriving Repr, BEq, DecidableEq, Inhabited, Hashable

/-- Size along x. -/
def GBlock.sx (b : GBlock) : Int := b.orient.size.1
/-- Size along y. -/
def GBlock.sy (b : GBlock) : Int := b.orient.size.2.1
/-- Size along z. -/
def GBlock.sz (b : GBlock) : Int := b.orient.size.2.2

/-- One above the highest course the block fills. -/
def GBlock.top (b : GBlock) : Int := b.z + b.sz

/-- The cells the block fills. Always 45. -/
def GBlock.cells (b : GBlock) : List Cell :=
  (List.range b.sz.toNat).flatMap fun (k : Nat) => (List.range b.sy.toNat).flatMap fun (j : Nat) =>
    (List.range b.sx.toNat).map fun (i : Nat) => (b.x + (i : Int), b.y + (j : Int), b.z + (k : Int))

/-- The core pose of the block: which face is down, the turn, and the centre. -/
def GBlock.toPose (b : GBlock) : Pose :=
  let rot := if b.orient.alongX then Rot.id else Rot.quarter
  ⟨b.orient.upright, rot, ⟨(b.x : Q) + (b.sx : Q) / 2, (b.y : Q) + (b.sy : Q) / 2, (b.z : Q) + (b.sz : Q) / 2⟩⟩

/-- Do two blocks share a cell? -/
def GBlock.overlaps (a b : GBlock) : Bool :=
  a.x < b.x + b.sx && b.x < a.x + a.sx && a.y < b.y + b.sy && b.y < a.y + a.sy &&
    a.z < b.z + b.sz && b.z < a.z + a.sz

/-- The middle of a cell. -/
def cellCentre (c : Cell) : Q3 := ⟨(c.1 : Q) + 1 / 2, (c.2.1 : Q) + 1 / 2, (c.2.2 : Q) + 1 / 2⟩

/-- The whole numbers `lo, lo + 1, …, hi`. Empty when `hi < lo`. -/
def intRange (lo hi : Int) : List Int :=
  (List.range (hi + 1 - lo).toNat).map fun (n : Nat) => lo + (n : Int)

-- A grid block fills exactly the cells its core pose contains.
#guard
  let b : GBlock := ⟨.flatY, -4, 2, 3⟩
  let p := b.toPose
  b.cells.length == 45 && b.cells.all (fun c => p.contains (cellCentre c)) &&
    !p.contains (cellCentre (-5, 2, 3)) && !p.contains (cellCentre (-4, 17, 3))
#guard (GBlock.mk .flatX 0 0 0).toPose == ⟨.flat, .id, ⟨15 / 2, 3 / 2, 1 / 2⟩⟩
#guard (GBlock.mk .flatX 0 0 0).toPose.box == (GBlock.mk .flatX 0 0 0).toPose.box
#guard (GBlock.mk .flatY 0 0 0).toPose.box == ⟨⟨0, 0, 0⟩, ⟨3, 15, 1⟩⟩
-- The same for on-edge and standing blocks: core's dimensions, turned a quarter turn when the
-- longer side of the foot follows y.
#guard [Orient.edgeX, .edgeY, .standX, .standY].all fun o =>
  let b : GBlock := ⟨o, 2, -3, 1⟩
  let p := b.toPose
  b.cells.length == 45 && b.cells.all (fun c => p.contains (cellCentre c)) &&
    p.box == ⟨⟨2, -3, 1⟩, ⟨(2 + b.sx : Int), (-3 + b.sy : Int), (1 + b.sz : Int)⟩⟩
#guard (GBlock.mk .flatX 0 0 0).overlaps ⟨.flatY, 14, 2, 0⟩
#guard (GBlock.mk .flatX 0 0 0).overlaps ⟨.standX, 0, 0, -14⟩
#guard !(GBlock.mk .flatX 0 0 0).overlaps ⟨.standX, 0, 0, -15⟩
#guard !(GBlock.mk .flatX 0 0 0).overlaps ⟨.flatY, 15, 0, 0⟩
#guard !(GBlock.mk .flatX 0 0 0).overlaps ⟨.flatX, 0, 0, 1⟩
#guard intRange 2 4 == [2, 3, 4] && intRange 4 2 == []

end KaplaPlanner
