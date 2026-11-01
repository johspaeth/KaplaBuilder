import KaplaCore
import Std.Data.HashSet

/-! # The grid

Lay a grid of cubes with side 1 over the table. Cube `(i, j, k)` has its middle at
`(i + ½, j + ½, k + ½)`. "A cube is inside something" means its middle is. See
`semantics/APPROACH.md` §4. -/

namespace KaplaSemantics

open KaplaCore

/-- One cube of the grid. -/
abbrev GridPt := Int × Int × Int

/-- The middle of a cube. -/
def GridPt.centre (g : GridPt) : Q3 :=
  ⟨(g.1 : Q) + 1 / 2, (g.2.1 : Q) + 1 / 2, (g.2.2 : Q) + 1 / 2⟩

/-- The whole numbers from `lo` to `hi`, both included. -/
def intsBetween (lo hi : Int) : List Int :=
  (List.range (hi + 1 - lo).toNat).map fun (n : Nat) => lo + (n : Int)

/-- The cubes whose middle is in the box, faces included. -/
def boxCells (b : Box) : List GridPt :=
  let line (lo hi : Q) : List Int := intsBetween (lo - 1 / 2).ceil (hi - 1 / 2).floor
  (line b.lo.x b.hi.x).flatMap fun i => (line b.lo.y b.hi.y).flatMap fun j =>
    (line b.lo.z b.hi.z).map fun k => (i, j, k)

/-- The same list with repeated cubes removed. -/
def dedupe (cells : List GridPt) : List GridPt :=
  (cells.foldl (fun (acc : Std.HashSet GridPt × List GridPt) c =>
    if acc.1.contains c then acc else (acc.1.insert c, c :: acc.2)) ({}, [])).2.reverse

/-- The bubble at its real size for this height. -/
def placeAt (height : Q) (b : Bubble) : Bubble := b.place height

/-- The cubes inside one bubble that is already at its real size. -/
def bubbleCells (b : Bubble) : List GridPt :=
  (boxCells b.box).filter fun g => b.contains g.centre

/-- The cubes inside any bubble of the model, at this height. -/
def targetCells (m : BubbleModel) (height : Q) : List GridPt :=
  dedupe ((m.bubbles.map (placeAt height)).flatMap bubbleCells)

/-- The cubes inside one block. An axis-aligned block always has 45. -/
def poseCells (p : Pose) : List GridPt :=
  (boxCells p.box).filter fun g => p.contains g.centre

/-- The cubes inside any block of the plan. -/
def blockCells (plan : List Pose) : List GridPt :=
  dedupe (plan.flatMap poseCells)

/-- Example: one bubble, a ball of height 1 with its bottom on the ground. -/
def ballModel : BubbleModel :=
  { name := "ball"
    bubbles := [{ label := "ball", tags := [], center := ⟨0, 0, 1 / 2⟩, semi := ⟨1 / 2, 1 / 2, 1 / 2⟩ }] }

/-- Example: a flat block filling cubes 0-14 along x, 0-2 along y and level 0. -/
def flatBlock : Pose := ⟨.flat, .id, ⟨15 / 2, 3 / 2, 1 / 2⟩⟩

/-- Example: a block far from the ball. -/
def farBlock : Pose := ⟨.flat, .id, ⟨100, 3 / 2, 1 / 2⟩⟩

/-- Example: a block whose end is in the ball but whose middle is not. -/
def endBlock : Pose := ⟨.flat, .id, ⟨7, 0, 1 / 2⟩⟩

#guard intsBetween 2 4 == [2, 3, 4]
#guard intsBetween 4 2 == []
#guard dedupe [(1, 0, 0), (2, 0, 0), (1, 0, 0)] == [(1, 0, 0), (2, 0, 0)]
-- The ball at height 2 has 8 cubes, and one of them is (-1, -1, 0).
#guard (targetCells ballModel 2).length == 8
#guard (targetCells ballModel 2).contains (-1, -1, 0)
#guard !(targetCells ballModel 2).contains (5, 5, 5)
-- At height 6 it has 136.
#guard (targetCells ballModel 6).length == 136
-- The egg at height 30 has the 5152 cubes that egg.json promises.
#guard (targetCells BubbleModel.egg 30).length == 5152
-- A block has 45 cubes, at any offset, and two copies of it still have 45.
#guard (blockCells [flatBlock]).length == 45
#guard (blockCells [flatBlock, flatBlock]).length == 45
#guard (blockCells [⟨.flat, .id, ⟨8, 7 / 4, 1 / 3⟩⟩]).length == 45
-- Only cubes above the ground count: half a ball of radius 2 has 16.
#guard
  let foot : Bubble := { label := "foot", tags := [], center := ⟨0, 0, 0⟩, semi := ⟨2, 2, 2⟩ }
  let cells := bubbleCells foot
  cells.length == 16 && cells.all (fun g => g.2.2 ≥ 0)

end KaplaSemantics
