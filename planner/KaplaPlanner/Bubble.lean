import Std.Data.HashSet
import KaplaPlanner.Inside
import KaplaPlanner.FastInside

/-! # Working with bubbles: scale, bounds, allowed cells

Untrusted helpers for the design search (DESIGN.md §3.2, §3.3). Safety does not depend on
them: every design passes `insideBubbles`, which is proven correct. -/

namespace KaplaPlanner
open KaplaCore

/-- The bubbles of a target (empty if the target is not given by bubbles). -/
def targetBubbles (t : TargetSpec) : List Bubble :=
  match t.shape with
  | .bubbles m => m.bubbles
  | _ => []

/-- Scale the bubble by `s` about the origin, then move it by `shift`. Unlike
`Bubble.place`, the shift may also go up or down (the planner sinks a target into the ground,
see `placeTarget`). -/
def placeBubble (s : Q) (shift : Q3) (b : Bubble) : Bubble :=
  { b with center := (b.center.scale s).add shift, semi := b.semi.scale s }

#guard
  let b2 := placeBubble 2 ⟨5, 0, 0⟩ (ball "b" ⟨0, 0, 0⟩ 10)
  b2.contains ⟨25, 0, 0⟩ && !b2.contains ⟨26, 0, 0⟩

/-- The box around the bubble, or `none` if a half-width is 0 or less (such a bubble
contains nothing). -/
def bubbleBounds (b : Bubble) : Option Box :=
  if 0 < b.semi.x && 0 < b.semi.y && 0 < b.semi.z then some b.box else none

-- the box stops at the ground
#guard bubbleBounds (ball "b" ⟨0, 0, 0⟩ 10) == some ⟨⟨-10, -10, 0⟩, ⟨10, 10, 10⟩⟩
#guard bubbleBounds (ellipsoid "x" ⟨0, 0, 0⟩ 1 1 0) == none

/-- Lowest corners (in units, multiples of 4) of the world cubes that may meet `[lo, hi]`. -/
def cellSpan (lo hi : Q) : List Int :=
  let a := (lo / blockThickness).floor - 1
  let z := (hi / blockThickness).ceil
  (intRange a (z - a + 1).toNat).map (· * (cubeSide : Int))

/-- A world cube, given by its lowest corner in units (all three a multiple of 4). World
cubes have the side of one block thickness and are fixed in space; the planner uses them to measure the target. -/
abbrev Cell := Int × Int × Int

/-- All allowed world cubes (DESIGN.md §3.3): cubes that lie inside the bubbles (`cellInside`:
inside one bubble, or cut into pieces that each are), and that are above the ground. Bubbles
with a half-width of 0 or less are ignored. -/
def allowedCells (bs : List Bubble) : Std.HashSet Cell := Id.run do
  let arr := prepareBubbles bs
  let mut out : Std.HashSet Cell := {}
  for b in bs do
    match bubbleBounds b with
    | some bx =>
      for i in cellSpan bx.lo.x bx.hi.x do
        for j in cellSpan bx.lo.y bx.hi.y do
          for k in cellSpan bx.lo.z bx.hi.z do
            -- `cubeInside` is `cellInside`, in whole numbers
            if k ≥ 0 && !out.contains (i, j, k) && cubeInside arr i j k then
              out := out.insert (i, j, k)
    | none => pure ()
  return out

/-- The 6 neighbours of a cell. -/
def neighbours (c : Cell) : List Cell :=
  let (i, j, k) := c
  [(i+4, j, k), (i-4, j, k), (i, j+4, k), (i, j-4, k), (i, j, k+4), (i, j, k-4)]

/-- Surface cells: allowed cells with at least one neighbour that is not allowed. Cells
on the ground (k = 0) count as surface only if a side or top neighbour is not allowed. -/
def surfaceCells (allowed : Std.HashSet Cell) : List Cell :=
  allowed.toList.filter fun c =>
    (neighbours c).any fun n => n.2.2 ≥ 0 && !allowed.contains n

-- every allowed cell passes the proven check
#guard
  let bs := [ball "b" ⟨0, 0, 50⟩ 50]
  (allowedCells bs).toList.all fun (i, j, k) => cellInside bs i j k
-- also where two bubbles overlap
#guard (allowedCells twoBalls).toList.all fun (i, j, k) => cellInside twoBalls i j k

end KaplaPlanner
