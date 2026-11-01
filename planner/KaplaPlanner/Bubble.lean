import Std.Data.HashSet
import KaplaPlanner.Inside

/-! # Working with bubbles: scale, bounds, allowed cells

Untrusted helpers for the design search (DESIGN.md §3.2, §3.3). Safety does not depend on
them: every design passes `insideBubbles`, which is proven correct. -/

namespace KaplaPlanner
open KaplaCore

/-- Scale the bubble by `s` about the origin, then move it by `shift`. A point `x` is in the
new bubble exactly when `(x − shift) / s` is in the old one. -/
def placeBubble (s : Q) (shift : Q3) (b : Bubble) : Bubble :=
  { b with center := (b.center.scale s).add shift
           u1 := b.u1.scale (1 / s), u2 := b.u2.scale (1 / s), u3 := b.u3.scale (1 / s) }

#guard
  let b := Bubble.ball "b" ⟨0, 0, 0⟩ 10
  let b2 := placeBubble 2 ⟨5, 0, 0⟩ b
  decide (b2.contains ⟨25, 0, 0⟩) && !decide (b2.contains ⟨26, 0, 0⟩)

/-- 3 × 3 matrix with rows `r1`, `r2`, `r3`: its determinant. -/
def det3 (r1 r2 r3 : Q3) : Q :=
  r1.x * (r2.y * r3.z - r2.z * r3.y) - r1.y * (r2.x * r3.z - r2.z * r3.x) +
  r1.z * (r2.x * r3.y - r2.y * r3.x)

/-- A box that surely contains the bubble, or `none` if the bubble is not bounded (its three
vectors are not independent).

Why it is safe: inside points are `x = c + M v` with `|v| ≤ 1`, where `M` is the inverse of
the matrix with rows `u₁, u₂, u₃`. So `|x_k − c_k|` is at most the length of row `k` of `M`,
and that is at most the sum of the absolute values in that row. -/
def bubbleBounds (b : Bubble) : Option Box :=
  let (a, c, d) := (b.u1, b.u2, b.u3)
  let D := det3 a c d
  if D == 0 then none else
  -- rows of the inverse (adjugate / determinant)
  let m1 : Q3 := ⟨c.y * d.z - c.z * d.y, a.z * d.y - a.y * d.z, a.y * c.z - a.z * c.y⟩
  let m2 : Q3 := ⟨c.z * d.x - c.x * d.z, a.x * d.z - a.z * d.x, a.z * c.x - a.x * c.z⟩
  let m3 : Q3 := ⟨c.x * d.y - c.y * d.x, a.y * d.x - a.x * d.y, a.x * c.y - a.y * c.x⟩
  let r (m : Q3) : Q := (m.x.abs + m.y.abs + m.z.abs) / D.abs
  let h : Q3 := ⟨r m1, r m2, r m3⟩
  some ⟨b.center.sub h, b.center.add h⟩

-- a ball of radius 10: the box is exactly ±10
#guard bubbleBounds (Bubble.ball "b" ⟨0, 0, 0⟩ 10) == some ⟨⟨-10, -10, -10⟩, ⟨10, 10, 10⟩⟩
-- a flat bubble (one vector zero) is not bounded
#guard bubbleBounds (Bubble.mk "x" ⟨0, 0, 0⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, 0, 0⟩) == none

/-- Lowest corners (in units, multiples of 4) of the world cubes that may meet `[lo, hi]`. -/
def cellSpan (lo hi : Q) : List Int :=
  let a := (lo / blockThickness).floor - 1
  let z := (hi / blockThickness).ceil
  (intRange a (z - a + 1).toNat).map (· * (cubeSide : Int))

/-- A world cube, given by its lowest corner in units (all three a multiple of 4). World
cubes are 7.8 mm and fixed in space; the planner uses them to measure the target. -/
abbrev Cell := Int × Int × Int

/-- All allowed world cubes (DESIGN.md §3.3): cubes whose 8 corners lie inside one bubble,
and that are above the ground. Unbounded bubbles are ignored. -/
def allowedCells (bs : List Bubble) : Std.HashSet Cell := Id.run do
  let mut out : Std.HashSet Cell := {}
  for b in bs do
    match bubbleBounds b with
    | none => pure ()
    | some bx =>
      for i in cellSpan bx.lo.x bx.hi.x do
        for j in cellSpan bx.lo.y bx.hi.y do
          for k in cellSpan bx.lo.z bx.hi.z do
            if k ≥ 0 && !out.contains (i, j, k) &&
                (cellBox i j k).corners.all (fun p => decide (b.contains p)) then
              out := out.insert (i, j, k)
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
  let bs := [Bubble.ball "b" ⟨0, 0, 50⟩ 50]
  (allowedCells bs).toList.all fun (i, j, k) => cellInside bs i j k

end KaplaPlanner
