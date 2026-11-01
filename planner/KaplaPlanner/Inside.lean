import KaplaPlanner.Grid

/-! # Strictly inside the target

The planner may only place blocks strictly inside the target's bubbles. This file has the
check, `insideBubbles`. Its promise, proven in `Proofs.lean` (statement in
`specs/KaplaSpecs/Planner.lean`): if the check accepts, **every point** of every block lies
inside some bubble. Not just the corners: every point.

How the check works: a block fills whole grid cells. A cell passes if its 8 corners lie
inside one and the same bubble. A block passes if all its cells pass. -/

namespace KaplaPlanner
open KaplaCore

/-- Grid cell `(i, j, k)` as a box in mm: from `(i, j, k)·7.8` to `(i+1, j+1, k+1)·7.8`. -/
def cellBox (i j k : Int) : Box :=
  let h := blockThickness
  ⟨⟨(i : Q) * h, (j : Q) * h, (k : Q) * h⟩,
   ⟨((i + 1 : Int) : Q) * h, ((j + 1 : Int) : Q) * h, ((k + 1 : Int) : Q) * h⟩⟩

/-- The cell's 8 corners all lie inside the same bubble, for some bubble in the list. -/
def cellInside (bs : List Bubble) (i j k : Int) : Bool :=
  bs.any fun b => (cellBox i j k).corners.all fun p => decide (b.contains p)

/-- The integers `a, a+1, …, a+n-1`. -/
def intRange (a : Int) (n : Nat) : List Int := (List.range n).map fun (m : Nat) => a + (m : Int)

/-- All grid cells the block fills. -/
def GridBlock.cells (b : GridBlock) : List (Int × Int × Int) :=
  (intRange b.x b.orient.size.1).flatMap fun i => (intRange b.y b.orient.size.2.1).flatMap
    fun j => (intRange b.z b.orient.size.2.2).map fun k => (i, j, k)

/-- **The check**: every cell of every block lies inside one bubble. -/
def insideBubbles (bs : List Bubble) (design : List GridBlock) : Bool :=
  design.all fun blk => blk.cells.all fun (i, j, k) => cellInside bs i j k

-- a flat block fills 15 × 3 × 1 = 45 cells
#guard (GridBlock.mk .flatX 0 0 0).cells.length == 45

/-- Example: a ball of radius 100 mm, centred 100 mm above the ground. -/
def exampleBall : Bubble := Bubble.ball "ball" ⟨0, 0, 100⟩ 100

-- a flat block through the middle of the ball fits (it is 117 mm long)
#guard insideBubbles [exampleBall] [⟨.flatX, -8, -2, 12⟩]
-- the same block one cell further along x sticks out of the ball
#guard !insideBubbles [exampleBall] [⟨.flatX, -16, -2, 12⟩]
-- a block on the ground is outside: the ball only touches the ground at one point
#guard !insideBubbles [exampleBall] [⟨.flatX, -8, -2, 0⟩]

end KaplaPlanner
