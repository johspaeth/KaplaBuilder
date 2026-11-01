import KaplaPlanner.Grid

/-! # Strictly inside the target

The planner may only place blocks strictly inside the target's bubbles. This file has the
check, `insideBubbles`. Its promise, proven in `Proofs.lean` (statement in
`specs/KaplaSpecs/Planner.lean`): if the check accepts, **every point** of every block lies
inside some bubble. Not just the corners: every point.

How the check works: a block is cut into cubes of one block thickness (7.8 mm): 15 × 3 × 1
cubes for a flat block. A cube passes if its 8 corners lie inside one and the same bubble.
A block passes if all its cubes pass. -/

namespace KaplaPlanner
open KaplaCore

/-- The cube (side 7.8 mm = 4 units) whose lowest corner is at `(i, j, k)` units, as a box
in mm. -/
def cellBox (i j k : Int) : Box :=
  let mm (v : Int) : Q := (v : Q) * unit
  ⟨⟨mm i, mm j, mm k⟩, ⟨mm (i + cubeSide), mm (j + cubeSide), mm (k + cubeSide)⟩⟩

/-- The cube's 8 corners all lie inside the same bubble, for some bubble in the list. -/
def cellInside (bs : List Bubble) (i j k : Int) : Bool :=
  bs.any fun b => (cellBox i j k).corners.all fun p => decide (b.contains p)

/-- The integers `a, a+d, …, a+(n-1)·d`. -/
def intRange (a : Int) (n : Nat) (d : Nat := 1) : List Int :=
  (List.range n).map fun (m : Nat) => a + (d * m : Nat)

/-- The lowest corners of the cubes the block is cut into. -/
def GridBlock.cells (b : GridBlock) : List (Int × Int × Int) :=
  (intRange b.x b.orient.cubes.1 cubeSide).flatMap fun i =>
    (intRange b.y b.orient.cubes.2.1 cubeSide).flatMap fun j =>
      (intRange b.z b.orient.cubes.2.2 cubeSide).map fun k => (i, j, k)

/-- **The check**: every cell of every block lies inside one bubble. -/
def insideBubbles (bs : List Bubble) (design : List GridBlock) : Bool :=
  design.all fun blk => blk.cells.all fun (i, j, k) => cellInside bs i j k

-- a flat block is cut into 15 × 3 × 1 = 45 cubes
#guard (GridBlock.mk .flatX 0 0 0).cells.length == 45

/-- Example: a ball of radius 100 mm, centred 100 mm above the ground. -/
def exampleBall : Bubble := Bubble.ball "ball" ⟨0, 0, 100⟩ 100

-- a flat block through the middle of the ball fits (it is 117 mm long)
#guard insideBubbles [exampleBall] [⟨.flatX, -30, -6, 48⟩]
-- the same block moved 62.4 mm along x sticks out of the ball
#guard !insideBubbles [exampleBall] [⟨.flatX, -62, -6, 48⟩]
-- a block on the ground is outside: the ball only touches the ground at one point
#guard !insideBubbles [exampleBall] [⟨.flatX, -30, -6, 0⟩]

end KaplaPlanner
