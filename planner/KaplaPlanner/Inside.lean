import KaplaPlanner.Grid

/-! # Strictly inside the target

The planner may only place blocks strictly inside the target's bubbles. This file has the
check, `insideBubbles`. Its promise, proven in `Proofs.lean` (statement in
`specs/KaplaSpecs/Planner.lean`): if the check accepts, **every point** of every block lies
inside some bubble. Not just the corners: every point.

How the check works: a block is cut into cubes of one block thickness: 15 × 3 × 1
cubes for a flat block. A cube passes if its 8 corners lie inside one and the same bubble.
A block passes if all its cubes pass. -/

namespace KaplaPlanner
open KaplaCore

/-- The cube (side one block thickness = 4 grid units) whose lowest corner is at `(i, j, k)`
grid units, as a box in block units. -/
def cellBox (i j k : Int) : Box :=
  let q (v : Int) : Q := (v : Q) * unit
  ⟨⟨q i, q j, q k⟩, ⟨q (i + cubeSide), q (j + cubeSide), q (k + cubeSide)⟩⟩

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

/-- Example: a ball of radius 13, centred 13 above the ground (in block units). -/
def exampleBall : Bubble := Bubble.ball "ball" ⟨0, 0, 13⟩ 13

-- a flat block through the middle of the ball fits (it is 15 long)
#guard insideBubbles [exampleBall] [⟨.flatX, -30, -6, 48⟩]
-- the same block moved 8 along x sticks out of the ball
#guard !insideBubbles [exampleBall] [⟨.flatX, -62, -6, 48⟩]
-- a block on the ground is outside: the ball only touches the ground at one point
#guard !insideBubbles [exampleBall] [⟨.flatX, -30, -6, 0⟩]

end KaplaPlanner
