import KaplaPlanner.Grid

/-! # Strictly inside the target

The planner may only place blocks strictly inside the target's bubbles. This file has the
check, `insideBubbles`. Its promise, proven in `Proofs.lean` (statement in
`specs/KaplaSpecs/Planner.lean`): if the check accepts, **every point** of every block lies
inside some bubble. Not just the corners: every point.

How the check works: a block is cut into cubes of one block thickness: 15 × 3 × 1
cubes for a flat block. A cube passes if its 8 corners lie inside one and the same bubble.
If not, it is cut into 8 smaller cubes (half the side), and passes if each of those passes;
this is done at most twice (`splitDepth`). So a block may reach from one bubble into another
where they overlap, as long as no part of it is outside all bubbles. A block passes if all
its cubes pass. -/

namespace KaplaPlanner
open KaplaCore

/-- The cube (side one block thickness = 4 grid units) whose lowest corner is at `(i, j, k)`
grid units, as a box in block units. -/
def cellBox (i j k : Int) : Box :=
  let q (v : Int) : Q := (v : Q) * unit
  ⟨⟨q i, q j, q k⟩, ⟨q (i + cubeSide), q (j + cubeSide), q (k + cubeSide)⟩⟩

/-- The box's 8 corners all lie inside the same bubble, for some bubble in the list. -/
def boxInOne (bs : List Bubble) (bx : Box) : Bool :=
  bs.any fun b => bx.corners.all fun p => b.contains p

/-- The two halves of the interval from `lo` to `hi`. -/
def halves (lo hi : Q) : List (Q × Q) := [(lo, (lo + hi) / 2), ((lo + hi) / 2, hi)]

/-- The 8 boxes you get by cutting the box in half along x, along y and along z. -/
def boxOctants (bx : Box) : List Box :=
  (halves bx.lo.x bx.hi.x).flatMap fun (x0, x1) =>
    (halves bx.lo.y bx.hi.y).flatMap fun (y0, y1) =>
      (halves bx.lo.z bx.hi.z).map fun (z0, z1) => ⟨⟨x0, y0, z0⟩, ⟨x1, y1, z1⟩⟩

/-- The box lies inside the bubbles: its corners lie in one bubble, or (up to `depth` more
times) each of its 8 halves lies inside the bubbles. -/
def boxInside (bs : List Bubble) (bx : Box) : Nat → Bool
  | 0 => boxInOne bs bx
  | depth + 1 => boxInOne bs bx || (boxOctants bx).all fun o => boxInside bs o depth

/-- How many times a cube may be cut in 8: twice, down to a quarter of a block thickness
(one grid unit). -/
def splitDepth : Nat := 2

/-- The cube lies inside the bubbles (see `boxInside`). -/
def cellInside (bs : List Bubble) (i j k : Int) : Bool :=
  boxInside bs (cellBox i j k) splitDepth

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

/-- A ball with centre `c` and radius `r`, as a bubble without tags. -/
def ball (label : String) (c : Q3) (r : Q) : Bubble := ⟨label, [], c, ⟨r, r, r⟩⟩

/-- An ellipsoid with centre `c` and half-widths `rx`, `ry`, `rz`, as a bubble without tags. -/
def ellipsoid (label : String) (c : Q3) (rx ry rz : Q) : Bubble := ⟨label, [], c, ⟨rx, ry, rz⟩⟩

/-- Example: a ball of radius 13, centred 13 above the ground (in block units). -/
def exampleBall : Bubble := ball "ball" ⟨0, 0, 13⟩ 13

-- a flat block through the middle of the ball fits (it is 15 long)
#guard insideBubbles [exampleBall] [⟨.flatX, -30, -6, 48⟩]
-- the same block moved 8 along x sticks out of the ball
#guard !insideBubbles [exampleBall] [⟨.flatX, -62, -6, 48⟩]
-- a block on the ground is outside: the ball only touches the ground at one point
#guard !insideBubbles [exampleBall] [⟨.flatX, -30, -6, 0⟩]

/-- Example: two balls of radius 8 whose centres are 10 apart; they overlap. -/
def twoBalls : List Bubble := [ball "left" ⟨-5, 0, 8⟩ 8, ball "right" ⟨5, 0, 8⟩ 8]

-- a block from x = -7.5 to 7.5 fits in neither ball alone, but in the two together
#guard insideBubbles twoBalls [⟨.flatX, -30, -6, 28⟩]
#guard !insideBubbles [twoBalls[0]!] [⟨.flatX, -30, -6, 28⟩]
#guard !insideBubbles [twoBalls[1]!] [⟨.flatX, -30, -6, 28⟩]
-- one that reaches past the outer side of a ball is still refused
#guard !insideBubbles twoBalls [⟨.flatX, -6, -6, 28⟩]

end KaplaPlanner
