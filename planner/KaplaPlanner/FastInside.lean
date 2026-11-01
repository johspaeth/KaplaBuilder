import KaplaPlanner.Grid

/-! # A fast inside test for the design search

The designer checks millions of cubes. `Bubble.contains` uses exact fractions (`Rat`), which
is slow: every step reduces a fraction. Here the same test is done with whole numbers.

For a grid point `n` (in units) on one axis, the bubble's term is `((n * unit - c) / s)²`.
Over a common denominator this is `(n * a - b)² / d²`. Multiply the three terms by one
number `m` that all `d²` divide, and the test "sum of the terms ≤ 1" becomes
"`w_x (x a_x - b_x)² + w_y (…)² + w_z (…)² ≤ m`", in whole numbers. The result is exactly the
same as `Bubble.contains`.

A cube has its 8 corners inside the bubble exactly when the sum of the larger end term on
each axis is at most `m`: each term depends on one axis only, so the worst corner takes the
worst end on every axis.

Untrusted: only the design search uses this. Every design is checked again by
`insideBubbles`, which is proven. The `#guard`s below and in `Tests.lean` compare the two. -/

namespace KaplaPlanner
open KaplaCore

/-- One axis of a bubble, in whole numbers: the term of grid point `n` is `w * (n * a - b)²`. -/
structure AxisTerm where
  a : Int
  b : Int
  w : Int
  deriving Repr, Inhabited

/-- The term of grid point `n` on this axis. -/
@[inline] def AxisTerm.at (t : AxisTerm) (n : Int) : Int :=
  let d := n * t.a - t.b
  t.w * (d * d)

/-- The larger of the terms at the two ends of a cube, `n` and `n + cubeSide`. -/
@[inline] def AxisTerm.worst (t : AxisTerm) (n : Int) : Int :=
  max (t.at n) (t.at (n + cubeSide))

/-- A bubble prepared for whole-number tests on grid points. -/
structure IntBubble where
  x : AxisTerm
  y : AxisTerm
  z : AxisTerm
  /-- The bound: a grid point is inside when its three terms add up to at most `m`. -/
  m : Int
  deriving Repr, Inhabited

/-- `(n * unit - c) / s` as `(n * a - b) / d`: returns `(a, b, d)` with `d > 0`. -/
def axisParts (c s : Q) : Int × Int × Nat :=
  let α := unit / s
  let β := c / s
  let d := Nat.lcm α.den β.den
  (α.num * (d / α.den : Nat), β.num * (d / β.den : Nat), d)

/-- Prepare a bubble. `none` if a half-width is 0 or less (such a bubble contains nothing). -/
def IntBubble.ofBubble (b : Bubble) : Option IntBubble :=
  if 0 < b.semi.x && 0 < b.semi.y && 0 < b.semi.z then
    let (ax, bx, dx) := axisParts b.center.x b.semi.x
    let (ay, by_, dy) := axisParts b.center.y b.semi.y
    let (az, bz, dz) := axisParts b.center.z b.semi.z
    let m : Nat := Nat.lcm (dx * dx) (Nat.lcm (dy * dy) (dz * dz))
    some { x := ⟨ax, bx, (m / (dx * dx) : Nat)⟩, y := ⟨ay, by_, (m / (dy * dy) : Nat)⟩,
           z := ⟨az, bz, (m / (dz * dz) : Nat)⟩, m := m }
  else none

/-- Prepare all bubbles; those that contain nothing are left out. -/
def prepareBubbles (bs : List Bubble) : Array IntBubble :=
  (bs.filterMap IntBubble.ofBubble).toArray

/-- The grid point `(i, j, k)` (in units) is inside the bubble. -/
@[inline] def IntBubble.containsPoint (b : IntBubble) (i j k : Int) : Bool :=
  b.x.at i + b.y.at j + b.z.at k ≤ b.m

/-- The cube with lowest corner `(i, j, k)` has all 8 corners inside the bubble
(same as `(cellBox i j k).corners.all b.contains`). -/
@[inline] def IntBubble.containsCube (b : IntBubble) (i j k : Int) : Bool :=
  b.x.worst i + b.y.worst j + b.z.worst k ≤ b.m

/-- The cube at `(i, j, k)` has its 8 corners inside one bubble (same as `cellInside`). -/
@[inline] def cubeInside (bs : Array IntBubble) (i j k : Int) : Bool :=
  bs.any fun b => b.containsCube i j k

-- the whole-number tests agree with `Bubble.contains` and `cellInside`, also for bubbles
-- with fractional centres and half-widths
private def testBubbles : List Bubble :=
  [⟨"a", [], ⟨0, 0, 13⟩, ⟨13, 13, 13⟩⟩, ⟨"b", [], ⟨7 / 3, -5 / 2, 9 / 4⟩, ⟨11 / 3, 5 / 2, 17 / 7⟩⟩,
   ⟨"c", [], ⟨1, 1, 1⟩, ⟨0, 1, 1⟩⟩]

#guard testBubbles.all fun b =>
  (List.range 25).all fun i => (List.range 17).all fun j => (List.range 17).all fun k =>
    let (i, j, k) : Int × Int × Int := (2 * i - 24, j - 8, 2 * k - 6)
    let fast := match IntBubble.ofBubble b with
      | some fb => fb.containsPoint i j k
      | none => false
    fast == b.contains ⟨i * unit, j * unit, k * unit⟩

#guard
  let fbs := prepareBubbles testBubbles
  (List.range 30).all fun i => (List.range 20).all fun j => (List.range 20).all fun k =>
    let (i, j, k) : Int × Int × Int := (i - 15, j - 10, k - 4)
    cubeInside fbs i j k ==
      testBubbles.any fun b =>
        (Box.corners ⟨⟨i * unit, j * unit, k * unit⟩,
          ⟨(i + 4) * unit, (j + 4) * unit, (k + 4) * unit⟩⟩).all b.contains

end KaplaPlanner
