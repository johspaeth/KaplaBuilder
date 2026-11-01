import KaplaPlanner.Bubble

/-! # Test targets made of bubbles

Hand-made targets, each testing one difficulty (DESIGN.md §6). Sizes are in block units (one block thickness) at scale 1;
the planner chooses its own scale. -/

namespace KaplaPlanner.Fixtures
open KaplaCore

/-- A target from its bubbles (the shape field is only a placeholder here). -/
def ofBubbles (bs : List Bubble) : TargetSpec := TargetSpec.ofBubbles ⟨"fixture", bs⟩

/-- A ball resting on the ground. The simplest case: a ring, then a lid. -/
def sphere : TargetSpec := ofBubbles [ball "ball" ⟨0, 0, 13⟩ 13]

/-- Three stacked balls: the outline narrows and widens again (overhangs, inner support). -/
def snowman : TargetSpec := ofBubbles
  [ball "bottom" ⟨0, 0, 10⟩ 10, ball "middle" ⟨0, 0, 25⟩ 7,
   ball "head" ⟨0, 0, 73 / 2⟩ (9 / 2)]

/-- A tall thin ellipsoid: needs blocks on edge or upright. -/
def spire : TargetSpec := ofBubbles [ellipsoid "spire" ⟨0, 0, 25⟩ 4 4 25]

/-- A duck: body, a head that sticks out, and a thin beak that vanishes at small scales. -/
def duck : TargetSpec := ofBubbles
  [ellipsoid "body" ⟨0, 0, 8⟩ 13 8 8, ball "head" ⟨10, 0, 19⟩ 5,
   ellipsoid "beak" ⟨17, 0, 19⟩ 3 (3 / 2) 1]

/-- Two towers and a bridge: separate parts, and a span between them. -/
def gate : TargetSpec := ofBubbles
  [ellipsoid "left tower" ⟨-15, 0, 19⟩ 5 5 19,
   ellipsoid "right tower" ⟨15, 0, 19⟩ 5 5 19,
   ellipsoid "bridge" ⟨0, 0, 35⟩ 22 (9 / 2) 4]

/-- All test targets with their names. -/
def all : List (String × TargetSpec) :=
  [("sphere", sphere), ("snowman", snowman), ("spire", spire),
   ("duck", duck), ("gate", gate)]

-- every bubble of every target is bounded
#guard all.all fun (_, t) => (targetBubbles t).all fun b => (bubbleBounds b).isSome

/-- An upper limit for the volume of a bubble: `4/3 · 22/7 · a · b · c` (22/7 is more than π). -/
def volumeAbove (b : Bubble) : Q := 4 / 3 * (22 / 7) * b.semi.x * b.semi.y * b.semi.z

/-- A lower limit for the volume of a bubble: `4/3 · 3 · a · b · c` (3 is less than π). -/
def volumeBelow (b : Bubble) : Q := 4 / 3 * 3 * b.semi.x * b.semi.y * b.semi.z

/-- Volume of one grid cell. -/
def cellVolume : Q := blockThickness ^ 3

/-- Sanity checks on the allowed cells of a target at scale `s`:
- every allowed cell passes the proven check `cellInside`;
- the allowed cells do not hold more volume than the bubbles (they lie inside);
- they hold at least a third of the largest bubble (the grid loses only a thin rim);
- surface cells exist and are allowed cells. -/
def allowedOk (t : TargetSpec) (s : Q) : Bool :=
  let bs := (targetBubbles t).map (placeBubble s ⟨0, 0, 0⟩)
  let allowed := allowedCells bs
  let n : Q := (allowed.size : Q)
  let surface := surfaceCells allowed
  allowed.toList.all (fun (i, j, k) => cellInside bs i j k) &&
  n * cellVolume ≤ (bs.map volumeAbove).foldl (· + ·) 0 &&
  3 * n * cellVolume ≥ ((bs.map volumeBelow).foldl max 0) &&
  !surface.isEmpty && surface.all allowed.contains

#guard all.all fun (_, t) => allowedOk t 1

/-- Number of allowed cells of the bubble named `part`, at scale `s`. -/
def cellsOfPart (t : TargetSpec) (part : String) (s : Q) : Nat :=
  (allowedCells (((targetBubbles t).filter (·.label == part)).map (placeBubble s ⟨0, 0, 0⟩))).size

-- The beak (2 high) has almost no room at scale 1, but plenty at scale 3: the planner
-- must choose the scale with the thin parts in mind.
#guard cellsOfPart duck "beak" 1 < 10 && cellsOfPart duck "beak" 3 > 100

end KaplaPlanner.Fixtures
