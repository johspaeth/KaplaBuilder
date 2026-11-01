import KaplaPlanner.Bubble

/-! # Test targets made of bubbles

Hand-made targets, each testing one difficulty (DESIGN.md §6). Sizes are in mm at scale 1;
the planner chooses its own scale. -/

namespace KaplaPlanner.Fixtures
open KaplaCore

/-- A target from its bubbles (the shape field is only a placeholder here). -/
def ofBubbles (bs : List Bubble) : TargetSpec :=
  { shape := .box ⟨⟨0, 0, 0⟩, ⟨0, 0, 0⟩⟩, bubbles := bs }

/-- A ball resting on the ground. The simplest case: a ring, then a lid. -/
def sphere : TargetSpec := ofBubbles [Bubble.ball "ball" ⟨0, 0, 100⟩ 100]

/-- Three stacked balls: the outline narrows and widens again (overhangs, inner support). -/
def snowman : TargetSpec := ofBubbles
  [Bubble.ball "bottom" ⟨0, 0, 80⟩ 80, Bubble.ball "middle" ⟨0, 0, 200⟩ 55,
   Bubble.ball "head" ⟨0, 0, 285⟩ 35]

/-- A tall thin ellipsoid: needs blocks on edge or upright. -/
def spire : TargetSpec := ofBubbles [Bubble.ellipsoid "spire" ⟨0, 0, 200⟩ 30 30 200]

/-- An ellipsoid leaning by a 3-4-5 angle (about 37° from upright, turned about x). -/
def leaning : TargetSpec := ofBubbles
  [⟨"leaning", ⟨0, 90, 125⟩,
    ⟨1 / 40, 0, 0⟩,                       -- across, radius 40
    ⟨0, (3 / 5) / 150, (4 / 5) / 150⟩,     -- along the lean, radius 150
    ⟨0, (-4 / 5) / 40, (3 / 5) / 40⟩⟩]     -- across, radius 40

/-- A duck: body, a head that sticks out, and a thin beak that vanishes at small scales. -/
def duck : TargetSpec := ofBubbles
  [Bubble.ellipsoid "body" ⟨0, 0, 60⟩ 100 60 60, Bubble.ball "head" ⟨80, 0, 150⟩ 40,
   Bubble.ellipsoid "beak" ⟨130, 0, 150⟩ 25 12 8]

/-- Two towers and a bridge: separate parts, and a span between them. -/
def gate : TargetSpec := ofBubbles
  [Bubble.ellipsoid "left tower" ⟨-120, 0, 150⟩ 40 40 150,
   Bubble.ellipsoid "right tower" ⟨120, 0, 150⟩ 40 40 150,
   Bubble.ellipsoid "bridge" ⟨0, 0, 270⟩ 170 35 30]

/-- All test targets with their names. -/
def all : List (String × TargetSpec) :=
  [("sphere", sphere), ("snowman", snowman), ("spire", spire), ("leaning", leaning),
   ("duck", duck), ("gate", gate)]

-- every bubble of every target is bounded
#guard all.all fun (_, t) => t.bubbles.all fun b => (bubbleBounds b).isSome

/-- An upper limit for the volume of a bubble: `4/3 · 22/7 / |det|` (22/7 is more than π). -/
def volumeAbove (b : Bubble) : Q := 4 / 3 * (22 / 7) / (det3 b.u1 b.u2 b.u3).abs

/-- A lower limit for the volume of a bubble: `4/3 · 3 / |det|` (3 is less than π). -/
def volumeBelow (b : Bubble) : Q := 4 / 3 * 3 / (det3 b.u1 b.u2 b.u3).abs

/-- Volume of one grid cell. -/
def cellVolume : Q := blockThickness ^ 3

/-- Sanity checks on the allowed cells of a target at scale `s`:
- every allowed cell passes the proven check `cellInside`;
- the allowed cells do not hold more volume than the bubbles (they lie inside);
- they hold at least a third of the largest bubble (the grid loses only a thin rim);
- surface cells exist and are allowed cells. -/
def allowedOk (t : TargetSpec) (s : Q) : Bool :=
  let bs := t.bubbles.map (placeBubble s ⟨0, 0, 0⟩)
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
  (allowedCells ((t.bubbles.filter (·.part == part)).map (placeBubble s ⟨0, 0, 0⟩))).size

-- The beak (16 mm high) has almost no room at scale 1, but plenty at scale 3: the planner
-- must choose the scale with the thin parts in mind.
#guard cellsOfPart duck "beak" 1 < 10 && cellsOfPart duck "beak" 3 > 100

-- A leaning bubble: cells high up are shifted along y (the lean), cells low down are not.
#guard
  let allowed := (allowedCells leaning.bubbles).toList
  let ysAt (k : Int) := (allowed.filter (·.2.2 == k)).map (·.2.1)
  match ysAt 8 |>.max?, ysAt 120 |>.min? with
  | some lowTop, some highBottom => highBottom > lowTop
  | _, _ => false

end KaplaPlanner.Fixtures
