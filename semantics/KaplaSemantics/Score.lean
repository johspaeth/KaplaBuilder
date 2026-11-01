import Std.Data.HashMap
import KaplaSemantics.Grid

/-! # How close a plan is to the target

A cube of a bubble is covered when a block fills it, or when it lies between two filled cubes of
that same bubble on one straight line along x, y or z. So the hollow middle of a tower counts as
built, but the gap between two ears does not. See `semantics/APPROACH.md` §4. -/

namespace KaplaSemantics

open KaplaCore

/-- A straight grid line: its direction (0, 1, 2 for x, y, z) and the two fixed coordinates. -/
abbrev GridLine := Nat × Int × Int

/-- The three lines through a cube, each with the cube's position along that line. -/
def linesThrough (g : GridPt) : List (GridLine × Int) :=
  let (i, j, k) := g
  [((0, j, k), i), ((1, i, k), j), ((2, i, j), k)]

/-- For each grid line with filled cubes on it: the first and the last filled position. -/
def filledSpans (filled : List GridPt) : Std.HashMap GridLine (Int × Int) :=
  filled.foldl (fun spans g => (linesThrough g).foldl (fun spans (line, t) =>
    match spans[line]? with
    | some (lo, hi) => spans.insert line (min lo t, max hi t)
    | none => spans.insert line (t, t)) spans) {}

/-- Does the cube lie from the first to the last filled position, on one of its three lines? A
filled cube itself passes, because it is on its own span. -/
def inSomeSpan (spans : Std.HashMap GridLine (Int × Int)) (g : GridPt) : Bool :=
  (linesThrough g).any fun (line, t) =>
    match spans[line]? with
    | some (lo, hi) => lo ≤ t && t ≤ hi
    | none => false

/-- The covered cubes of one bubble at its real size. `built` is every cube inside a block. -/
def coveredOfBubble (built : List GridPt) (b : Bubble) : List GridPt :=
  let spans := filledSpans (built.filter fun g => b.contains g.centre)
  (bubbleCells b).filter (inSomeSpan spans)

/-- The covered cubes of the whole model. Every one of them is inside some bubble. -/
def coveredCells (placed : List Bubble) (built : List GridPt) : List GridPt :=
  dedupe (placed.flatMap (coveredOfBubble built))

/-- The cubes inside blocks but inside no bubble. These stick out. -/
def extraCells (placed : List Bubble) (built : List GridPt) : List GridPt :=
  built.filter fun g => !placed.any (·.contains g.centre)

/-- The similarity number: covered cubes over target cubes plus cubes that stick out. It is 0
when nothing is covered, and 1 when nothing is missing and nothing sticks out. -/
def scoreOf (target covered extra : Nat) : Q :=
  if target + extra == 0 then 0 else (covered : Q) / ((target + extra : Nat) : Q)

/-- The similarity number of a plan against a model at a height. -/
def score (m : BubbleModel) (height : Q) (plan : List Pose) : Q :=
  let placed := m.bubbles.map (placeAt height)
  let built := blockCells plan
  scoreOf (targetCells m height).length (coveredCells placed built).length
    (extraCells placed built).length

/-- The share of one bubble at its real size that is covered. A bubble with no cubes gives 0. -/
def perBubble (built : List GridPt) (b : Bubble) : Q :=
  let total := (bubbleCells b).length
  if total == 0 then 0 else ((coveredOfBubble built b).length : Q) / (total : Q)

-- One block touching the ball: 1 of its cubes is inside, of 8 in the ball. This is the
-- example of APPROACH.md §6.
#guard score ballModel 2 [flatBlock] == 1 / 52
-- Nothing built scores 0, and no target and no blocks also scores 0.
#guard score ballModel 2 [] == 0
#guard scoreOf 0 0 0 == 0
-- A bubble filled exactly scores 1.
#guard scoreOf 8 8 0 == 1

/-- Example: a ball of radius 8 at its real size. -/
private def bigBall : Bubble :=
  { label := "big", tags := [], center := ⟨0, 0, 8⟩, semi := ⟨8, 8, 8⟩ }

-- The middle between two filled cubes of one bubble counts as covered.
#guard (coveredOfBubble [(-5, 0, 8), (5, 0, 8)] bigBall).contains (0, 0, 8)
-- A cube past the last filled cube does not.
#guard !(coveredOfBubble [(-5, 0, 8), (5, 0, 8)] bigBall).contains (6, 0, 8)
-- Filled cubes outside the bubble do not help it.
#guard (coveredOfBubble [(100, 0, 8), (-100, 0, 8)] bigBall).isEmpty

/-- Example: two overlapping balls side by side, at their real size. -/
private def leftBall : Bubble :=
  { label := "left", tags := [], center := ⟨-3, 0, 5⟩, semi := ⟨5, 5, 5⟩ }
private def rightBall : Bubble :=
  { label := "right", tags := [], center := ⟨3, 0, 5⟩, semi := ⟨5, 5, 5⟩ }

-- A filled cube in each ball, on one line: the cube in the overlap between them is not covered,
-- because the two filled cubes are not in the same bubble.
#guard !(coveredCells [leftBall, rightBall] [(-6, 0, 5), (5, 0, 5)]).contains (0, 0, 5)

-- A hollow tower scores more than its blocks alone: two blocks with a gap, in the egg at 30.
#guard
  let walls : List Pose := [⟨.flat, .id, ⟨0, -9 / 2, 31 / 2⟩⟩, ⟨.flat, .id, ⟨0, 9 / 2, 31 / 2⟩⟩]
  let placed := BubbleModel.egg.bubbles.map (placeAt 30)
  let built := blockCells walls
  (coveredCells placed built).length > (built.length - (extraCells placed built).length)

end KaplaSemantics
