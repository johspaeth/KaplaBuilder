import KaplaCore.Basic

/-! # Bubbles: the target as a list of simple shapes

A target can be a list of bubbles. A bubble is an ellipsoid (a stretched ball) with its axes
parallel to x, y and z. A model is scale-free. A `Frame` says how big to build it and where.
The ground is at z = 0. A bubble may go below the ground, as a half sphere makes a foot, but only
the part above the ground counts.
Both the planner and the semantic engine use the definitions here, so they share one meaning
of "inside". -/

namespace KaplaCore

/-- One part of the target. -/
structure Bubble where
  /-- A name for people and reports, such as "head". -/
  label  : String
  /-- Hints for the planner, such as "tower". A tag nobody knows is ignored. -/
  tags   : List String
  /-- The middle of the bubble. -/
  center : Q3
  /-- The half-width of the bubble along x, y and z. Each must be above 0. -/
  semi   : Q3
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A target: a name and its bubbles. -/
structure BubbleModel where
  name    : String
  bubbles : List Bubble
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The most bubbles a model may have. -/
def maxBubbles : Nat := 32

/-- Is point `p` inside the bubble? Points on the surface count as inside. Points below the
ground (z < 0) are never inside. A bubble with a
half-width of 0 or less contains nothing. (Without this rule it would contain every point,
because in Lean dividing by 0 gives 0.) -/
def Bubble.contains (b : Bubble) (p : Q3) : Bool :=
  let dx := (p.x - b.center.x) / b.semi.x
  let dy := (p.y - b.center.y) / b.semi.y
  let dz := (p.z - b.center.z) / b.semi.z
  decide (0 ≤ p.z) && decide (0 < b.semi.x) && decide (0 < b.semi.y) && decide (0 < b.semi.z) &&
    decide (dx * dx + dy * dy + dz * dz ≤ 1)

/-- A bubble is valid when it has a label, all three half-widths are above 0, and some of it is
above the ground. -/
def Bubble.wellFormed (b : Bubble) : Bool :=
  !b.label.isEmpty && decide (0 < b.semi.x) && decide (0 < b.semi.y) && decide (0 < b.semi.z) &&
    decide (0 < b.center.z + b.semi.z)

/-- A model is valid when it has at most `maxBubbles` bubbles, each one is valid, and at least
one bubble reaches the ground. A model that floats could only be built with flying blocks. -/
def BubbleModel.wellFormed (m : BubbleModel) : Bool :=
  decide (m.bubbles.length ≤ maxBubbles) && m.bubbles.all Bubble.wellFormed &&
    m.bubbles.any fun b => decide (b.center.z - b.semi.z ≤ 0)

/-- The smallest box with sides parallel to the axes that contains the part of the bubble above
the ground. -/
def Bubble.box (b : Bubble) : Box :=
  let lo := b.center.sub b.semi
  ⟨{ lo with z := max 0 lo.z }, b.center.add b.semi⟩

/-- How big to build a model and where: multiply every length by `scale` (above 0), then slide
it sideways by `shiftX` and `shiftY`. It cannot move up or down, because the model and the
blocks both stand on the ground. -/
structure Frame where
  scale  : Q
  shiftX : Q
  shiftY : Q
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Build a model of height 1 to height `h`, with no sideways shift. -/
def Frame.ofHeight (h : Q) : Frame := ⟨h, 0, 0⟩

/-- The bubble at its real size and position, in block units. -/
def Bubble.place (f : Frame) (b : Bubble) : Bubble :=
  { b with
    center := ⟨f.scale * b.center.x + f.shiftX, f.scale * b.center.y + f.shiftY,
               f.scale * b.center.z⟩
    semi   := b.semi.scale f.scale }

/-- Example: the egg, one bubble of height 1 standing on the ground. -/
def BubbleModel.egg : BubbleModel :=
  { name := "egg"
    bubbles := [{ label := "egg", tags := ["tower"], center := ⟨0, 0, 1 / 2⟩
                  semi := ⟨3 / 10, 3 / 10, 1 / 2⟩ }] }

private def eggBubble : Bubble := BubbleModel.egg.bubbles.head!

#guard BubbleModel.egg.wellFormed
-- The egg contains its middle and its top, but not a point just above the top.
#guard eggBubble.contains ⟨0, 0, 1 / 2⟩
#guard eggBubble.contains ⟨0, 0, 1⟩
#guard !eggBubble.contains ⟨0, 0, 11 / 10⟩
-- At height 30 the egg is 30 tall and stands on the ground.
#guard eggBubble.place (Frame.ofHeight 30) ==
  { eggBubble with center := ⟨0, 0, 15⟩, semi := ⟨9, 9, 15⟩ }
-- A sideways shift moves it. It does not lift it.
#guard (eggBubble.place ⟨2, 5, 7⟩).center == ⟨5, 7, 1⟩
-- At scale 0 the bubble contains nothing, not even its own middle.
#guard !(eggBubble.place (Frame.ofHeight 0)).contains ⟨0, 0, 0⟩
/-- Example: a half sphere with its middle on the ground, such as a foot. -/
private def foot : Bubble :=
  { label := "foot", tags := [], center := ⟨0, 0, 0⟩, semi := ⟨2, 2, 2⟩ }

-- Only the part of the foot above the ground counts.
#guard foot.contains ⟨0, 0, 1⟩ && foot.contains ⟨0, 0, 0⟩ && !foot.contains ⟨0, 0, -1⟩
#guard foot.box == ⟨⟨-2, -2, 0⟩, ⟨2, 2, 2⟩⟩
#guard (BubbleModel.mk "foot" [foot]).wellFormed
-- Scaling keeps the ground where it is.
#guard (foot.place ⟨3, 1, 1⟩).center.z == 0
-- A bubble entirely underground is rejected, also when it only touches the ground from below.
#guard !(BubbleModel.mk "bad" [{ foot with center := ⟨0, 0, -3⟩ }]).wellFormed
#guard !(BubbleModel.mk "bad" [{ foot with center := ⟨0, 0, -2⟩ }]).wellFormed
-- A model that floats is rejected, and so is a model with no bubbles.
#guard !(BubbleModel.mk "bad" [{ foot with center := ⟨0, 0, 3⟩ }]).wellFormed
#guard !(BubbleModel.mk "none" []).wellFormed
-- One part may float if another reaches the ground. Physics decides if that can stand.
#guard (BubbleModel.mk "two" [foot, { foot with center := ⟨0, 0, 9⟩ }]).wellFormed
-- Bad models are rejected: a half-width of 0, and an empty label.
#guard !(BubbleModel.mk "bad" [{ eggBubble with semi := ⟨0, 1, 1⟩ }]).wellFormed
#guard !(BubbleModel.mk "bad" [{ eggBubble with label := "" }]).wellFormed

end KaplaCore
