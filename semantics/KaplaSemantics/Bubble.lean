/-! # Bubble models

A target is a list of bubbles. A bubble is an ellipsoid with its axes parallel to x, y and z.
All numbers are exact fractions. See `semantics/APPROACH.md` §1. -/

namespace KaplaSemantics

/-- Three exact numbers: a point, or the three half-widths of a bubble. -/
structure V3 where
  x : Rat
  y : Rat
  z : Rat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- One part of the target. -/
structure Bubble where
  /-- A name for people and reports, such as "head". -/
  label  : String
  /-- Hints for the planner, such as "tower". A tag nobody knows is ignored. -/
  tags   : List String
  /-- The middle of the bubble. -/
  center : V3
  /-- The half-width of the bubble along x, y and z. Each must be above 0. -/
  semi   : V3
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A target: a name and its bubbles. -/
structure BubbleModel where
  name    : String
  bubbles : List Bubble
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The most bubbles a model may have. -/
def maxBubbles : Nat := 32

/-- Is point `p` inside the bubble? Points on the surface count as inside. -/
def Bubble.contains (b : Bubble) (p : V3) : Bool :=
  let dx := (p.x - b.center.x) / b.semi.x
  let dy := (p.y - b.center.y) / b.semi.y
  let dz := (p.z - b.center.z) / b.semi.z
  decide (dx * dx + dy * dy + dz * dz ≤ 1)

/-- A bubble is valid when it has a label and all three half-widths are above 0. -/
def Bubble.wellFormed (b : Bubble) : Bool :=
  !b.label.isEmpty && decide (0 < b.semi.x) && decide (0 < b.semi.y) && decide (0 < b.semi.z)

/-- A model is valid when it has at most `maxBubbles` bubbles and each one is valid. -/
def BubbleModel.wellFormed (m : BubbleModel) : Bool :=
  decide (m.bubbles.length ≤ maxBubbles) && m.bubbles.all Bubble.wellFormed

/-- Make the model stand on the ground (lowest point at z = 0) and be exactly 1 tall (highest
point at z = 1). The same scale applies to x, y and z, so the shape does not change. x and y
are not moved to the middle. A model with no height (no bubbles) comes back unchanged. -/
def BubbleModel.normalize (m : BubbleModel) : BubbleModel :=
  let lows  := m.bubbles.map fun b => b.center.z - b.semi.z
  let highs := m.bubbles.map fun b => b.center.z + b.semi.z
  match lows.min?, highs.max? with
  | some lo, some hi =>
    if 0 < hi - lo then
      let k := 1 / (hi - lo)
      { m with
        bubbles := m.bubbles.map fun b =>
          { b with
            center := ⟨k * b.center.x, k * b.center.y, k * (b.center.z - lo)⟩
            semi   := ⟨k * b.semi.x, k * b.semi.y, k * b.semi.z⟩ } }
    else m
  | _, _ => m

/-- Example: the egg, one bubble of height 1 standing on the ground. -/
def eggExample : BubbleModel :=
  { name := "egg"
    bubbles := [{ label := "egg", tags := ["tower"], center := ⟨0, 0, 1 / 2⟩
                  semi := ⟨3 / 10, 3 / 10, 1 / 2⟩ }] }

/-- Example: the same egg, 4 times as big and floating 3 above the ground. -/
def bigEggExample : BubbleModel :=
  { name := "egg"
    bubbles := [{ label := "egg", tags := ["tower"], center := ⟨0, 0, 5⟩
                  semi := ⟨6 / 5, 6 / 5, 2⟩ }] }

#guard eggExample.wellFormed
#guard eggExample.normalize == eggExample
#guard bigEggExample.normalize == eggExample
-- The model with no bubbles comes back unchanged.
#guard (BubbleModel.mk "none" []).normalize == BubbleModel.mk "none" []
-- The egg contains its middle and its top, but not a point just above the top.
#guard (eggExample.bubbles.head!).contains ⟨0, 0, 1 / 2⟩
#guard (eggExample.bubbles.head!).contains ⟨0, 0, 1⟩
#guard !(eggExample.bubbles.head!).contains ⟨0, 0, 11 / 10⟩
-- Bad models are rejected: a half-width of 0, and an empty label.
#guard !(BubbleModel.mk "bad" [{ label := "a", tags := [], center := ⟨0, 0, 0⟩,
                                 semi := ⟨0, 1, 1⟩ }]).wellFormed
#guard !(BubbleModel.mk "bad" [{ label := "", tags := [], center := ⟨0, 0, 0⟩,
                                 semi := ⟨1, 1, 1⟩ }]).wellFormed

end KaplaSemantics
