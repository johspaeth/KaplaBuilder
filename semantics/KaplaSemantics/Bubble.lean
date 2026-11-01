import KaplaCore

/-! # Bubble models: making them stand on the ground

The bubble types and the "inside" test are in `KaplaCore.Bubble`, shared with the planner. See
`semantics/APPROACH.md` §1. -/

namespace KaplaSemantics

open KaplaCore

/-- Make the model stand on the ground (lowest point at z = 0) and be exactly 1 tall (highest
point at z = 1). The same scale applies to x, y and z, so the shape does not change. x and y
are not moved to the middle. A model with no height (no bubbles) comes back unchanged. -/
def normalize (m : BubbleModel) : BubbleModel :=
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

/-- Example: the egg, 4 times as big and floating 3 above the ground. -/
def bigEggExample : BubbleModel :=
  { name := "egg"
    bubbles := [{ label := "egg", tags := ["tower"], center := ⟨0, 0, 5⟩
                  semi := ⟨6 / 5, 6 / 5, 2⟩ }] }

#guard normalize BubbleModel.egg == BubbleModel.egg
#guard normalize bigEggExample == BubbleModel.egg
-- The model with no bubbles comes back unchanged.
#guard normalize (BubbleModel.mk "none" []) == BubbleModel.mk "none" []

end KaplaSemantics
