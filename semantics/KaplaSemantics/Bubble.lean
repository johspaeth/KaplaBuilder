import KaplaCore

/-! # Bubble models: making them stand on the ground

The bubble types and the "inside" test are in `KaplaCore.Bubble`, shared with the planner. See
`semantics/APPROACH.md` §1. -/

namespace KaplaSemantics

open KaplaCore

/-- Make the model exactly 1 tall: its highest point goes to z = 1. The same scale applies to
x, y and z, so the shape does not change. The ground stays at z = 0, so a bubble that goes below
the ground still does. x and y are not moved to the middle. A model with nothing above the ground
comes back unchanged. A model that floats is rejected by `wellFormed`, not moved here. -/
def normalize (m : BubbleModel) : BubbleModel :=
  let highs := m.bubbles.map fun b => b.center.z + b.semi.z
  match highs.max? with
  | some hi =>
    if 0 < hi then
      let k := 1 / hi
      { m with
        bubbles := m.bubbles.map fun b =>
          { b with
            center := ⟨k * b.center.x, k * b.center.y, k * b.center.z⟩
            semi   := ⟨k * b.semi.x, k * b.semi.y, k * b.semi.z⟩ } }
    else m
  | none => m

/-- Example: the egg, 4 times as big. -/
def bigEggExample : BubbleModel :=
  { name := "egg"
    bubbles := [{ label := "egg", tags := ["tower"], center := ⟨0, 0, 2⟩
                  semi := ⟨6 / 5, 6 / 5, 2⟩ }] }

/-- Example: a half sphere of radius 2 with its middle on the ground, such as a foot. -/
def bigFootExample : BubbleModel :=
  { name := "foot"
    bubbles := [{ label := "foot", tags := [], center := ⟨0, 0, 0⟩, semi := ⟨2, 2, 2⟩ }] }

#guard normalize BubbleModel.egg == BubbleModel.egg
#guard normalize bigEggExample == BubbleModel.egg
-- The foot becomes 1 tall and stays cut by the ground: it is not lifted.
#guard normalize bigFootExample == { bigFootExample with
  bubbles := [{ label := "foot", tags := [], center := ⟨0, 0, 0⟩, semi := ⟨1, 1, 1⟩ }] }
-- The model with no bubbles comes back unchanged.
#guard normalize (BubbleModel.mk "none" []) == BubbleModel.mk "none" []

end KaplaSemantics
