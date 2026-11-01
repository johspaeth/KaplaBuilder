import KaplaSemantics.Check

/-! # Spec for KaplaSemantics (human-owned)

The statements here are the promise. Proofs live in `semantics/KaplaSemantics/Proofs/Semantics.lean`.
Unfinished proofs are expected in this file only. `lake comparator --config comparator/semantics.json`
checks that the proofs prove exactly these statements, with only standard axioms. -/

namespace KaplaSemantics

open KaplaCore

/-- The target's cubes are exactly the cubes whose middle is inside some bubble at this height. -/
theorem targetCells_correct (m : BubbleModel) (height : Q) (g : GridPt) :
    g ∈ targetCells m height ↔ ∃ b ∈ m.bubbles, (placeAt height b).contains g.centre = true := by
  sorry

/-- When every block has a real turn (cos² + sin² = 1), the plan's cubes are exactly the cubes whose
middle is inside some block. -/
theorem blockCells_correct (plan : List Pose) (hrot : ∀ blk ∈ plan, blk.rot.valid = true)
    (g : GridPt) :
    g ∈ blockCells plan ↔ ∃ blk ∈ plan, blk.contains g.centre = true := by
  sorry

/-- When every block has a real turn, the checker says yes exactly when every block shares a cube
with some bubble. -/
theorem checkWithin_correct (m : BubbleModel) (height : Q) (plan : List Pose)
    (hrot : ∀ blk ∈ plan, blk.rot.valid = true) :
    checkWithin m height plan = true ↔ WithinTarget m height plan := by
  sorry

/-- When every block has a real turn, the checker says yes exactly when every bubble with cubes at
this height shares a cube with some block. -/
theorem checkCovers_correct (m : BubbleModel) (height : Q) (plan : List Pose)
    (hrot : ∀ blk ∈ plan, blk.rot.valid = true) :
    checkCovers m height plan = true ↔ CoversTarget m height plan := by
  sorry

/-- The similarity number is from 0 to 1. -/
theorem score_in_unit_interval (m : BubbleModel) (height : Q) (plan : List Pose) :
    0 ≤ score m height plan ∧ score m height plan ≤ 1 := by
  sorry

/-- The covered share of each bubble, shown by the web badge, is from 0 to 1. -/
theorem perBubble_in_unit_interval (built : List GridPt) (b : Bubble) :
    0 ≤ perBubble built b ∧ perBubble built b ≤ 1 := by
  sorry

end KaplaSemantics
