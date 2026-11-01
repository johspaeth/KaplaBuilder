# Draft text for specs/ and comparator/ (for team review)

The proofs of these statements are in `semantics/KaplaSemantics/Proofs/Semantics.lean`.
Copy each block to the file named above it, review it, then run `lake comparator`.
This file is only a draft: delete it when the two files are in place.

To review first: `blockCells_correct` has a condition, ruled on 1 Nov 2026. Every block's turn must
be a real rotation (cos² + sin² = 1). Without it the statement is false.

## `specs/KaplaSpecs/Semantics.lean`

```lean
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

/-- The checker says yes exactly when every block has a cube inside some bubble. -/
theorem checkWithin_correct (m : BubbleModel) (height : Q) (plan : List Pose) :
    checkWithin m height plan = true ↔ WithinTarget m height plan := by
  sorry

/-- The checker says yes exactly when every bubble with cubes at this height has a block cube. -/
theorem checkCovers_correct (m : BubbleModel) (height : Q) (plan : List Pose) :
    checkCovers m height plan = true ↔ CoversTarget m height plan := by
  sorry

/-- The similarity number is from 0 to 1. -/
theorem score_in_unit_interval (m : BubbleModel) (height : Q) (plan : List Pose) :
    0 ≤ score m height plan ∧ score m height plan ≤ 1 := by
  sorry

end KaplaSemantics
```

## `comparator/semantics.json`

```json
{
  "challenge_module": "KaplaSpecs.Semantics",
  "solution_module": "KaplaSemantics.Proofs.Semantics",
  "theorem_names": [
    "KaplaSemantics.targetCells_correct",
    "KaplaSemantics.blockCells_correct",
    "KaplaSemantics.checkWithin_correct",
    "KaplaSemantics.checkCovers_correct",
    "KaplaSemantics.score_in_unit_interval"
  ],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]
}
```
