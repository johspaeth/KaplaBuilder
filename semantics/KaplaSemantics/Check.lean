import KaplaSemantics.Score

/-! # The two acceptance checks

A plan is accepted when it has at least one block and passes both. The score plays no part. See
`semantics/APPROACH.md` §4. -/

namespace KaplaSemantics

open KaplaCore

/-- Every block has at least one cube inside some bubble. No block is fully outside. -/
def WithinTarget (m : BubbleModel) (height : Q) (plan : List Pose) : Prop :=
  ∀ blk ∈ plan, ∃ g : GridPt, blk.contains g.centre = true ∧
    ∃ b ∈ m.bubbles, (placeAt height b).contains g.centre = true

/-- Every bubble that has at least one cube at this height shares a cube with some block. A bubble
with no cube can never share one, so it is skipped. -/
def CoversTarget (m : BubbleModel) (height : Q) (plan : List Pose) : Prop :=
  ∀ b ∈ m.bubbles, (∃ g : GridPt, (placeAt height b).contains g.centre = true) →
    ∃ blk ∈ plan, ∃ g : GridPt, blk.contains g.centre = true ∧
      (placeAt height b).contains g.centre = true

/-- Is this block fully outside all bubbles at their real size? -/
def blockOutside (placed : List Bubble) (blk : Pose) : Bool :=
  !(poseCells blk).any fun g => placed.any (·.contains g.centre)

/-- Does this bubble at its real size have cubes, but no block cube in it? -/
def bubbleUncovered (built : List GridPt) (b : Bubble) : Bool :=
  !(bubbleCells b).isEmpty && !built.any fun g => b.contains g.centre

/-- The checker for `WithinTarget`. -/
def checkWithin (m : BubbleModel) (height : Q) (plan : List Pose) : Bool :=
  !plan.any (blockOutside (m.bubbles.map (placeAt height)))

/-- The checker for `CoversTarget`. -/
def checkCovers (m : BubbleModel) (height : Q) (plan : List Pose) : Bool :=
  !(m.bubbles.map (placeAt height)).any (bubbleUncovered (blockCells plan))

/-- Positions in the plan of blocks fully outside all bubbles. -/
def outsideBlocks (placed : List Bubble) (plan : List Pose) : List Nat :=
  (plan.zipIdx.filter fun (blk, _) => blockOutside placed blk).map (·.2)

/-- Labels of bubbles with cubes but no block cube. -/
def uncoveredBubbles (placed : List Bubble) (built : List GridPt) : List String :=
  (placed.filter (bubbleUncovered built)).map (·.label)

/-- Labels of bubbles too small to hold a cube at this height. -/
def tooSmallBubbles (placed : List Bubble) : List String :=
  (placed.filter fun b => (bubbleCells b).isEmpty).map (·.label)

-- A block touching the ball passes both checks. A block far away fails both.
#guard checkWithin ballModel 2 [flatBlock] && checkCovers ballModel 2 [flatBlock]
#guard !checkWithin ballModel 2 [farBlock] && !checkCovers ballModel 2 [farBlock]
-- One good and one bad block: the bad one is named, and the ball still counts as covered.
#guard outsideBlocks (ballModel.bubbles.map (placeAt 2)) [flatBlock, farBlock] == [1]
#guard checkCovers ballModel 2 [flatBlock, farBlock]
-- A block whose middle is outside but whose end is inside is not outside.
#guard !blockOutside (ballModel.bubbles.map (placeAt 2)) endBlock
-- A ball too small to hold a cube is listed, and it needs no block.
#guard tooSmallBubbles (ballModel.bubbles.map (placeAt (1 / 2))) == ["ball"]
#guard checkCovers ballModel (1 / 2) []

end KaplaSemantics
