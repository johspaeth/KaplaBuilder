import KaplaPlanner.Search
import KaplaPlanner.Inside

/-! # Spec for KaplaPlanner (human-owned)

The statements here are the promise. Proofs live in `planner/KaplaPlanner/Proofs.lean`.
`sorry` is expected in this file only. `lake comparator --config comparator/planner.json`
checks that the proofs prove exactly these statements, with only standard axioms.

The planner is not trusted: the physics engine decides whether a plan is safe. These
theorems say the planner does not undo that decision, does not lose blocks on the way, and
never builds outside the target shape. -/

namespace KaplaPlanner
open KaplaCore

/-! ## 1. The planner returns only checked plans within budget

`planPure req phys sem` is the planner's full output for a request, given a physics engine
and a semantic engine. The promise: every plan in that output was accepted by **that**
physics engine, and uses at most the number of blocks the user allowed. This holds for any
engine, real or mock. -/

/-- Every candidate the planner returns passed the physics check and uses at most
`req.blocks` blocks. -/
theorem planPure_sound (req : PlanRequest) (phys : PhysicsEngine) (sem : SemanticEngine) :
    ∀ c ∈ planPure req phys sem, c.physics.ok = true ∧ c.plan.blockCount ≤ req.blocks := by
  sorry

/-- A concrete request: a tower 15 × 15 × 38, at most 20 blocks. -/
def exampleRequest : PlanRequest :=
  let b : Box := ⟨⟨0, 0, 0⟩, ⟨15, 15, 38⟩⟩
  { target := { shape := .box b, parts := [⟨"tower", .tower, b⟩] }, blocks := 20 }

-- The promise is not empty: on this request the planner does return plans.
#guard !(planPure exampleRequest physicsMock semanticMock).isEmpty

/-- A bad candidate: the physics engine rejected it. -/
def rejectedCandidate : Candidate :=
  { plan := BuildPlan.example
    physics := { ok := false, diagnostics := [.unstable 0 0] }
    score := { score := 0, iou := 0 }
    difficulty := .easy }

/-- The promise rules out returning a plan the physics engine rejected. -/
example : ¬ (∀ c ∈ [rejectedCandidate], c.physics.ok = true ∧ c.plan.blockCount ≤ 20) := by
  intro h
  have := (h rejectedCandidate (List.mem_singleton_self _)).1
  simp [rejectedCandidate] at this

/-- A bad candidate: accepted, but it uses 1 block when 0 are allowed. -/
example : ¬ (∀ c ∈ [{ rejectedCandidate with physics := { ok := true } }],
    c.physics.ok = true ∧ c.plan.blockCount ≤ 0) := by
  intro h
  have := (h _ (List.mem_singleton_self _)).2
  simp [rejectedCandidate, BuildPlan.blockCount, BuildPlan.blocks, BuildPlan.example] at this

/-! ## 2. Sequencing keeps every block

`sequence phase bs` turns a set of grid blocks into build steps (bottom-up order, one block
per step). `GridStep.allBlocks` lists the blocks of all steps, in build order. The promise:
these are exactly the blocks we started with. Only the order may change. No block is lost,
added or doubled. (`List.Perm a b` means: `a` and `b` have the same elements, each the same
number of times.) -/

/-- The build steps contain exactly the input blocks, only in a different order: no block
is lost, added or doubled. -/
theorem sequence_perm (phase : String) (bs : List GridBlock) :
    (GridStep.allBlocks (sequence phase bs)).Perm bs := by
  sorry

/-- Example: a block lying on top of another, listed first. -/
def exampleBlocks : List GridBlock := [⟨.flatY, 0, 0, 4⟩, ⟨.flatX, 0, 0, 0⟩]

-- The order changes (the lower block now comes first) ...
#guard GridStep.allBlocks (sequence "" exampleBlocks) == [⟨.flatX, 0, 0, 0⟩, ⟨.flatY, 0, 0, 4⟩]

/-- ... and the promise rules out dropping a block. -/
example : ¬ ([⟨.flatX, 0, 0, 0⟩] : List GridBlock).Perm exampleBlocks := by
  intro h
  have := h.length_eq
  simp [exampleBlocks] at this

/-- The promise rules out doubling a block. -/
example : ¬ ([⟨.flatX, 0, 0, 0⟩, ⟨.flatX, 0, 0, 0⟩] : List GridBlock).Perm exampleBlocks := by
  intro h
  have := h.count_eq ⟨.flatX, 0, 0, 0⟩
  revert this
  decide

/-! ## 3. The design never sticks out of the target

The target is a union of bubbles (stretched balls; `KaplaCore.Bubble`). A design
is a list of blocks on the grid; `blk.box` is the space block `blk` fills.
`insideBubbles bubbles design` is the planner's check. The promise: if the check accepts,
**every point** of every block is inside some bubble. The check itself only looks at the
corners of grid cells, so this is the part that needs a proof. -/

/-- If `insideBubbles` accepts a design, every point of every block lies inside some
bubble: the design never sticks out of the target. -/
theorem insideBubbles_sound (bs : List Bubble) (design : List GridBlock)
    (h : insideBubbles bs design = true) :
    ∀ blk ∈ design, ∀ p : Q3, blk.box.contains p → ∃ b ∈ bs, b.contains p = true := by
  sorry

/-- A ball of radius 13, 13 above the ground, and a flat block through its middle. -/
def ballTarget : List Bubble := [⟨"ball", [], ⟨0, 0, 13⟩, ⟨13, 13, 13⟩⟩]
def blockInBall : GridBlock := ⟨.flatX, -30, -6, 48⟩

-- The condition can be met: the check accepts this block.
#guard insideBubbles ballTarget [blockInBall]

/-- The promise rules out a block that sticks out: a block from x = 7 to x = 22 has a corner
point outside the ball. (Grid positions are in quarters of a block thickness.) -/
example : ¬ (∀ p : Q3, (GridBlock.mk .flatX 28 (-8) 48).box.contains p →
    ∃ b ∈ ballTarget, b.contains p) := by
  intro h
  -- the point (22, -2, 12) is a corner of the block, 22 from the centre axis
  obtain ⟨b, hb, hp⟩ := h ⟨22, -2, 12⟩ (by
    simp only [Box.contains, GridBlock.box, GridBlock.sx, GridBlock.sy, GridBlock.sz,
      Orient.size, Orient.cubes, cubeSide, unit, blockThickness]
    grind)
  simp only [ballTarget, List.mem_singleton] at hb
  subst hb
  simp only [Bubble.contains, Bool.and_eq_true, decide_eq_true_eq] at hp
  grind

end KaplaPlanner
