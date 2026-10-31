import KaplaPlanner.Grid

/-! # Sequencer: from a set of blocks to build steps

The structure must stand after every step, so the order matters. The first order we try
is bottom-up: sort by height, and keep the motif's order within one layer. One block per
step. If the physics check rejects a step, the repair loop changes the plan (see
`Search.lean`).

Proven here:
- the steps contain exactly the input blocks: none lost, none added, none doubled
  (`sequence_perm`);
- every step places exactly one block (`sequence_step_size`), so it never needs more
  hands than the builder has. -/

namespace KaplaPlanner
open KaplaCore

/-- One planned step on the grid. -/
structure GridStep where
  blocks : List GridBlock
  phase  : String
  deriving Repr, BEq, Inhabited

/-- Bottom-up order: sort by the z of the bottom face. The sort is stable, so blocks at the
same height keep their order. -/
def buildOrder (bs : List GridBlock) : List GridBlock :=
  bs.mergeSort fun a b => decide (a.z ≤ b.z)

/-- One step per block, in bottom-up order. -/
def sequence (phase : String) (bs : List GridBlock) : List GridStep :=
  (buildOrder bs).map fun b => { blocks := [b], phase }

/-- All blocks of the steps, in order. -/
def GridStep.allBlocks (steps : List GridStep) : List GridBlock := steps.flatMap (·.blocks)

/-- The steps contain exactly the input blocks, only in a different order. -/
theorem sequence_perm (phase : String) (bs : List GridBlock) :
    (GridStep.allBlocks (sequence phase bs)).Perm bs := by
  simp only [GridStep.allBlocks, sequence, List.flatMap_map, List.flatMap_singleton']
  exact List.mergeSort_perm _ _

/-- Every step places exactly one block. -/
theorem sequence_step_size (phase : String) (bs : List GridBlock) :
    ∀ s ∈ sequence phase bs, s.blocks.length = 1 := by
  intro s hs
  simp only [sequence, List.mem_map] at hs
  obtain ⟨b, _, rfl⟩ := hs
  rfl

/-- Where to hold the block: a standing block at its top end, others at the long sides. -/
def gripFor (b : GridBlock) : Grip :=
  match b.orient with
  | .uprightX | .uprightY => .topEnd
  | _ => .longSides

/-- Turn a grid step into a `KaplaCore.Step`. Every block is lowered from above. -/
def GridStep.toStep (s : GridStep) : Step :=
  { blocks := s.blocks.map GridBlock.toPose
    grip := (s.blocks.head?.map gripFor).getD .longSides
    approach := .fromAbove
    phase := s.phase }

/-- Turn grid steps into a `BuildPlan`. -/
def toBuildPlan (steps : List GridStep) : BuildPlan := ⟨steps.map GridStep.toStep⟩

-- a block listed before the one it rests on is moved after it
#guard (sequence "t" [⟨.flatY, 0, 0, 1⟩, ⟨.flatX, 0, 0, 0⟩]).map (·.blocks) ==
  [[⟨.flatX, 0, 0, 0⟩], [⟨.flatY, 0, 0, 1⟩]]
#guard (toBuildPlan (sequence "t" [⟨.uprightX, 0, 0, 0⟩])).steps.map (·.grip) == [.topEnd]

end KaplaPlanner
