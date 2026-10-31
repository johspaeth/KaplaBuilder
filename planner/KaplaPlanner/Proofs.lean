import KaplaPlanner.Search

/-! Proofs of the statements in `specs/KaplaSpecs/Planner.lean`.
The names and statements must match the spec exactly; `lake comparator` checks this. -/

namespace KaplaPlanner
open KaplaCore

/-- Every candidate the planner returns passed the physics check and uses at most
`req.blocks` blocks. -/
theorem planPure_sound (req : PlanRequest) (phys : PhysicsEngine) (sem : SemanticEngine) :
    ∀ c ∈ planPure req phys sem, c.physics.ok = true ∧ c.plan.blockCount ≤ req.blocks := by
  intro c hc
  simp only [planPure] at hc
  have h := List.mem_of_mem_take hc
  rw [List.mem_mergeSort] at h
  have := (List.mem_filter.mp h).2
  simp only [acceptable, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

/-- The build steps contain exactly the input blocks, only in a different order: no block
is lost, added or doubled. -/
theorem sequence_perm (phase : String) (bs : List GridBlock) :
    (GridStep.allBlocks (sequence phase bs)).Perm bs := by
  simp only [GridStep.allBlocks, sequence, List.flatMap_map, List.flatMap_singleton']
  exact List.mergeSort_perm _ _

end KaplaPlanner
