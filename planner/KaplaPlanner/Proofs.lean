import KaplaPlanner.Strategy

/-! Proofs of the statements in `specs/KaplaSpecs/Planner.lean`. -/

namespace KaplaPlanner

open KaplaCore

/-- The portfolio of any strategies is acceptable. -/
theorem portfolio_ok (ss : List Strategy) (req : PlanRequest) (ph : PhysicsEngine)
    (sem : SemanticEngine) : CandidatesOk req ph ((portfolio ss).run req ph sem) :=
  (portfolio ss).ok req ph sem

end KaplaPlanner
