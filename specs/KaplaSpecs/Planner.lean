import KaplaPlanner.Strategy

/-! # Spec for KaplaPlanner (human-owned)

What "acceptable output" means is `CandidatesOk` in `planner/KaplaPlanner/Strategy.lean`:
the physics engine accepts every plan, and no plan uses more blocks than allowed. Every
`Strategy` carries a proof of it. Proofs live in `planner/KaplaPlanner/Proofs.lean`.
`sorry` is expected in this file only. -/

namespace KaplaPlanner

open KaplaCore

/-- Running several strategies together gives acceptable output, whatever the strategies are. -/
theorem portfolio_ok (ss : List Strategy) (req : PlanRequest) (ph : PhysicsEngine)
    (sem : SemanticEngine) : CandidatesOk req ph ((portfolio ss).run req ph sem) := by
  sorry

-- The hypotheses hold on a concrete input: the portfolio of the basic strategies, the mock
-- engines and the default request.
example : CandidatesOk default physicsMock
    ((portfolio baseStrategies).run default physicsMock semanticMock) :=
  (portfolio baseStrategies).ok _ _ _

-- A bad output is rejected: a one-block plan when no block is allowed.
example : ¬ CandidatesOk { (default : PlanRequest) with blocks := 0 } physicsMock
    [{ (default : Candidate) with plan := BuildPlan.example }] := by
  intro h
  have := (h _ (List.mem_singleton_self _)).2
  simp [BuildPlan.example, BuildPlan.blockCount, BuildPlan.blocks] at this

end KaplaPlanner
